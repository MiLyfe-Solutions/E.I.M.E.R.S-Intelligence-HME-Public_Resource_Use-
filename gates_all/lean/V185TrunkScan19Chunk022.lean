import V185TrunkScan19Chunk021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_221174 : List Nat := [5, 1, 1, 1, 4, 2, 5]
def baseStart_221174 : Nat := 118140960795 + 221174 * 2 ^ 59
def prefixEnd_221174 : Nat := 4983230072969 + 3 ^ 40 * 221174 * 2
def baseEnd_221174 : Nat := 22433297832616867043525

theorem tailTrace_221174 : CollatzResearch.WordTrace tailWord_221174 prefixEnd_221174 22433297832616867043525 := by
  unfold tailWord_221174
  simp only [CollatzResearch.WordTrace]
  refine ⟨504179906295740397312911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5377919000487897571337717 504179906295740397312911)
  ·
    refine ⟨756269859443610595969367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 504179906295740397312911 756269859443610595969367)
    ·
      refine ⟨1134404789165415893954051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756269859443610595969367 1134404789165415893954051)
      ·
        refine ⟨1701607183748123840931077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134404789165415893954051 1701607183748123840931077)
        ·
          refine ⟨319051346952773220174577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1701607183748123840931077 319051346952773220174577)
          ·
            refine ⟨239288510214579915130933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319051346952773220174577 239288510214579915130933)
            ·
              refine ⟨22433297832616867043525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239288510214579915130933 22433297832616867043525)
              ·
                rfl

theorem cell19_221174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_221174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221174 prefixEnd_221174 := by exact prefixLift 221174
  have htrace : WordTrace (prefixWord ++ tailWord_221174) baseStart_221174 baseEnd_221174 := by
    simpa [prefixWord, tailWord_221174, baseEnd_221174] using wordTrace_append hprefix tailTrace_221174
  have hstable : (prefixWord ++ tailWord_221174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221174).length < 2 ^ (prefixWord ++ tailWord_221174).sum := by decide
  have hdescent : baseEnd_221174 < baseStart_221174 := by decide
  rcases family_descends (prefixWord ++ tailWord_221174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221290 : List Nat := [3, 1, 3, 2, 3, 1, 6]
def baseStart_221290 : Nat := 118140960795 + 221290 * 2 ^ 59
def prefixEnd_221290 : Nat := 4983230072969 + 3 ^ 40 * 221290 * 2
def baseEnd_221290 : Nat := 22445063512798900850827

theorem tailTrace_221290 : CollatzResearch.WordTrace tailWord_221290 prefixEnd_221290 22445063512798900850827 := by
  unfold tailWord_221290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017777342077899542057331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5380739578874398778819549 2017777342077899542057331)
  ·
    refine ⟨3026666013116849313085997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017777342077899542057331 3026666013116849313085997)
    ·
      refine ⟨1134999754918818492407249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3026666013116849313085997 1134999754918818492407249)
      ·
        refine ⟨851249816189113869305437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134999754918818492407249 851249816189113869305437)
        ·
          refine ⟨319218681070917700989539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851249816189113869305437 319218681070917700989539)
          ·
            refine ⟨478828021606376551484309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319218681070917700989539 478828021606376551484309)
            ·
              refine ⟨22445063512798900850827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 478828021606376551484309 22445063512798900850827)
              ·
                rfl

theorem cell19_221290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_221290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221290 prefixEnd_221290 := by exact prefixLift 221290
  have htrace : WordTrace (prefixWord ++ tailWord_221290) baseStart_221290 baseEnd_221290 := by
    simpa [prefixWord, tailWord_221290, baseEnd_221290] using wordTrace_append hprefix tailTrace_221290
  have hstable : (prefixWord ++ tailWord_221290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221290).length < 2 ^ (prefixWord ++ tailWord_221290).sum := by decide
  have hdescent : baseEnd_221290 < baseStart_221290 := by decide
  rcases family_descends (prefixWord ++ tailWord_221290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221292 : List Nat := [2, 2, 1, 1, 3, 4, 6]
def baseStart_221292 : Nat := 118140960795 + 221292 * 2 ^ 59
def prefixEnd_221292 : Nat := 4983230072969 + 3 ^ 40 * 221292 * 2
def baseEnd_221292 : Nat := 22445266369353763502677

theorem tailTrace_221292 : CollatzResearch.WordTrace tailWord_221292 prefixEnd_221292 22445266369353763502677 := by
  unfold tailWord_221292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035591157152176254901065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5380788209536235006534753 4035591157152176254901065)
  ·
    refine ⟨3026693367864132191175799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4035591157152176254901065 3026693367864132191175799)
    ·
      refine ⟨4540040051796198286763699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3026693367864132191175799 4540040051796198286763699)
      ·
        refine ⟨6810060077694297430145549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540040051796198286763699 6810060077694297430145549)
        ·
          refine ⟨2553772529135361536304581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6810060077694297430145549 2553772529135361536304581)
          ·
            refine ⟨478832349212880288057109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2553772529135361536304581 478832349212880288057109)
            ·
              refine ⟨22445266369353763502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 478832349212880288057109 22445266369353763502677)
              ·
                rfl

theorem cell19_221292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_221292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221292 prefixEnd_221292 := by exact prefixLift 221292
  have htrace : WordTrace (prefixWord ++ tailWord_221292) baseStart_221292 baseEnd_221292 := by
    simpa [prefixWord, tailWord_221292, baseEnd_221292] using wordTrace_append hprefix tailTrace_221292
  have hstable : (prefixWord ++ tailWord_221292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221292).length < 2 ^ (prefixWord ++ tailWord_221292).sum := by decide
  have hdescent : baseEnd_221292 < baseStart_221292 := by decide
  rcases family_descends (prefixWord ++ tailWord_221292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221368 : List Nat := [2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_221368 : Nat := 118140960795 + 221368 * 2 ^ 59
def prefixEnd_221368 : Nat := 4983230072969 + 3 ^ 40 * 221368 * 2
def baseEnd_221368 : Nat := 67358924755315632818935

theorem tailTrace_221368 : CollatzResearch.WordTrace tailWord_221368 prefixEnd_221368 67358924755315632818935 := by
  unfold tailWord_221368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036977131014508744784379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5382636174686011659712505 4036977131014508744784379)
  ·
    refine ⟨6055465696521763117176569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036977131014508744784379 6055465696521763117176569)
    ·
      refine ⟨4541599272391322337882427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055465696521763117176569 4541599272391322337882427)
      ·
        refine ⟨6812398908586983506823641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541599272391322337882427 6812398908586983506823641)
        ·
          refine ⟨5109299181440237630117731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812398908586983506823641 5109299181440237630117731)
          ·
            refine ⟨7663948772160356445176597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109299181440237630117731 7663948772160356445176597)
            ·
              refine ⟨359247598695016708367653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7663948772160356445176597 359247598695016708367653)
              ·
                refine ⟨67358924755315632818935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359247598695016708367653 67358924755315632818935)
                ·
                  rfl

theorem cell19_221368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_221368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221368 prefixEnd_221368 := by exact prefixLift 221368
  have htrace : WordTrace (prefixWord ++ tailWord_221368) baseStart_221368 baseEnd_221368 := by
    simpa [prefixWord, tailWord_221368, baseEnd_221368] using wordTrace_append hprefix tailTrace_221368
  have hstable : (prefixWord ++ tailWord_221368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221368).length < 2 ^ (prefixWord ++ tailWord_221368).sum := by decide
  have hdescent : baseEnd_221368 < baseStart_221368 := by decide
  rcases family_descends (prefixWord ++ tailWord_221368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221404 : List Nat := [2, 2, 5, 2, 8]
def baseStart_221404 : Nat := 118140960795 + 221404 * 2 ^ 59
def prefixEnd_221404 : Nat := 4983230072969 + 3 ^ 40 * 221404 * 2
def baseEnd_221404 : Nat := 2495180704047341334031

theorem tailTrace_221404 : CollatzResearch.WordTrace tailWord_221404 prefixEnd_221404 2495180704047341334031 := by
  unfold tailWord_221404
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037633644949297818939633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5383511526599063758586177 4037633644949297818939633)
  ·
    refine ⟨3028225233711973364204725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4037633644949297818939633 3028225233711973364204725)
    ·
      refine ⟨283896115660497502894193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3028225233711973364204725 283896115660497502894193)
      ·
        refine ⟨212922086745373127170645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283896115660497502894193 212922086745373127170645)
        ·
          refine ⟨2495180704047341334031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 212922086745373127170645 2495180704047341334031)
          ·
            rfl

theorem cell19_221404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_221404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221404 prefixEnd_221404 := by exact prefixLift 221404
  have htrace : WordTrace (prefixWord ++ tailWord_221404) baseStart_221404 baseEnd_221404 := by
    simpa [prefixWord, tailWord_221404, baseEnd_221404] using wordTrace_append hprefix tailTrace_221404
  have hstable : (prefixWord ++ tailWord_221404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221404).length < 2 ^ (prefixWord ++ tailWord_221404).sum := by decide
  have hdescent : baseEnd_221404 < baseStart_221404 := by decide
  rcases family_descends (prefixWord ++ tailWord_221404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221421 : List Nat := [1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_221421 : Nat := 118140960795 + 221421 * 2 ^ 59
def prefixEnd_221421 : Nat := 4983230072969 + 3 ^ 40 * 221421 * 2
def baseEnd_221421 : Nat := 67375051851427213641013

theorem tailTrace_221421 : CollatzResearch.WordTrace tailWord_221421 prefixEnd_221421 67375051851427213641013 := by
  unfold tailWord_221421
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075887330837007541248117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383924887224671694165411 8075887330837007541248117)
  ·
    refine ⟨757114437265969456992011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8075887330837007541248117 757114437265969456992011)
    ·
      refine ⟨1135671655898954185488017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757114437265969456992011 1135671655898954185488017)
      ·
        refine ⟨851753741924215639116013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135671655898954185488017 851753741924215639116013)
        ·
          refine ⟨319407653221580864668505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851753741924215639116013 319407653221580864668505)
          ·
            refine ⟨239555739916185648501379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319407653221580864668505 239555739916185648501379)
            ·
              refine ⟨359333609874278472752069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239555739916185648501379 359333609874278472752069)
              ·
                refine ⟨67375051851427213641013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359333609874278472752069 67375051851427213641013)
                ·
                  rfl

theorem cell19_221421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_221421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221421 prefixEnd_221421 := by exact prefixLift 221421
  have htrace : WordTrace (prefixWord ++ tailWord_221421) baseStart_221421 baseEnd_221421 := by
    simpa [prefixWord, tailWord_221421, baseEnd_221421] using wordTrace_append hprefix tailTrace_221421
  have hstable : (prefixWord ++ tailWord_221421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221421).length < 2 ^ (prefixWord ++ tailWord_221421).sum := by decide
  have hdescent : baseEnd_221421 < baseStart_221421 := by decide
  rcases family_descends (prefixWord ++ tailWord_221421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221423 : List Nat := [1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_221423 : Nat := 118140960795 + 221423 * 2 ^ 59
def prefixEnd_221423 : Nat := 4983230072969 + 3 ^ 40 * 221423 * 2
def baseEnd_221423 : Nat := 67375660421091801596563

theorem tailTrace_221423 : CollatzResearch.WordTrace tailWord_221423 prefixEnd_221423 67375660421091801596563 := by
  unfold tailWord_221423
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075960276829761882820923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383973517886507921880615 8075960276829761882820923)
  ·
    refine ⟨12113940415244642824231385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8075960276829761882820923 12113940415244642824231385)
    ·
      refine ⟨9085455311433482118173539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12113940415244642824231385 9085455311433482118173539)
      ·
        refine ⟨13628182967150223177260309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9085455311433482118173539 13628182967150223177260309)
        ·
          refine ⟨638821076585166711434077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13628182967150223177260309 638821076585166711434077)
          ·
            refine ⟨239557903719437516787779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 638821076585166711434077 239557903719437516787779)
            ·
              refine ⟨359336855579156275181669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239557903719437516787779 359336855579156275181669)
              ·
                refine ⟨67375660421091801596563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359336855579156275181669 67375660421091801596563)
                ·
                  rfl

theorem cell19_221423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_221423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221423 prefixEnd_221423 := by exact prefixLift 221423
  have htrace : WordTrace (prefixWord ++ tailWord_221423) baseStart_221423 baseEnd_221423 := by
    simpa [prefixWord, tailWord_221423, baseEnd_221423] using wordTrace_append hprefix tailTrace_221423
  have hstable : (prefixWord ++ tailWord_221423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221423).length < 2 ^ (prefixWord ++ tailWord_221423).sum := by decide
  have hdescent : baseEnd_221423 < baseStart_221423 := by decide
  rcases family_descends (prefixWord ++ tailWord_221423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221425 : List Nat := [1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_221425 : Nat := 118140960795 + 221425 * 2 ^ 59
def prefixEnd_221425 : Nat := 4983230072969 + 3 ^ 40 * 221425 * 2
def baseEnd_221425 : Nat := 67376268990756389552113

theorem tailTrace_221425 : CollatzResearch.WordTrace tailWord_221425 prefixEnd_221425 67376268990756389552113 := by
  unfold tailWord_221425
  simp only [CollatzResearch.WordTrace]
  refine ⟨8076033222822516224393729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5384022148548344149595819 8076033222822516224393729)
  ·
    refine ⟨6057024917116887168295297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8076033222822516224393729 6057024917116887168295297)
    ·
      refine ⟨4542768687837665376221473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6057024917116887168295297 4542768687837665376221473)
      ·
        refine ⟨3407076515878249032166105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542768687837665376221473 3407076515878249032166105)
        ·
          refine ⟨2555307386908686774124579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3407076515878249032166105 2555307386908686774124579)
          ·
            refine ⟨3832961080363030161186869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2555307386908686774124579 3832961080363030161186869)
            ·
              refine ⟨359340101284034077611269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3832961080363030161186869 359340101284034077611269)
              ·
                refine ⟨67376268990756389552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359340101284034077611269 67376268990756389552113)
                ·
                  rfl

theorem cell19_221425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_221425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221425 prefixEnd_221425 := by exact prefixLift 221425
  have htrace : WordTrace (prefixWord ++ tailWord_221425) baseStart_221425 baseEnd_221425 := by
    simpa [prefixWord, tailWord_221425, baseEnd_221425] using wordTrace_append hprefix tailTrace_221425
  have hstable : (prefixWord ++ tailWord_221425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221425).length < 2 ^ (prefixWord ++ tailWord_221425).sum := by decide
  have hdescent : baseEnd_221425 < baseStart_221425 := by decide
  rcases family_descends (prefixWord ++ tailWord_221425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221463 : List Nat := [1, 1, 3, 4, 1, 3, 6]
def baseStart_221463 : Nat := 118140960795 + 221463 * 2 ^ 59
def prefixEnd_221463 : Nat := 4983230072969 + 3 ^ 40 * 221463 * 2
def baseEnd_221463 : Nat := 22462610604794520235855

theorem tailTrace_221463 : CollatzResearch.WordTrace tailWord_221463 prefixEnd_221463 22462610604794520235855 := by
  unfold tailWord_221463
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077419196684848714277043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5384946131123232476184695 8077419196684848714277043)
  ·
    refine ⟨12116128795027273071415565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077419196684848714277043 12116128795027273071415565)
    ·
      refine ⟨4543548298135227401780837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12116128795027273071415565 4543548298135227401780837)
      ·
        refine ⟨851915305900355137833907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4543548298135227401780837 851915305900355137833907)
        ·
          refine ⟨1277872958850532706750861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851915305900355137833907 1277872958850532706750861)
          ·
            refine ⟨479202359568949765031573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277872958850532706750861 479202359568949765031573)
            ·
              refine ⟨22462610604794520235855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 479202359568949765031573 22462610604794520235855)
              ·
                rfl

theorem cell19_221463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_221463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221463 prefixEnd_221463 := by exact prefixLift 221463
  have htrace : WordTrace (prefixWord ++ tailWord_221463) baseStart_221463 baseEnd_221463 := by
    simpa [prefixWord, tailWord_221463, baseEnd_221463] using wordTrace_append hprefix tailTrace_221463
  have hstable : (prefixWord ++ tailWord_221463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221463).length < 2 ^ (prefixWord ++ tailWord_221463).sum := by decide
  have hdescent : baseEnd_221463 < baseStart_221463 := by decide
  rcases family_descends (prefixWord ++ tailWord_221463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221497 : List Nat := [1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_221497 : Nat := 118140960795 + 221497 * 2 ^ 59
def prefixEnd_221497 : Nat := 4983230072969 + 3 ^ 40 * 221497 * 2
def baseEnd_221497 : Nat := 67398177498681555951917

theorem tailTrace_221497 : CollatzResearch.WordTrace tailWord_221497 prefixEnd_221497 67398177498681555951917 := by
  unfold tailWord_221497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8078659278561672521014745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5385772852374448347343163 8078659278561672521014745)
  ·
    refine ⟨6058994458921254390761059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8078659278561672521014745 6058994458921254390761059)
    ·
      refine ⟨9088491688381881586141589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058994458921254390761059 9088491688381881586141589)
      ·
        refine ⟨426023047892900699350387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9088491688381881586141589 426023047892900699350387)
        ·
          refine ⟨639034571839351049025581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426023047892900699350387 639034571839351049025581)
          ·
            refine ⟨239637964439756643384593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639034571839351049025581 239637964439756643384593)
            ·
              refine ⟨179728473329817482538445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239637964439756643384593 179728473329817482538445)
              ·
                refine ⟨67398177498681555951917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179728473329817482538445 67398177498681555951917)
                ·
                  rfl

theorem cell19_221497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_221497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221497 prefixEnd_221497 := by exact prefixLift 221497
  have htrace : WordTrace (prefixWord ++ tailWord_221497) baseStart_221497 baseEnd_221497 := by
    simpa [prefixWord, tailWord_221497, baseEnd_221497] using wordTrace_append hprefix tailTrace_221497
  have hstable : (prefixWord ++ tailWord_221497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221497).length < 2 ^ (prefixWord ++ tailWord_221497).sum := by decide
  have hdescent : baseEnd_221497 < baseStart_221497 := by decide
  rcases family_descends (prefixWord ++ tailWord_221497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221520 : List Nat := [2, 1, 1, 1, 1, 8, 5]
def baseStart_221520 : Nat := 118140960795 + 221520 * 2 ^ 59
def prefixEnd_221520 : Nat := 4983230072969 + 3 ^ 40 * 221520 * 2
def baseEnd_221520 : Nat := 22468392016608105813581

theorem tailTrace_221520 : CollatzResearch.WordTrace tailWord_221520 prefixEnd_221520 22468392016608105813581 := by
  unfold tailWord_221520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039749078739173724551007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5386332104985564966068009 4039749078739173724551007)
  ·
    refine ⟨6059623618108760586826511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039749078739173724551007 6059623618108760586826511)
    ·
      refine ⟨9089435427163140880239767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6059623618108760586826511 9089435427163140880239767)
      ·
        refine ⟨13634153140744711320359651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9089435427163140880239767 13634153140744711320359651)
        ·
          refine ⟨20451229711117066980539477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13634153140744711320359651 20451229711117066980539477)
          ·
            refine ⟨239662848177153128678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 20451229711117066980539477 239662848177153128678197)
            ·
              refine ⟨22468392016608105813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239662848177153128678197 22468392016608105813581)
              ·
                rfl

theorem cell19_221520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_221520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221520 prefixEnd_221520 := by exact prefixLift 221520
  have htrace : WordTrace (prefixWord ++ tailWord_221520) baseStart_221520 baseEnd_221520 := by
    simpa [prefixWord, tailWord_221520, baseEnd_221520] using wordTrace_append hprefix tailTrace_221520
  have hstable : (prefixWord ++ tailWord_221520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221520).length < 2 ^ (prefixWord ++ tailWord_221520).sum := by decide
  have hdescent : baseEnd_221520 < baseStart_221520 := by decide
  rcases family_descends (prefixWord ++ tailWord_221520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221539 : List Nat := [1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_221539 : Nat := 118140960795 + 221539 * 2 ^ 59
def prefixEnd_221539 : Nat := 4983230072969 + 3 ^ 40 * 221539 * 2
def baseEnd_221539 : Nat := 67410957461637903018469

theorem tailTrace_221539 : CollatzResearch.WordTrace tailWord_221539 prefixEnd_221539 67410957461637903018469 := by
  unfold tailWord_221539
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080191144409513694043671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5386794096273009129362447 8080191144409513694043671)
  ·
    refine ⟨12120286716614270541065507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8080191144409513694043671 12120286716614270541065507)
    ·
      refine ⟨18180430074921405811598261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12120286716614270541065507 18180430074921405811598261)
      ·
        refine ⟨1704415319523881794837337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18180430074921405811598261 1704415319523881794837337)
        ·
          refine ⟨1278311489642911346128003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1704415319523881794837337 1278311489642911346128003)
          ·
            refine ⟨1917467234464367019192005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278311489642911346128003 1917467234464367019192005)
            ·
              refine ⟨359525106462068816098501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1917467234464367019192005 359525106462068816098501)
              ·
                refine ⟨67410957461637903018469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359525106462068816098501 67410957461637903018469)
                ·
                  rfl

theorem cell19_221539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_221539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221539 prefixEnd_221539 := by exact prefixLift 221539
  have htrace : WordTrace (prefixWord ++ tailWord_221539) baseStart_221539 baseEnd_221539 := by
    simpa [prefixWord, tailWord_221539, baseEnd_221539] using wordTrace_append hprefix tailTrace_221539
  have hstable : (prefixWord ++ tailWord_221539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221539).length < 2 ^ (prefixWord ++ tailWord_221539).sum := by decide
  have hdescent : baseEnd_221539 < baseStart_221539 := by decide
  rcases family_descends (prefixWord ++ tailWord_221539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221579 : List Nat := [1, 1, 1, 1, 4, 11]
def baseStart_221579 : Nat := 118140960795 + 221579 * 2 ^ 59
def prefixEnd_221579 : Nat := 4983230072969 + 3 ^ 40 * 221579 * 2
def baseEnd_221579 : Nat := 7491458761658851347719

theorem tailTrace_221579 : CollatzResearch.WordTrace tailWord_221579 prefixEnd_221579 7491458761658851347719 := by
  unfold tailWord_221579
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081650064264600525499791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5387766709509733683666527 8081650064264600525499791)
  ·
    refine ⟨12122475096396900788249687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8081650064264600525499791 12122475096396900788249687)
    ·
      refine ⟨18183712644595351182374531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12122475096396900788249687 18183712644595351182374531)
      ·
        refine ⟨27275568966893026773561797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18183712644595351182374531 27275568966893026773561797)
        ·
          refine ⟨5114169181292442520042837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27275568966893026773561797 5114169181292442520042837)
          ·
            refine ⟨7491458761658851347719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5114169181292442520042837 7491458761658851347719)
            ·
              rfl

theorem cell19_221579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_221579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221579 prefixEnd_221579 := by exact prefixLift 221579
  have htrace : WordTrace (prefixWord ++ tailWord_221579) baseStart_221579 baseEnd_221579 := by
    simpa [prefixWord, tailWord_221579, baseEnd_221579] using wordTrace_append hprefix tailTrace_221579
  have hstable : (prefixWord ++ tailWord_221579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221579).length < 2 ^ (prefixWord ++ tailWord_221579).sum := by decide
  have hdescent : baseEnd_221579 < baseStart_221579 := by decide
  rcases family_descends (prefixWord ++ tailWord_221579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221594 : List Nat := [3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_221594 : Nat := 118140960795 + 221594 * 2 ^ 59
def prefixEnd_221594 : Nat := 4983230072969 + 3 ^ 40 * 221594 * 2
def baseEnd_221594 : Nat := 67427693127414071796097

theorem tailTrace_221594 : CollatzResearch.WordTrace tailWord_221594 prefixEnd_221594 67427693127414071796097 := by
  unfold tailWord_221594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020549289802564521823959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5388131439473505391530557 2020549289802564521823959)
  ·
    refine ⟨3030823934703846782735939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2020549289802564521823959 3030823934703846782735939)
    ·
      refine ⟨4546235902055770174103909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030823934703846782735939 4546235902055770174103909)
      ·
        refine ⟨852419231635456907644483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4546235902055770174103909 852419231635456907644483)
        ·
          refine ⟨1278628847453185361466725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852419231635456907644483 1278628847453185361466725)
          ·
            refine ⟨239742908897472255275011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1278628847453185361466725 239742908897472255275011)
            ·
              refine ⟨359614363346208382912517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239742908897472255275011 359614363346208382912517)
              ·
                refine ⟨67427693127414071796097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359614363346208382912517 67427693127414071796097)
                ·
                  rfl

theorem cell19_221594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_221594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221594 prefixEnd_221594 := by exact prefixLift 221594
  have htrace : WordTrace (prefixWord ++ tailWord_221594) baseStart_221594 baseEnd_221594 := by
    simpa [prefixWord, tailWord_221594, baseEnd_221594] using wordTrace_append hprefix tailTrace_221594
  have hstable : (prefixWord ++ tailWord_221594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221594).length < 2 ^ (prefixWord ++ tailWord_221594).sum := by decide
  have hdescent : baseEnd_221594 < baseStart_221594 := by decide
  rcases family_descends (prefixWord ++ tailWord_221594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221672 : List Nat := [2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_221672 : Nat := 118140960795 + 221672 * 2 ^ 59
def prefixEnd_221672 : Nat := 4983230072969 + 3 ^ 40 * 221672 * 2
def baseEnd_221672 : Nat := 67451427344333002062551

theorem tailTrace_221672 : CollatzResearch.WordTrace tailWord_221672 prefixEnd_221672 67451427344333002062551 := by
  unfold tailWord_221672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042521026463838704317635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5390028035285118272423513 4042521026463838704317635)
  ·
    refine ⟨6063781539695758056476453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042521026463838704317635 6063781539695758056476453)
    ·
      refine ⟨1136959038692954635589335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6063781539695758056476453 1136959038692954635589335)
      ·
        refine ⟨1705438558039431953384003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136959038692954635589335 1705438558039431953384003)
        ·
          refine ⟨2558157837059147930076005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705438558039431953384003 2558157837059147930076005)
          ·
            refine ⟨479654594448590236889251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2558157837059147930076005 479654594448590236889251)
            ·
              refine ⟨719481891672885355333877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479654594448590236889251 719481891672885355333877)
              ·
                refine ⟨67451427344333002062551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 719481891672885355333877 67451427344333002062551)
                ·
                  rfl

theorem cell19_221672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_221672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221672 prefixEnd_221672 := by exact prefixLift 221672
  have htrace : WordTrace (prefixWord ++ tailWord_221672) baseStart_221672 baseEnd_221672 := by
    simpa [prefixWord, tailWord_221672, baseEnd_221672] using wordTrace_append hprefix tailTrace_221672
  have hstable : (prefixWord ++ tailWord_221672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221672).length < 2 ^ (prefixWord ++ tailWord_221672).sum := by decide
  have hdescent : baseEnd_221672 < baseStart_221672 := by decide
  rcases family_descends (prefixWord ++ tailWord_221672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221710 : List Nat := [4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_221710 : Nat := 118140960795 + 221710 * 2 ^ 59
def prefixEnd_221710 : Nat := 4983230072969 + 3 ^ 40 * 221710 * 2
def baseEnd_221710 : Nat := 67462990167960173218003

theorem tailTrace_221710 : CollatzResearch.WordTrace tailWord_221710 prefixEnd_221710 67462990167960173218003 := by
  unfold tailWord_221710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010803503348751237314823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5390952017860006599012389 1010803503348751237314823)
  ·
    refine ⟨1516205255023126855972235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010803503348751237314823 1516205255023126855972235)
    ·
      refine ⟨2274307882534690283958353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516205255023126855972235 2274307882534690283958353)
      ·
        refine ⟨1705730911901017712968765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2274307882534690283958353 1705730911901017712968765)
        ·
          refine ⟨639649091962881642363287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1705730911901017712968765 639649091962881642363287)
          ·
            refine ⟨959473637944322463544931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639649091962881642363287 959473637944322463544931)
            ·
              refine ⟨1439210456916483695317397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959473637944322463544931 1439210456916483695317397)
              ·
                refine ⟨67462990167960173218003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1439210456916483695317397 67462990167960173218003)
                ·
                  rfl

theorem cell19_221710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_221710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221710 prefixEnd_221710 := by exact prefixLift 221710
  have htrace : WordTrace (prefixWord ++ tailWord_221710) baseStart_221710 baseEnd_221710 := by
    simpa [prefixWord, tailWord_221710, baseEnd_221710] using wordTrace_append hprefix tailTrace_221710
  have hstable : (prefixWord ++ tailWord_221710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221710).length < 2 ^ (prefixWord ++ tailWord_221710).sum := by decide
  have hdescent : baseEnd_221710 < baseStart_221710 := by decide
  rcases family_descends (prefixWord ++ tailWord_221710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221767 : List Nat := [1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_221767 : Nat := 118140960795 + 221767 * 2 ^ 59
def prefixEnd_221767 : Nat := 4983230072969 + 3 ^ 40 * 221767 * 2
def baseEnd_221767 : Nat := 67480334403400929951181

theorem tailTrace_221767 : CollatzResearch.WordTrace tailWord_221767 prefixEnd_221767 67480334403400929951181 := by
  unfold tailWord_221767
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088506987583508633343555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5392337991722339088895703 8088506987583508633343555)
  ·
    refine ⟨12132760481375262950015333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088506987583508633343555 12132760481375262950015333)
    ·
      refine ⟨2274892590257861803127875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12132760481375262950015333 2274892590257861803127875)
      ·
        refine ⟨3412338885386792704691813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274892590257861803127875 3412338885386792704691813)
        ·
          refine ⟨639813541010023632129715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3412338885386792704691813 639813541010023632129715)
          ·
            refine ⟨959720311515035448194573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639813541010023632129715 959720311515035448194573)
            ·
              refine ⟨359895116818138293072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 959720311515035448194573 359895116818138293072965)
              ·
                refine ⟨67480334403400929951181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359895116818138293072965 67480334403400929951181)
                ·
                  rfl

theorem cell19_221767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_221767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221767 prefixEnd_221767 := by exact prefixLift 221767
  have htrace : WordTrace (prefixWord ++ tailWord_221767) baseStart_221767 baseEnd_221767 := by
    simpa [prefixWord, tailWord_221767, baseEnd_221767] using wordTrace_append hprefix tailTrace_221767
  have hstable : (prefixWord ++ tailWord_221767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221767).length < 2 ^ (prefixWord ++ tailWord_221767).sum := by decide
  have hdescent : baseEnd_221767 < baseStart_221767 := by decide
  rcases family_descends (prefixWord ++ tailWord_221767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221805 : List Nat := [1, 5, 1, 1, 3, 2, 6]
def baseStart_221805 : Nat := 118140960795 + 221805 * 2 ^ 59
def prefixEnd_221805 : Nat := 4983230072969 + 3 ^ 40 * 221805 * 2
def baseEnd_221805 : Nat := 22497299075676033702211

theorem tailTrace_221805 : CollatzResearch.WordTrace tailWord_221805 prefixEnd_221805 22497299075676033702211 := by
  unfold tailWord_221805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089892961445841123226869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5393261974297227415484579 8089892961445841123226869)
  ·
    refine ⟨758427465135547605302519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8089892961445841123226869 758427465135547605302519)
    ·
      refine ⟨1137641197703321407953779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758427465135547605302519 1137641197703321407953779)
      ·
        refine ⟨1706461796554982111930669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137641197703321407953779 1706461796554982111930669)
        ·
          refine ⟨639923173708118291974001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1706461796554982111930669 639923173708118291974001)
          ·
            refine ⟨479942380281088718980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639923173708118291974001 479942380281088718980501)
            ·
              refine ⟨22497299075676033702211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 479942380281088718980501 22497299075676033702211)
              ·
                rfl

theorem cell19_221805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_221805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221805 prefixEnd_221805 := by exact prefixLift 221805
  have htrace : WordTrace (prefixWord ++ tailWord_221805) baseStart_221805 baseEnd_221805 := by
    simpa [prefixWord, tailWord_221805, baseEnd_221805] using wordTrace_append hprefix tailTrace_221805
  have hstable : (prefixWord ++ tailWord_221805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221805).length < 2 ^ (prefixWord ++ tailWord_221805).sum := by decide
  have hdescent : baseEnd_221805 < baseStart_221805 := by decide
  rcases family_descends (prefixWord ++ tailWord_221805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221900 : List Nat := [2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_221900 : Nat := 118140960795 + 221900 * 2 ^ 59
def prefixEnd_221900 : Nat := 4983230072969 + 3 ^ 40 * 221900 * 2
def baseEnd_221900 : Nat := 67520804286096028995263

theorem tailTrace_221900 : CollatzResearch.WordTrace tailWord_221900 prefixEnd_221900 67520804286096028995263 := by
  unfold tailWord_221900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046678948050836173967577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5395571930734448231956769 4046678948050836173967577)
  ·
    refine ⟨3035009211038127130475683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4046678948050836173967577 3035009211038127130475683)
    ·
      refine ⟨4552513816557190695713525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035009211038127130475683 4552513816557190695713525)
      ·
        refine ⟨426798170302236627723143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4552513816557190695713525 426798170302236627723143)
        ·
          refine ⟨640197255453354941584715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426798170302236627723143 640197255453354941584715)
          ·
            refine ⟨960295883180032412377073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640197255453354941584715 960295883180032412377073)
            ·
              refine ⟨720221912385024309282805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960295883180032412377073 720221912385024309282805)
              ·
                refine ⟨67520804286096028995263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720221912385024309282805 67520804286096028995263)
                ·
                  rfl

theorem cell19_221900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_221900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221900 prefixEnd_221900 := by exact prefixLift 221900
  have htrace : WordTrace (prefixWord ++ tailWord_221900) baseStart_221900 baseEnd_221900 := by
    simpa [prefixWord, tailWord_221900, baseEnd_221900] using wordTrace_append hprefix tailTrace_221900
  have hstable : (prefixWord ++ tailWord_221900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221900).length < 2 ^ (prefixWord ++ tailWord_221900).sum := by decide
  have hdescent : baseEnd_221900 < baseStart_221900 := by decide
  rcases family_descends (prefixWord ++ tailWord_221900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221921 : List Nat := [1, 2, 3, 1, 4, 8]
def baseStart_221921 : Nat := 118140960795 + 221921 * 2 ^ 59
def prefixEnd_221921 : Nat := 4983230072969 + 3 ^ 40 * 221921 * 2
def baseEnd_221921 : Nat := 7503021585286022503171

theorem tailTrace_221921 : CollatzResearch.WordTrace tailWord_221921 prefixEnd_221921 7503021585286022503171 := by
  unfold tailWord_221921
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094123829025592934449617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5396082552683728622966411 8094123829025592934449617)
  ·
    refine ⟨6070592871769194700837213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8094123829025592934449617 6070592871769194700837213)
    ·
      refine ⟨2276472326913448012813955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6070592871769194700837213 2276472326913448012813955)
      ·
        refine ⟨3414708490370172019220933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276472326913448012813955 3414708490370172019220933)
        ·
          refine ⟨640257841944407253603925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3414708490370172019220933 640257841944407253603925)
          ·
            refine ⟨7503021585286022503171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 640257841944407253603925 7503021585286022503171)
            ·
              rfl

theorem cell19_221921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_221921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221921 prefixEnd_221921 := by exact prefixLift 221921
  have htrace : WordTrace (prefixWord ++ tailWord_221921) baseStart_221921 baseEnd_221921 := by
    simpa [prefixWord, tailWord_221921, baseEnd_221921] using wordTrace_append hprefix tailTrace_221921
  have hstable : (prefixWord ++ tailWord_221921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221921).length < 2 ^ (prefixWord ++ tailWord_221921).sum := by decide
  have hdescent : baseEnd_221921 < baseStart_221921 := by decide
  rcases family_descends (prefixWord ++ tailWord_221921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221938 : List Nat := [3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_221938 : Nat := 118140960795 + 221938 * 2 ^ 59
def prefixEnd_221938 : Nat := 4983230072969 + 3 ^ 40 * 221938 * 2
def baseEnd_221938 : Nat := 67532367109723200150715

theorem tailTrace_221938 : CollatzResearch.WordTrace tailWord_221938 prefixEnd_221938 67532367109723200150715 := by
  unfold tailWord_221938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023685967491001209454617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5396495913309336558545645 2023685967491001209454617)
  ·
    refine ⟨1517764475618250907090963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023685967491001209454617 1517764475618250907090963)
    ·
      refine ⟨2276646713427376360636445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517764475618250907090963 2276646713427376360636445)
      ·
        refine ⟨853742517535266135238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2276646713427376360636445 853742517535266135238667)
        ·
          refine ⟨1280613776302899202858001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853742517535266135238667 1280613776302899202858001)
          ·
            refine ⟨960460332227174402143501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280613776302899202858001 960460332227174402143501)
            ·
              refine ⟨360172624585190400803813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960460332227174402143501 360172624585190400803813)
              ·
                refine ⟨67532367109723200150715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360172624585190400803813 67532367109723200150715)
                ·
                  rfl

theorem cell19_221938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_221938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221938 prefixEnd_221938 := by exact prefixLift 221938
  have htrace : WordTrace (prefixWord ++ tailWord_221938) baseStart_221938 baseEnd_221938 := by
    simpa [prefixWord, tailWord_221938, baseEnd_221938] using wordTrace_append hprefix tailTrace_221938
  have hstable : (prefixWord ++ tailWord_221938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221938).length < 2 ^ (prefixWord ++ tailWord_221938).sum := by decide
  have hdescent : baseEnd_221938 < baseStart_221938 := by decide
  rcases family_descends (prefixWord ++ tailWord_221938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221978 : List Nat := [3, 1, 1, 3, 2, 1, 8]
def baseStart_221978 : Nat := 118140960795 + 221978 * 2 ^ 59
def prefixEnd_221978 : Nat := 4983230072969 + 3 ^ 40 * 221978 * 2
def baseEnd_221978 : Nat := 22514846167671653087239

theorem tailTrace_221978 : CollatzResearch.WordTrace tailWord_221978 prefixEnd_221978 22514846167671653087239 := by
  unfold tailWord_221978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024050697454772917318647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5397468526546061112849725 2024050697454772917318647)
  ·
    refine ⟨3036076046182159375977971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024050697454772917318647 3036076046182159375977971)
    ·
      refine ⟨4554114069273239063966957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036076046182159375977971 4554114069273239063966957)
      ·
        refine ⟨1707792775977464648987609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4554114069273239063966957 1707792775977464648987609)
        ·
          refine ⟨1280844581983098486740707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707792775977464648987609 1280844581983098486740707)
          ·
            refine ⟨1921266872974647730111061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280844581983098486740707 1921266872974647730111061)
            ·
              refine ⟨22514846167671653087239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1921266872974647730111061 22514846167671653087239)
              ·
                rfl

theorem cell19_221978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_221978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221978 prefixEnd_221978 := by exact prefixLift 221978
  have htrace : WordTrace (prefixWord ++ tailWord_221978) baseStart_221978 baseEnd_221978 := by
    simpa [prefixWord, tailWord_221978, baseEnd_221978] using wordTrace_append hprefix tailTrace_221978
  have hstable : (prefixWord ++ tailWord_221978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221978).length < 2 ^ (prefixWord ++ tailWord_221978).sum := by decide
  have hdescent : baseEnd_221978 < baseStart_221978 := by decide
  rcases family_descends (prefixWord ++ tailWord_221978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222010 : List Nat := [3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_222010 : Nat := 118140960795 + 222010 * 2 ^ 59
def prefixEnd_222010 : Nat := 4983230072969 + 3 ^ 40 * 222010 * 2
def baseEnd_222010 : Nat := 67554275617648366550519

theorem tailTrace_222010 : CollatzResearch.WordTrace tailWord_222010 prefixEnd_222010 67554275617648366550519 := by
  unfold tailWord_222010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024342481425790283609871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5398246617135440756292989 2024342481425790283609871)
  ·
    refine ⟨3036513722138685425414807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024342481425790283609871 3036513722138685425414807)
    ·
      refine ⟨4554770583208028138122211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036513722138685425414807 4554770583208028138122211)
      ·
        refine ⟨6832155874812042207183317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554770583208028138122211 6832155874812042207183317)
        ·
          refine ⟨160128653315907239230859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6832155874812042207183317 160128653315907239230859)
          ·
            refine ⟨240192979973860858846289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160128653315907239230859 240192979973860858846289)
            ·
              refine ⟨180144734980395644134717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240192979973860858846289 180144734980395644134717)
              ·
                refine ⟨67554275617648366550519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180144734980395644134717 67554275617648366550519)
                ·
                  rfl

theorem cell19_222010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_222010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222010 prefixEnd_222010 := by exact prefixLift 222010
  have htrace : WordTrace (prefixWord ++ tailWord_222010) baseStart_222010 baseEnd_222010 := by
    simpa [prefixWord, tailWord_222010, baseEnd_222010] using wordTrace_append hprefix tailTrace_222010
  have hstable : (prefixWord ++ tailWord_222010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222010).length < 2 ^ (prefixWord ++ tailWord_222010).sum := by decide
  have hdescent : baseEnd_222010 < baseStart_222010 := by decide
  rcases family_descends (prefixWord ++ tailWord_222010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222029 : List Nat := [1, 6, 1, 2, 3, 1, 5]
def baseStart_222029 : Nat := 118140960795 + 222029 * 2 ^ 59
def prefixEnd_222029 : Nat := 4983230072969 + 3 ^ 40 * 222029 * 2
def baseEnd_222029 : Nat := 22520019009820650709415

theorem tailTrace_222029 : CollatzResearch.WordTrace tailWord_222029 prefixEnd_222029 22520019009820650709415 := by
  unfold tailWord_222029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098062912634327379381141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398708608422884919587427 8098062912634327379381141)
  ·
    refine ⟨379596699029734095908491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8098062912634327379381141 379596699029734095908491)
    ·
      refine ⟨569395048544601143862737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379596699029734095908491 569395048544601143862737)
      ·
        refine ⟨427046286408450857897053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569395048544601143862737 427046286408450857897053)
        ·
          refine ⟨160142357403169071711395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427046286408450857897053 160142357403169071711395)
          ·
            refine ⟨240213536104753607567093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160142357403169071711395 240213536104753607567093)
            ·
              refine ⟨22520019009820650709415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240213536104753607567093 22520019009820650709415)
              ·
                rfl

theorem cell19_222029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_222029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222029 prefixEnd_222029 := by exact prefixLift 222029
  have htrace : WordTrace (prefixWord ++ tailWord_222029) baseStart_222029 baseEnd_222029 := by
    simpa [prefixWord, tailWord_222029, baseEnd_222029] using wordTrace_append hprefix tailTrace_222029
  have hstable : (prefixWord ++ tailWord_222029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222029).length < 2 ^ (prefixWord ++ tailWord_222029).sum := by decide
  have hdescent : baseEnd_222029 < baseStart_222029 := by decide
  rcases family_descends (prefixWord ++ tailWord_222029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222033 : List Nat := [1, 2, 2, 1, 6, 2, 5]
def baseStart_222033 : Nat := 118140960795 + 222033 * 2 ^ 59
def prefixEnd_222033 : Nat := 4983230072969 + 3 ^ 40 * 222033 * 2
def baseEnd_222033 : Nat := 22520424722930376013115

theorem tailTrace_222033 : CollatzResearch.WordTrace tailWord_222033 prefixEnd_222033 22520424722930376013115 := by
  unfold tailWord_222033
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098208804619836062526753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398805869746557375017835 8098208804619836062526753)
  ·
    refine ⟨6073656603464877046895065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8098208804619836062526753 6073656603464877046895065)
    ·
      refine ⟨4555242452598657785171299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6073656603464877046895065 4555242452598657785171299)
      ·
        refine ⟨6832863678897986677756949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555242452598657785171299 6832863678897986677756949)
        ·
          refine ⟨320290484948343125519857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6832863678897986677756949 320290484948343125519857)
          ·
            refine ⟨240217863711257344139893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320290484948343125519857 240217863711257344139893)
            ·
              refine ⟨22520424722930376013115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240217863711257344139893 22520424722930376013115)
              ·
                rfl

theorem cell19_222033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_222033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222033 prefixEnd_222033 := by exact prefixLift 222033
  have htrace : WordTrace (prefixWord ++ tailWord_222033) baseStart_222033 baseEnd_222033 := by
    simpa [prefixWord, tailWord_222033, baseEnd_222033] using wordTrace_append hprefix tailTrace_222033
  have hstable : (prefixWord ++ tailWord_222033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222033).length < 2 ^ (prefixWord ++ tailWord_222033).sum := by decide
  have hdescent : baseEnd_222033 < baseStart_222033 := by decide
  rcases family_descends (prefixWord ++ tailWord_222033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222050 : List Nat := [3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_222050 : Nat := 118140960795 + 222050 * 2 ^ 59
def prefixEnd_222050 : Nat := 4983230072969 + 3 ^ 40 * 222050 * 2
def baseEnd_222050 : Nat := 67566447010940125661521

theorem tailTrace_222050 : CollatzResearch.WordTrace tailWord_222050 prefixEnd_222050 67566447010940125661521 := by
  unfold tailWord_222050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024707211389561991473901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5399219230372165310597069 2024707211389561991473901)
  ·
    refine ⟨759265204271085746802713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2024707211389561991473901 759265204271085746802713)
    ·
      refine ⟨569448903203314310102035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759265204271085746802713 569448903203314310102035)
      ·
        refine ⟨854173354804971465153053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569448903203314310102035 854173354804971465153053)
        ·
          refine ⟨320315008051864299432395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854173354804971465153053 320315008051864299432395)
          ·
            refine ⟨480472512077796449148593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320315008051864299432395 480472512077796449148593)
            ·
              refine ⟨360354384058347336861445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480472512077796449148593 360354384058347336861445)
              ·
                refine ⟨67566447010940125661521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360354384058347336861445 67566447010940125661521)
                ·
                  rfl

theorem cell19_222050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_222050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222050 prefixEnd_222050 := by exact prefixLift 222050
  have htrace : WordTrace (prefixWord ++ tailWord_222050) baseStart_222050 baseEnd_222050 := by
    simpa [prefixWord, tailWord_222050, baseEnd_222050] using wordTrace_append hprefix tailTrace_222050
  have hstable : (prefixWord ++ tailWord_222050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222050).length < 2 ^ (prefixWord ++ tailWord_222050).sum := by decide
  have hdescent : baseEnd_222050 < baseStart_222050 := by decide
  rcases family_descends (prefixWord ++ tailWord_222050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222052 : List Nat := [2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_222052 : Nat := 118140960795 + 222052 * 2 ^ 59
def prefixEnd_222052 : Nat := 4983230072969 + 3 ^ 40 * 222052 * 2
def baseEnd_222052 : Nat := 67567055580604713617071

theorem tailTrace_222052 : CollatzResearch.WordTrace tailWord_222052 prefixEnd_222052 67567055580604713617071 := by
  unfold tailWord_222052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049450895775501153734205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5399267861034001538312273 4049450895775501153734205)
  ·
    refine ⟨1518544085915812932650327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4049450895775501153734205 1518544085915812932650327)
    ·
      refine ⟨2277816128873719398975491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518544085915812932650327 2277816128873719398975491)
      ·
        refine ⟨3416724193310579098463237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277816128873719398975491 3416724193310579098463237)
        ·
          refine ⟨640635786245733580961857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3416724193310579098463237 640635786245733580961857)
          ·
            refine ⟨480476839684300185721393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640635786245733580961857 480476839684300185721393)
            ·
              refine ⟨360357629763225139291045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480476839684300185721393 360357629763225139291045)
              ·
                refine ⟨67567055580604713617071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360357629763225139291045 67567055580604713617071)
                ·
                  rfl

theorem cell19_222052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_222052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222052 prefixEnd_222052 := by exact prefixLift 222052
  have htrace : WordTrace (prefixWord ++ tailWord_222052) baseStart_222052 baseEnd_222052 := by
    simpa [prefixWord, tailWord_222052, baseEnd_222052] using wordTrace_append hprefix tailTrace_222052
  have hstable : (prefixWord ++ tailWord_222052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222052).length < 2 ^ (prefixWord ++ tailWord_222052).sum := by decide
  have hdescent : baseEnd_222052 < baseStart_222052 := by decide
  rcases family_descends (prefixWord ++ tailWord_222052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222073 : List Nat := [1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_222073 : Nat := 118140960795 + 222073 * 2 ^ 59
def prefixEnd_222073 : Nat := 4983230072969 + 3 ^ 40 * 222073 * 2
def baseEnd_222073 : Nat := 67573445562082887150347

theorem tailTrace_222073 : CollatzResearch.WordTrace tailWord_222073 prefixEnd_222073 67573445562082887150347 := by
  unfold tailWord_222073
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099667724474922893982873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5399778482983281929321915 8099667724474922893982873)
  ·
    refine ⟨6074750793356192170487155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8099667724474922893982873 6074750793356192170487155)
    ·
      refine ⟨9112126190034288255730733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6074750793356192170487155 9112126190034288255730733)
      ·
        refine ⟨3417047321262858095899025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9112126190034288255730733 3417047321262858095899025)
        ·
          refine ⟨2562785490947143571924269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417047321262858095899025 2562785490947143571924269)
          ·
            refine ⟨961044559105178839471601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2562785490947143571924269 961044559105178839471601)
            ·
              refine ⟨720783419328884129603701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961044559105178839471601 720783419328884129603701)
              ·
                refine ⟨67573445562082887150347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720783419328884129603701 67573445562082887150347)
                ·
                  rfl

theorem cell19_222073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_222073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222073 prefixEnd_222073 := by exact prefixLift 222073
  have htrace : WordTrace (prefixWord ++ tailWord_222073) baseStart_222073 baseEnd_222073 := by
    simpa [prefixWord, tailWord_222073, baseEnd_222073] using wordTrace_append hprefix tailTrace_222073
  have hstable : (prefixWord ++ tailWord_222073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222073).length < 2 ^ (prefixWord ++ tailWord_222073).sum := by decide
  have hdescent : baseEnd_222073 < baseStart_222073 := by decide
  rcases family_descends (prefixWord ++ tailWord_222073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222181 : List Nat := [1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_222181 : Nat := 118140960795 + 222181 * 2 ^ 59
def prefixEnd_222181 : Nat := 4983230072969 + 3 ^ 40 * 222181 * 2
def baseEnd_222181 : Nat := 67606308323970636750053

theorem tailTrace_222181 : CollatzResearch.WordTrace tailWord_222181 prefixEnd_222181 67606308323970636750053 := by
  unfold tailWord_222181
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103606808083657338914397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5402404538722438225942931 8103606808083657338914397)
  ·
    refine ⟨3038852553031371502092899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8103606808083657338914397 3038852553031371502092899)
    ·
      refine ⟨4558278829547057253139349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038852553031371502092899 4558278829547057253139349)
      ·
        refine ⟨213669320135018308740907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4558278829547057253139349 213669320135018308740907)
        ·
          refine ⟨320503980202527463111361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213669320135018308740907 320503980202527463111361)
          ·
            refine ⟨240377985151895597333521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320503980202527463111361 240377985151895597333521)
            ·
              refine ⟨180283488863921698000141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240377985151895597333521 180283488863921698000141)
              ·
                refine ⟨67606308323970636750053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180283488863921698000141 67606308323970636750053)
                ·
                  rfl

theorem cell19_222181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_222181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222181 prefixEnd_222181 := by exact prefixLift 222181
  have htrace : WordTrace (prefixWord ++ tailWord_222181) baseStart_222181 baseEnd_222181 := by
    simpa [prefixWord, tailWord_222181, baseEnd_222181] using wordTrace_append hprefix tailTrace_222181
  have hstable : (prefixWord ++ tailWord_222181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222181).length < 2 ^ (prefixWord ++ tailWord_222181).sum := by decide
  have hdescent : baseEnd_222181 < baseStart_222181 := by decide
  rcases family_descends (prefixWord ++ tailWord_222181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222183 : List Nat := [1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_222183 : Nat := 118140960795 + 222183 * 2 ^ 59
def prefixEnd_222183 : Nat := 4983230072969 + 3 ^ 40 * 222183 * 2
def baseEnd_222183 : Nat := 67606916893635224705603

theorem tailTrace_222183 : CollatzResearch.WordTrace tailWord_222183 prefixEnd_222183 67606916893635224705603 := by
  unfold tailWord_222183
  simp only [CollatzResearch.WordTrace]
  refine ⟨8103679754076411680487203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5402453169384274453658135 8103679754076411680487203)
  ·
    refine ⟨12155519631114617520730805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8103679754076411680487203 12155519631114617520730805)
    ·
      refine ⟨1139579965416995392568513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12155519631114617520730805 1139579965416995392568513)
      ·
        refine ⟨854684974062746544426385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139579965416995392568513 854684974062746544426385)
        ·
          refine ⟨641013730547059908319789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854684974062746544426385 641013730547059908319789)
          ·
            refine ⟨240380148955147465619921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641013730547059908319789 240380148955147465619921)
            ·
              refine ⟨180285111716360599214941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240380148955147465619921 180285111716360599214941)
              ·
                refine ⟨67606916893635224705603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180285111716360599214941 67606916893635224705603)
                ·
                  rfl

theorem cell19_222183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_222183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222183 prefixEnd_222183 := by exact prefixLift 222183
  have htrace : WordTrace (prefixWord ++ tailWord_222183) baseStart_222183 baseEnd_222183 := by
    simpa [prefixWord, tailWord_222183, baseEnd_222183] using wordTrace_append hprefix tailTrace_222183
  have hstable : (prefixWord ++ tailWord_222183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222183).length < 2 ^ (prefixWord ++ tailWord_222183).sum := by decide
  have hdescent : baseEnd_222183 < baseStart_222183 := by decide
  rcases family_descends (prefixWord ++ tailWord_222183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222196 : List Nat := [2, 6, 2, 1, 2, 1, 5]
def baseStart_222196 : Nat := 118140960795 + 222196 * 2 ^ 59
def prefixEnd_222196 : Nat := 4983230072969 + 3 ^ 40 * 222196 * 2
def baseEnd_222196 : Nat := 22536957532151682138893

theorem tailTrace_222196 : CollatzResearch.WordTrace tailWord_222196 prefixEnd_222196 22536957532151682138893 := by
  unfold tailWord_222196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052076951514657450355221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5402769268686209933806961 4052076951514657450355221)
  ·
    refine ⟨189941107102249567985401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4052076951514657450355221 189941107102249567985401)
    ·
      refine ⟨142455830326687175989051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189941107102249567985401 142455830326687175989051)
      ·
        refine ⟨213683745490030763983577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142455830326687175989051 213683745490030763983577)
        ·
          refine ⟨160262809117523072987683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213683745490030763983577 160262809117523072987683)
          ·
            refine ⟨240394213676284609481525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160262809117523072987683 240394213676284609481525)
            ·
              refine ⟨22536957532151682138893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240394213676284609481525 22536957532151682138893)
              ·
                rfl

theorem cell19_222196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_222196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222196 prefixEnd_222196 := by exact prefixLift 222196
  have htrace : WordTrace (prefixWord ++ tailWord_222196) baseStart_222196 baseEnd_222196 := by
    simpa [prefixWord, tailWord_222196, baseEnd_222196] using wordTrace_append hprefix tailTrace_222196
  have hstable : (prefixWord ++ tailWord_222196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222196).length < 2 ^ (prefixWord ++ tailWord_222196).sum := by decide
  have hdescent : baseEnd_222196 < baseStart_222196 := by decide
  rcases family_descends (prefixWord ++ tailWord_222196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222278 : List Nat := [6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_222278 : Nat := 118140960795 + 222278 * 2 ^ 59
def prefixEnd_222278 : Nat := 4983230072969 + 3 ^ 40 * 222278 * 2
def baseEnd_222278 : Nat := 67635823952703152594233

theorem tailTrace_222278 : CollatzResearch.WordTrace tailWord_222278 prefixEnd_222278 67635823952703152594233 := by
  unfold tailWord_222278
  simp only [CollatzResearch.WordTrace]
  refine ⟨253348271522882590787359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5404763125821495270130325 253348271522882590787359)
  ·
    refine ⟨380022407284323886181039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253348271522882590787359 380022407284323886181039)
    ·
      refine ⟨570033610926485829271559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380022407284323886181039 570033610926485829271559)
      ·
        refine ⟨855050416389728743907339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570033610926485829271559 855050416389728743907339)
        ·
          refine ⟨1282575624584593115861009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855050416389728743907339 1282575624584593115861009)
          ·
            refine ⟨961931718438444836895757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282575624584593115861009 961931718438444836895757)
            ·
              refine ⟨360724394414416813835909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961931718438444836895757 360724394414416813835909)
              ·
                refine ⟨67635823952703152594233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360724394414416813835909 67635823952703152594233)
                ·
                  rfl

theorem cell19_222278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_222278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222278 prefixEnd_222278 := by exact prefixLift 222278
  have htrace : WordTrace (prefixWord ++ tailWord_222278) baseStart_222278 baseEnd_222278 := by
    simpa [prefixWord, tailWord_222278, baseEnd_222278] using wordTrace_append hprefix tailTrace_222278
  have hstable : (prefixWord ++ tailWord_222278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222278).length < 2 ^ (prefixWord ++ tailWord_222278).sum := by decide
  have hdescent : baseEnd_222278 < baseStart_222278 := by decide
  rcases family_descends (prefixWord ++ tailWord_222278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222282 : List Nat := [3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_222282 : Nat := 118140960795 + 222282 * 2 ^ 59
def prefixEnd_222282 : Nat := 4983230072969 + 3 ^ 40 * 222282 * 2
def baseEnd_222282 : Nat := 67637041092032328505333

theorem tailTrace_222282 : CollatzResearch.WordTrace tailWord_222282 prefixEnd_222282 67637041092032328505333 := by
  unfold tailWord_222282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026822645179437897085275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5404860387145167725560733 2026822645179437897085275)
  ·
    refine ⟨3040233967769156845627913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2026822645179437897085275 3040233967769156845627913)
    ·
      refine ⟨2280175475826867634220935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040233967769156845627913 2280175475826867634220935)
      ·
        refine ⟨3420263213740301451331403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280175475826867634220935 3420263213740301451331403)
        ·
          refine ⟨5130394820610452176997105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420263213740301451331403 5130394820610452176997105)
          ·
            refine ⟨3847796115457839132747829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5130394820610452176997105 3847796115457839132747829)
            ·
              refine ⟨360730885824172418695109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3847796115457839132747829 360730885824172418695109)
              ·
                refine ⟨67637041092032328505333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360730885824172418695109 67637041092032328505333)
                ·
                  rfl

theorem cell19_222282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_222282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222282 prefixEnd_222282 := by exact prefixLift 222282
  have htrace : WordTrace (prefixWord ++ tailWord_222282) baseStart_222282 baseEnd_222282 := by
    simpa [prefixWord, tailWord_222282, baseEnd_222282] using wordTrace_append hprefix tailTrace_222282
  have hstable : (prefixWord ++ tailWord_222282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222282).length < 2 ^ (prefixWord ++ tailWord_222282).sum := by decide
  have hdescent : baseEnd_222282 < baseStart_222282 := by decide
  rcases family_descends (prefixWord ++ tailWord_222282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222354 : List Nat := [3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_222354 : Nat := 118140960795 + 222354 * 2 ^ 59
def prefixEnd_222354 : Nat := 4983230072969 + 3 ^ 40 * 222354 * 2
def baseEnd_222354 : Nat := 67658949599957494905137

theorem tailTrace_222354 : CollatzResearch.WordTrace tailWord_222354 prefixEnd_222354 67658949599957494905137 := by
  unfold tailWord_222354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027479159114226971240529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5406611090971271923308077 2027479159114226971240529)
  ·
    refine ⟨1520609369335670228430397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2027479159114226971240529 1520609369335670228430397)
    ·
      refine ⟨570228513500876335661399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1520609369335670228430397 570228513500876335661399)
      ·
        refine ⟨855342770251314503492099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570228513500876335661399 855342770251314503492099)
        ·
          refine ⟨1283014155376971755238149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855342770251314503492099 1283014155376971755238149)
          ·
            refine ⟨240565154133182204107153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1283014155376971755238149 240565154133182204107153)
            ·
              refine ⟨180423865599886653080365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240565154133182204107153 180423865599886653080365)
              ·
                refine ⟨67658949599957494905137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180423865599886653080365 67658949599957494905137)
                ·
                  rfl

theorem cell19_222354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_222354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222354 prefixEnd_222354 := by exact prefixLift 222354
  have htrace : WordTrace (prefixWord ++ tailWord_222354) baseStart_222354 baseEnd_222354 := by
    simpa [prefixWord, tailWord_222354, baseEnd_222354] using wordTrace_append hprefix tailTrace_222354
  have hstable : (prefixWord ++ tailWord_222354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222354).length < 2 ^ (prefixWord ++ tailWord_222354).sum := by decide
  have hdescent : baseEnd_222354 < baseStart_222354 := by decide
  rcases family_descends (prefixWord ++ tailWord_222354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222375 : List Nat := [1, 1, 6, 2, 1, 3, 5]
def baseStart_222375 : Nat := 118140960795 + 222375 * 2 ^ 59
def prefixEnd_222375 : Nat := 4983230072969 + 3 ^ 40 * 222375 * 2
def baseEnd_222375 : Nat := 22555113193811889479471

theorem tailTrace_222375 : CollatzResearch.WordTrace tailWord_222375 prefixEnd_222375 22555113193811889479471 := by
  unfold tailWord_222375
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110682569380828471476579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5407121712920552314317719 8110682569380828471476579)
  ·
    refine ⟨12166023854071242707214869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8110682569380828471476579 12166023854071242707214869)
    ·
      refine ⟨570282368159589501900697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12166023854071242707214869 570282368159589501900697)
      ·
        refine ⟨427711776119692126425523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570282368159589501900697 427711776119692126425523)
        ·
          refine ⟨641567664179538189638285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427711776119692126425523 641567664179538189638285)
          ·
            refine ⟨240587874067326821114357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641567664179538189638285 240587874067326821114357)
            ·
              refine ⟨22555113193811889479471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240587874067326821114357 22555113193811889479471)
              ·
                rfl

theorem cell19_222375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_222375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222375 prefixEnd_222375 := by exact prefixLift 222375
  have htrace : WordTrace (prefixWord ++ tailWord_222375) baseStart_222375 baseEnd_222375 := by
    simpa [prefixWord, tailWord_222375, baseEnd_222375] using wordTrace_append hprefix tailTrace_222375
  have hstable : (prefixWord ++ tailWord_222375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222375).length < 2 ^ (prefixWord ++ tailWord_222375).sum := by decide
  have hdescent : baseEnd_222375 < baseStart_222375 := by decide
  rcases family_descends (prefixWord ++ tailWord_222375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222390 : List Nat := [5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_222390 : Nat := 118140960795 + 222390 * 2 ^ 59
def prefixEnd_222390 : Nat := 4983230072969 + 3 ^ 40 * 222390 * 2
def baseEnd_222390 : Nat := 67669903853920078105039

theorem tailTrace_222390 : CollatzResearch.WordTrace tailWord_222390 prefixEnd_222390 67669903853920078105039 := by
  unfold tailWord_222390
  simp only [CollatzResearch.WordTrace]
  refine ⟨506951854020405377079539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5407486442884324022181749 506951854020405377079539)
  ·
    refine ⟨760427781030608065619309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506951854020405377079539 760427781030608065619309)
    ·
      refine ⟨285160417886478024607241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 760427781030608065619309 285160417886478024607241)
      ·
        refine ⟨213870313414858518455431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285160417886478024607241 213870313414858518455431)
        ·
          refine ⟨320805470122287777683147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213870313414858518455431 320805470122287777683147)
          ·
            refine ⟨481208205183431666524721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320805470122287777683147 481208205183431666524721)
            ·
              refine ⟨360906153887573749893541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481208205183431666524721 360906153887573749893541)
              ·
                refine ⟨67669903853920078105039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360906153887573749893541 67669903853920078105039)
                ·
                  rfl

theorem cell19_222390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_222390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222390 prefixEnd_222390 := by exact prefixLift 222390
  have htrace : WordTrace (prefixWord ++ tailWord_222390) baseStart_222390 baseEnd_222390 := by
    simpa [prefixWord, tailWord_222390, baseEnd_222390] using wordTrace_append hprefix tailTrace_222390
  have hstable : (prefixWord ++ tailWord_222390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222390).length < 2 ^ (prefixWord ++ tailWord_222390).sum := by decide
  have hdescent : baseEnd_222390 < baseStart_222390 := by decide
  rcases family_descends (prefixWord ++ tailWord_222390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222396 : List Nat := [2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_222396 : Nat := 118140960795 + 222396 * 2 ^ 59
def prefixEnd_222396 : Nat := 4983230072969 + 3 ^ 40 * 222396 * 2
def baseEnd_222396 : Nat := 67671729562913841971689

theorem tailTrace_222396 : CollatzResearch.WordTrace tailWord_222396 prefixEnd_222396 67671729562913841971689 := by
  unfold tailWord_222396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055724251152374528995521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5407632334869832705327361 4055724251152374528995521)
  ·
    refine ⟨3041793188364280896746641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4055724251152374528995521 3041793188364280896746641)
    ·
      refine ⟨2281344891273210672559981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3041793188364280896746641 2281344891273210672559981)
      ·
        refine ⟨855504334227454002209993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2281344891273210672559981 855504334227454002209993)
        ·
          refine ⟨641628250670590501657495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855504334227454002209993 641628250670590501657495)
          ·
            refine ⟨962442376005885752486243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641628250670590501657495 962442376005885752486243)
            ·
              refine ⟨1443663564008828628729365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962442376005885752486243 1443663564008828628729365)
              ·
                refine ⟨67671729562913841971689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1443663564008828628729365 67671729562913841971689)
                ·
                  rfl

theorem cell19_222396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_222396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222396 prefixEnd_222396 := by exact prefixLift 222396
  have htrace : WordTrace (prefixWord ++ tailWord_222396) baseStart_222396 baseEnd_222396 := by
    simpa [prefixWord, tailWord_222396, baseEnd_222396] using wordTrace_append hprefix tailTrace_222396
  have hstable : (prefixWord ++ tailWord_222396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222396).length < 2 ^ (prefixWord ++ tailWord_222396).sum := by decide
  have hdescent : baseEnd_222396 < baseStart_222396 := by decide
  rcases family_descends (prefixWord ++ tailWord_222396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222512 : List Nat := [2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_222512 : Nat := 118140960795 + 222512 * 2 ^ 59
def prefixEnd_222512 : Nat := 4983230072969 + 3 ^ 40 * 222512 * 2
def baseEnd_222512 : Nat := 67707026603459943393595

theorem tailTrace_222512 : CollatzResearch.WordTrace tailWord_222512 prefixEnd_222512 67707026603459943393595 := by
  unfold tailWord_222512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057839684942250434606895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5410452913256333912809193 4057839684942250434606895)
  ·
    refine ⟨6086759527413375651910343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4057839684942250434606895 6086759527413375651910343)
    ·
      refine ⟨9130139291120063477865515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086759527413375651910343 9130139291120063477865515)
      ·
        refine ⟨13695208936680095216798273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130139291120063477865515 13695208936680095216798273)
        ·
          refine ⟨10271406702510071412598705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13695208936680095216798273 10271406702510071412598705)
          ·
            refine ⟨7703555026882553559449029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10271406702510071412598705 7703555026882553559449029)
            ·
              refine ⟨1444416567540478792396693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7703555026882553559449029 1444416567540478792396693)
              ·
                refine ⟨67707026603459943393595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1444416567540478792396693 67707026603459943393595)
                ·
                  rfl

theorem cell19_222512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_222512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222512 prefixEnd_222512 := by exact prefixLift 222512
  have htrace : WordTrace (prefixWord ++ tailWord_222512) baseStart_222512 baseEnd_222512 := by
    simpa [prefixWord, tailWord_222512, baseEnd_222512] using wordTrace_append hprefix tailTrace_222512
  have hstable : (prefixWord ++ tailWord_222512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222512).length < 2 ^ (prefixWord ++ tailWord_222512).sum := by decide
  have hdescent : baseEnd_222512 < baseStart_222512 := by decide
  rcases family_descends (prefixWord ++ tailWord_222512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222527 : List Nat := [1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_222527 : Nat := 118140960795 + 222527 * 2 ^ 59
def prefixEnd_222527 : Nat := 4983230072969 + 3 ^ 40 * 222527 * 2
def baseEnd_222527 : Nat := 67711590875944353060221

theorem tailTrace_222527 : CollatzResearch.WordTrace tailWord_222527 prefixEnd_222527 67711590875944353060221 := by
  unfold tailWord_222527
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116226464830158431009835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5410817643220105620673223 8116226464830158431009835)
  ·
    refine ⟨12174339697245237646514753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8116226464830158431009835 12174339697245237646514753)
    ·
      refine ⟨9130754772933928234886065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12174339697245237646514753 9130754772933928234886065)
      ·
        refine ⟨6848066079700446176164549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9130754772933928234886065 6848066079700446176164549)
        ·
          refine ⟨1284012389943833658030853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6848066079700446176164549 1284012389943833658030853)
          ·
            refine ⟨240752323114468810880785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1284012389943833658030853 240752323114468810880785)
            ·
              refine ⟨180564242335851608160589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240752323114468810880785 180564242335851608160589)
              ·
                refine ⟨67711590875944353060221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180564242335851608160589 67711590875944353060221)
                ·
                  rfl

theorem cell19_222527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_222527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222527 prefixEnd_222527 := by exact prefixLift 222527
  have htrace : WordTrace (prefixWord ++ tailWord_222527) baseStart_222527 baseEnd_222527 := by
    simpa [prefixWord, tailWord_222527, baseEnd_222527] using wordTrace_append hprefix tailTrace_222527
  have hstable : (prefixWord ++ tailWord_222527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222527).length < 2 ^ (prefixWord ++ tailWord_222527).sum := by decide
  have hdescent : baseEnd_222527 < baseStart_222527 := by decide
  rcases family_descends (prefixWord ++ tailWord_222527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222588 : List Nat := [2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_222588 : Nat := 118140960795 + 222588 * 2 ^ 59
def prefixEnd_222588 : Nat := 4983230072969 + 3 ^ 40 * 222588 * 2
def baseEnd_222588 : Nat := 67730152250714285704499

theorem tailTrace_222588 : CollatzResearch.WordTrace tailWord_222588 prefixEnd_222588 67730152250714285704499 := by
  unfold tailWord_222588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059225658804582924490209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5412300878406110565986945 4059225658804582924490209)
  ·
    refine ⟨3044419244103437193367657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4059225658804582924490209 3044419244103437193367657)
    ·
      refine ⟨2283314433077577895025743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3044419244103437193367657 2283314433077577895025743)
      ·
        refine ⟨3424971649616366842538615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283314433077577895025743 3424971649616366842538615)
        ·
          refine ⟨5137457474424550263807923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424971649616366842538615 5137457474424550263807923)
          ·
            refine ⟨7706186211636825395711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137457474424550263807923 7706186211636825395711885)
            ·
              refine ⟨2889819829363809523391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7706186211636825395711885 2889819829363809523391957)
              ·
                refine ⟨67730152250714285704499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2889819829363809523391957 67730152250714285704499)
                ·
                  rfl

theorem cell19_222588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_222588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222588 prefixEnd_222588 := by exact prefixLift 222588
  have htrace : WordTrace (prefixWord ++ tailWord_222588) baseStart_222588 baseEnd_222588 := by
    simpa [prefixWord, tailWord_222588, baseEnd_222588] using wordTrace_append hprefix tailTrace_222588
  have hstable : (prefixWord ++ tailWord_222588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222588).length < 2 ^ (prefixWord ++ tailWord_222588).sum := by decide
  have hdescent : baseEnd_222588 < baseStart_222588 := by decide
  rcases family_descends (prefixWord ++ tailWord_222588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222620 : List Nat := [2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_222620 : Nat := 118140960795 + 222620 * 2 ^ 59
def prefixEnd_222620 : Nat := 4983230072969 + 3 ^ 40 * 222620 * 2
def baseEnd_222620 : Nat := 67739889365347692993301

theorem tailTrace_222620 : CollatzResearch.WordTrace tailWord_222620 prefixEnd_222620 67739889365347692993301 := by
  unfold tailWord_222620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059809226746617657072657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5413078968995490209430209 4059809226746617657072657)
  ·
    refine ⟨3044856920059963242804493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4059809226746617657072657 3044856920059963242804493)
    ·
      refine ⟨1141821345022486216051685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3044856920059963242804493 1141821345022486216051685)
      ·
        refine ⟨214091502191716165509691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1141821345022486216051685 214091502191716165509691)
        ·
          refine ⟨321137253287574248264537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214091502191716165509691 321137253287574248264537)
          ·
            refine ⟨240852939965680686198403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321137253287574248264537 240852939965680686198403)
            ·
              refine ⟨361279409948521029297605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240852939965680686198403 361279409948521029297605)
              ·
                refine ⟨67739889365347692993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361279409948521029297605 67739889365347692993301)
                ·
                  rfl

theorem cell19_222620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_222620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222620 prefixEnd_222620 := by exact prefixLift 222620
  have htrace : WordTrace (prefixWord ++ tailWord_222620) baseStart_222620 baseEnd_222620 := by
    simpa [prefixWord, tailWord_222620, baseEnd_222620] using wordTrace_append hprefix tailTrace_222620
  have hstable : (prefixWord ++ tailWord_222620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222620).length < 2 ^ (prefixWord ++ tailWord_222620).sum := by decide
  have hdescent : baseEnd_222620 < baseStart_222620 := by decide
  rcases family_descends (prefixWord ++ tailWord_222620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222664 : List Nat := [2, 1, 3, 1, 3, 1, 8]
def baseStart_222664 : Nat := 118140960795 + 222664 * 2 ^ 59
def prefixEnd_222664 : Nat := 4983230072969 + 3 ^ 40 * 222664 * 2
def baseEnd_222664 : Nat := 22584425965989542671801

theorem tailTrace_222664 : CollatzResearch.WordTrace tailWord_222664 prefixEnd_222664 22584425965989542671801 := by
  unfold tailWord_222664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060611632666915414373523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5414148843555887219164697 4060611632666915414373523)
  ·
    refine ⟨6090917449000373121560285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4060611632666915414373523 6090917449000373121560285)
    ·
      refine ⟨2284094043375139920585107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6090917449000373121560285 2284094043375139920585107)
      ·
        refine ⟨3426141065062709880877661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284094043375139920585107 3426141065062709880877661)
        ·
          refine ⟨1284802899398516205329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3426141065062709880877661 1284802899398516205329123)
          ·
            refine ⟨1927204349097774307993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284802899398516205329123 1927204349097774307993685)
            ·
              refine ⟨22584425965989542671801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1927204349097774307993685 22584425965989542671801)
              ·
                rfl

theorem cell19_222664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_222664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222664 prefixEnd_222664 := by exact prefixLift 222664
  have htrace : WordTrace (prefixWord ++ tailWord_222664) baseStart_222664 baseEnd_222664 := by
    simpa [prefixWord, tailWord_222664, baseEnd_222664] using wordTrace_append hprefix tailTrace_222664
  have hstable : (prefixWord ++ tailWord_222664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222664).length < 2 ^ (prefixWord ++ tailWord_222664).sum := by decide
  have hdescent : baseEnd_222664 < baseStart_222664 := by decide
  rcases family_descends (prefixWord ++ tailWord_222664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222774 : List Nat := [5, 1, 2, 1, 4, 6]
def baseStart_222774 : Nat := 118140960795 + 222774 * 2 ^ 59
def prefixEnd_222774 : Nat := 4983230072969 + 3 ^ 40 * 222774 * 2
def baseEnd_222774 : Nat := 7531861025502329507851

theorem tailTrace_222774 : CollatzResearch.WordTrace tailWord_222774 prefixEnd_222774 7531861025502329507851 := by
  unfold tailWord_222774
  simp only [CollatzResearch.WordTrace]
  refine ⟨507827205933457475953211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5416823529956879743500917 507827205933457475953211)
  ·
    refine ⟨761740808900186213929817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507827205933457475953211 761740808900186213929817)
    ·
      refine ⟨571305606675139660447363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 761740808900186213929817 571305606675139660447363)
      ·
        refine ⟨856958410012709490671045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571305606675139660447363 856958410012709490671045)
        ·
          refine ⟨160679701877383029500821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 856958410012709490671045 160679701877383029500821)
          ·
            refine ⟨7531861025502329507851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160679701877383029500821 7531861025502329507851)
            ·
              rfl

theorem cell19_222774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_222774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222774 prefixEnd_222774 := by exact prefixLift 222774
  have htrace : WordTrace (prefixWord ++ tailWord_222774) baseStart_222774 baseEnd_222774 := by
    simpa [prefixWord, tailWord_222774, baseEnd_222774] using wordTrace_append hprefix tailTrace_222774
  have hstable : (prefixWord ++ tailWord_222774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222774).length < 2 ^ (prefixWord ++ tailWord_222774).sum := by decide
  have hdescent : baseEnd_222774 < baseStart_222774 := by decide
  rcases family_descends (prefixWord ++ tailWord_222774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222812 : List Nat := [2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_222812 : Nat := 118140960795 + 222812 * 2 ^ 59
def prefixEnd_222812 : Nat := 4983230072969 + 3 ^ 40 * 222812 * 2
def baseEnd_222812 : Nat := 67798312053148136726111

theorem tailTrace_222812 : CollatzResearch.WordTrace tailWord_222812 prefixEnd_222812 67798312053148136726111 := by
  unfold tailWord_222812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063310634398826052567345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5417747512531768070089793 4063310634398826052567345)
  ·
    refine ⟨3047482975799119539425509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063310634398826052567345 3047482975799119539425509)
    ·
      refine ⟨571403057962334913642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3047482975799119539425509 571403057962334913642283)
      ·
        refine ⟨857104586943502370463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571403057962334913642283 857104586943502370463425)
        ·
          refine ⟨642828440207626777847569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857104586943502370463425 642828440207626777847569)
          ·
            refine ⟨482121330155720083385677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642828440207626777847569 482121330155720083385677)
            ·
              refine ⟨180795498808395031269629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482121330155720083385677 180795498808395031269629)
              ·
                refine ⟨67798312053148136726111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180795498808395031269629 67798312053148136726111)
                ·
                  rfl

theorem cell19_222812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_222812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222812 prefixEnd_222812 := by exact prefixLift 222812
  have htrace : WordTrace (prefixWord ++ tailWord_222812) baseStart_222812 baseEnd_222812 := by
    simpa [prefixWord, tailWord_222812, baseEnd_222812] using wordTrace_append hprefix tailTrace_222812
  have hstable : (prefixWord ++ tailWord_222812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222812).length < 2 ^ (prefixWord ++ tailWord_222812).sum := by decide
  have hdescent : baseEnd_222812 < baseStart_222812 := by decide
  rcases family_descends (prefixWord ++ tailWord_222812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222871 : List Nat := [1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_222871 : Nat := 118140960795 + 222871 * 2 ^ 59
def prefixEnd_222871 : Nat := 4983230072969 + 3 ^ 40 * 222871 * 2
def baseEnd_222871 : Nat := 67816264858253481414839

theorem tailTrace_222871 : CollatzResearch.WordTrace tailWord_222871 prefixEnd_222871 67816264858253481414839 := by
  unfold tailWord_222871
  simp only [CollatzResearch.WordTrace]
  refine ⟨8128773175583905181532467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5419182117055936787688311 8128773175583905181532467)
  ·
    refine ⟨12193159763375857772298701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8128773175583905181532467 12193159763375857772298701)
    ·
      refine ⟨4572434911265946664612013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12193159763375857772298701 4572434911265946664612013)
      ·
        refine ⟨1714663091724729999229505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4572434911265946664612013 1714663091724729999229505)
        ·
          refine ⟨1285997318793547499422129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714663091724729999229505 1285997318793547499422129)
          ·
            refine ⟨964497989095160624566597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285997318793547499422129 964497989095160624566597)
            ·
              refine ⟨180843372955342617106237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 964497989095160624566597 180843372955342617106237)
              ·
                refine ⟨67816264858253481414839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180843372955342617106237 67816264858253481414839)
                ·
                  rfl

theorem cell19_222871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_222871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222871 prefixEnd_222871 := by exact prefixLift 222871
  have htrace : WordTrace (prefixWord ++ tailWord_222871) baseStart_222871 baseEnd_222871 := by
    simpa [prefixWord, tailWord_222871, baseEnd_222871] using wordTrace_append hprefix tailTrace_222871
  have hstable : (prefixWord ++ tailWord_222871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222871).length < 2 ^ (prefixWord ++ tailWord_222871).sum := by decide
  have hdescent : baseEnd_222871 < baseStart_222871 := by decide
  rcases family_descends (prefixWord ++ tailWord_222871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222911 : List Nat := [1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_222911 : Nat := 118140960795 + 222911 * 2 ^ 59
def prefixEnd_222911 : Nat := 4983230072969 + 3 ^ 40 * 222911 * 2
def baseEnd_222911 : Nat := 67828436251545240525841

theorem tailTrace_222911 : CollatzResearch.WordTrace tailWord_222911 prefixEnd_222911 67828436251545240525841 := by
  unfold tailWord_222911
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130232095438992012988587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5420154730292661341992391 8130232095438992012988587)
  ·
    refine ⟨12195348143158488019482881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130232095438992012988587 12195348143158488019482881)
    ·
      refine ⟨9146511107368866014612161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12195348143158488019482881 9146511107368866014612161)
      ·
        refine ⟨6859883330526649510959121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9146511107368866014612161 6859883330526649510959121)
        ·
          refine ⟨5144912497894987133219341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6859883330526649510959121 5144912497894987133219341)
          ·
            refine ⟨1929342186710620174957253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5144912497894987133219341 1929342186710620174957253)
            ·
              refine ⟨361751660008241282804485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1929342186710620174957253 361751660008241282804485)
              ·
                refine ⟨67828436251545240525841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361751660008241282804485 67828436251545240525841)
                ·
                  rfl

theorem cell19_222911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_222911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222911 prefixEnd_222911 := by exact prefixLift 222911
  have htrace : WordTrace (prefixWord ++ tailWord_222911) baseStart_222911 baseEnd_222911 := by
    simpa [prefixWord, tailWord_222911, baseEnd_222911] using wordTrace_append hprefix tailTrace_222911
  have hstable : (prefixWord ++ tailWord_222911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222911).length < 2 ^ (prefixWord ++ tailWord_222911).sum := by decide
  have hdescent : baseEnd_222911 < baseStart_222911 := by decide
  rcases family_descends (prefixWord ++ tailWord_222911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222947 : List Nat := [1, 1, 1, 7, 3, 6]
def baseStart_222947 : Nat := 118140960795 + 222947 * 2 ^ 59
def prefixEnd_222947 : Nat := 4983230072969 + 3 ^ 40 * 222947 * 2
def baseEnd_222947 : Nat := 7537710056167535969527

theorem tailTrace_222947 : CollatzResearch.WordTrace tailWord_222947 prefixEnd_222947 7537710056167535969527 := by
  unfold tailWord_222947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131545123308570161299095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5421030082205713440866063 8131545123308570161299095)
  ·
    refine ⟨12197317684962855241948643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131545123308570161299095 12197317684962855241948643)
    ·
      refine ⟨18295976527444282862922965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12197317684962855241948643 18295976527444282862922965)
      ·
        refine ⟨428811949861975379599757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18295976527444282862922965 428811949861975379599757)
        ·
          refine ⟨160804481198240767349909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428811949861975379599757 160804481198240767349909)
          ·
            refine ⟨7537710056167535969527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160804481198240767349909 7537710056167535969527)
            ·
              rfl

theorem cell19_222947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_222947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222947 prefixEnd_222947 := by exact prefixLift 222947
  have htrace : WordTrace (prefixWord ++ tailWord_222947) baseStart_222947 baseEnd_222947 := by
    simpa [prefixWord, tailWord_222947, baseEnd_222947] using wordTrace_append hprefix tailTrace_222947
  have hstable : (prefixWord ++ tailWord_222947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222947).length < 2 ^ (prefixWord ++ tailWord_222947).sum := by decide
  have hdescent : baseEnd_222947 < baseStart_222947 := by decide
  rcases family_descends (prefixWord ++ tailWord_222947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222966 : List Nat := [5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_222966 : Nat := 118140960795 + 222966 * 2 ^ 59
def prefixEnd_222966 : Nat := 4983230072969 + 3 ^ 40 * 222966 * 2
def baseEnd_222966 : Nat := 67845171917321409303469

theorem tailTrace_222966 : CollatzResearch.WordTrace tailWord_222966 prefixEnd_222966 67845171917321409303469 := by
  unfold tailWord_222966
  simp only [CollatzResearch.WordTrace]
  refine ⟨508264881889983525390047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5421492073493157604160501 508264881889983525390047)
  ·
    refine ⟨762397322834975288085071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508264881889983525390047 762397322834975288085071)
    ·
      refine ⟨1143595984252462932127607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762397322834975288085071 1143595984252462932127607)
      ·
        refine ⟨1715393976378694398191411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143595984252462932127607 1715393976378694398191411)
        ·
          refine ⟨2573090964568041597287117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715393976378694398191411 2573090964568041597287117)
          ·
            refine ⟨964909111713015598982669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2573090964568041597287117 964909111713015598982669)
            ·
              refine ⟨361840916892380849618501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964909111713015598982669 361840916892380849618501)
              ·
                refine ⟨67845171917321409303469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361840916892380849618501 67845171917321409303469)
                ·
                  rfl

theorem cell19_222966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_222966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222966 prefixEnd_222966 := by exact prefixLift 222966
  have htrace : WordTrace (prefixWord ++ tailWord_222966) baseStart_222966 baseEnd_222966 := by
    simpa [prefixWord, tailWord_222966, baseEnd_222966] using wordTrace_append hprefix tailTrace_222966
  have hstable : (prefixWord ++ tailWord_222966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222966).length < 2 ^ (prefixWord ++ tailWord_222966).sum := by decide
  have hdescent : baseEnd_222966 < baseStart_222966 := by decide
  rcases family_descends (prefixWord ++ tailWord_222966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222983 : List Nat := [1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_222983 : Nat := 118140960795 + 222983 * 2 ^ 59
def prefixEnd_222983 : Nat := 4983230072969 + 3 ^ 40 * 222983 * 2
def baseEnd_222983 : Nat := 67850344759470406925645

theorem tailTrace_222983 : CollatzResearch.WordTrace tailWord_222983 prefixEnd_222983 67850344759470406925645 := by
  unfold tailWord_222983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132858151178148309609603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5421905434118765539739735 8132858151178148309609603)
  ·
    refine ⟨12199287226767222464414405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132858151178148309609603 12199287226767222464414405)
    ·
      refine ⟨2287366355018854212077701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12199287226767222464414405 2287366355018854212077701)
      ·
        refine ⟨428881191566035164764569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2287366355018854212077701 428881191566035164764569)
        ·
          refine ⟨321660893674526373573427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428881191566035164764569 321660893674526373573427)
          ·
            refine ⟨482491340511789560360141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321660893674526373573427 482491340511789560360141)
            ·
              refine ⟨180934252691921085135053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482491340511789560360141 180934252691921085135053)
              ·
                refine ⟨67850344759470406925645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180934252691921085135053 67850344759470406925645)
                ·
                  rfl

theorem cell19_222983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_222983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_222983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_222983 prefixEnd_222983 := by exact prefixLift 222983
  have htrace : WordTrace (prefixWord ++ tailWord_222983) baseStart_222983 baseEnd_222983 := by
    simpa [prefixWord, tailWord_222983, baseEnd_222983] using wordTrace_append hprefix tailTrace_222983
  have hstable : (prefixWord ++ tailWord_222983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222983).length < 2 ^ (prefixWord ++ tailWord_222983).sum := by decide
  have hdescent : baseEnd_222983 < baseStart_222983 := by decide
  rcases family_descends (prefixWord ++ tailWord_222983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223118 : List Nat := [4, 1, 1, 5, 1, 7]
def baseStart_223118 : Nat := 118140960795 + 223118 * 2 ^ 59
def prefixEnd_223118 : Nat := 4983230072969 + 3 ^ 40 * 223118 * 2
def baseEnd_223118 : Nat := 7543491467981121547253

theorem tailTrace_223118 : CollatzResearch.WordTrace tailWord_223118 prefixEnd_223118 7543491467981121547253 := by
  unfold tailWord_223118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017222750711133295721751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5425188003792710910516005 1017222750711133295721751)
  ·
    refine ⟨1525834126066699943582627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017222750711133295721751 1525834126066699943582627)
    ·
      refine ⟨2288751189100049915373941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525834126066699943582627 2288751189100049915373941)
      ·
        refine ⟨214570423978129679566307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2288751189100049915373941 214570423978129679566307)
        ·
          refine ⟨321855635967194519349461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214570423978129679566307 321855635967194519349461)
          ·
            refine ⟨7543491467981121547253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 321855635967194519349461 7543491467981121547253)
            ·
              rfl

theorem cell19_223118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_223118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223118 prefixEnd_223118 := by exact prefixLift 223118
  have htrace : WordTrace (prefixWord ++ tailWord_223118) baseStart_223118 baseEnd_223118 := by
    simpa [prefixWord, tailWord_223118, baseEnd_223118] using wordTrace_append hprefix tailTrace_223118
  have hstable : (prefixWord ++ tailWord_223118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223118).length < 2 ^ (prefixWord ++ tailWord_223118).sum := by decide
  have hdescent : baseEnd_223118 < baseStart_223118 := by decide
  rcases family_descends (prefixWord ++ tailWord_223118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223135 : List Nat := [1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_223135 : Nat := 118140960795 + 223135 * 2 ^ 59
def prefixEnd_223135 : Nat := 4983230072969 + 3 ^ 40 * 223135 * 2
def baseEnd_223135 : Nat := 67896596053979091547453

theorem tailTrace_223135 : CollatzResearch.WordTrace tailWord_223135 prefixEnd_223135 67896596053979091547453 := by
  unfold tailWord_223135
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138402046627478269142859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5425601364418318846095239 8138402046627478269142859)
  ·
    refine ⟨12207603069941217403714289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138402046627478269142859 12207603069941217403714289)
    ·
      refine ⟨9155702302455913052785717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12207603069941217403714289 9155702302455913052785717)
      ·
        refine ⟨858347090855241848698661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9155702302455913052785717 858347090855241848698661)
        ·
          refine ⟨160940079535357846630999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 858347090855241848698661 160940079535357846630999)
          ·
            refine ⟨241410119303036769946499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160940079535357846630999 241410119303036769946499)
            ·
              refine ⟨362115178954555154919749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241410119303036769946499 362115178954555154919749)
              ·
                refine ⟨67896596053979091547453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362115178954555154919749 67896596053979091547453)
                ·
                  rfl

theorem cell19_223135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_223135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223135 prefixEnd_223135 := by exact prefixLift 223135
  have htrace : WordTrace (prefixWord ++ tailWord_223135) baseStart_223135 baseEnd_223135 := by
    simpa [prefixWord, tailWord_223135, baseEnd_223135] using wordTrace_append hprefix tailTrace_223135
  have hstable : (prefixWord ++ tailWord_223135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223135).length < 2 ^ (prefixWord ++ tailWord_223135).sum := by decide
  have hdescent : baseEnd_223135 < baseStart_223135 := by decide
  rcases family_descends (prefixWord ++ tailWord_223135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223150 : List Nat := [4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_223150 : Nat := 118140960795 + 223150 * 2 ^ 59
def prefixEnd_223150 : Nat := 4983230072969 + 3 ^ 40 * 223150 * 2
def baseEnd_223150 : Nat := 67901160326463501214079

theorem tailTrace_223150 : CollatzResearch.WordTrace tailWord_223150 prefixEnd_223150 67901160326463501214079 := by
  unfold tailWord_223150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017368642696641978867363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5425966094382090553959269 1017368642696641978867363)
  ·
    refine ⟨1526052964044962968301045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017368642696641978867363 1526052964044962968301045)
    ·
      refine ⟨143067465379215278278223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1526052964044962968301045 143067465379215278278223)
      ·
        refine ⟨214601198068822917417335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143067465379215278278223 214601198068822917417335)
        ·
          refine ⟨321901797103234376126003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214601198068822917417335 321901797103234376126003)
          ·
            refine ⟨482852695654851564189005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321901797103234376126003 482852695654851564189005)
            ·
              refine ⟨181069760870569336570877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482852695654851564189005 181069760870569336570877)
              ·
                refine ⟨67901160326463501214079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181069760870569336570877 67901160326463501214079)
                ·
                  rfl

theorem cell19_223150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_223150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223150 prefixEnd_223150 := by exact prefixLift 223150
  have htrace : WordTrace (prefixWord ++ tailWord_223150) baseStart_223150 baseEnd_223150 := by
    simpa [prefixWord, tailWord_223150, baseEnd_223150] using wordTrace_append hprefix tailTrace_223150
  have hstable : (prefixWord ++ tailWord_223150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223150).length < 2 ^ (prefixWord ++ tailWord_223150).sum := by decide
  have hdescent : baseEnd_223150 < baseStart_223150 := by decide
  rcases family_descends (prefixWord ++ tailWord_223150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223179 : List Nat := [1, 1, 1, 1, 3, 4, 8]
def baseStart_223179 : Nat := 118140960795 + 223179 * 2 ^ 59
def prefixEnd_223179 : Nat := 4983230072969 + 3 ^ 40 * 223179 * 2
def baseEnd_223179 : Nat := 22636661528866675523185

theorem tailTrace_223179 : CollatzResearch.WordTrace tailWord_223179 prefixEnd_223179 22636661528866675523185 := by
  unfold tailWord_223179
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140006858468073783744591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5426671238978715855829727 8140006858468073783744591)
  ·
    refine ⟨12210010287702110675616887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140006858468073783744591 12210010287702110675616887)
    ·
      refine ⟨18315015431553166013425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210010287702110675616887 18315015431553166013425331)
      ·
        refine ⟨27472523147329749020137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18315015431553166013425331 27472523147329749020137997)
        ·
          refine ⟨10302196180248655882551749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27472523147329749020137997 10302196180248655882551749)
          ·
            refine ⟨1931661783796622977978453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10302196180248655882551749 1931661783796622977978453)
            ·
              refine ⟨22636661528866675523185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1931661783796622977978453 22636661528866675523185)
              ·
                rfl

theorem cell19_223179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_223179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223179 prefixEnd_223179 := by exact prefixLift 223179
  have htrace : WordTrace (prefixWord ++ tailWord_223179) baseStart_223179 baseEnd_223179 := by
    simpa [prefixWord, tailWord_223179, baseEnd_223179] using wordTrace_append hprefix tailTrace_223179
  have hstable : (prefixWord ++ tailWord_223179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223179).length < 2 ^ (prefixWord ++ tailWord_223179).sum := by decide
  have hdescent : baseEnd_223179 < baseStart_223179 := by decide
  rcases family_descends (prefixWord ++ tailWord_223179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223310 : List Nat := [4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_223310 : Nat := 118140960795 + 223310 * 2 ^ 59
def prefixEnd_223310 : Nat := 4983230072969 + 3 ^ 40 * 223310 * 2
def baseEnd_223310 : Nat := 67949845899630537658087

theorem tailTrace_223310 : CollatzResearch.WordTrace tailWord_223310 prefixEnd_223310 67949845899630537658087 := by
  unfold tailWord_223310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018098102624185394595423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5429856547328988771175589 1018098102624185394595423)
  ·
    refine ⟨1527147153936278091893135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018098102624185394595423 1527147153936278091893135)
    ·
      refine ⟨2290720730904417137839703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527147153936278091893135 2290720730904417137839703)
      ·
        refine ⟨3436081096356625706759555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290720730904417137839703 3436081096356625706759555)
        ·
          refine ⟨5154121644534938560139333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436081096356625706759555 5154121644534938560139333)
          ·
            refine ⟨966397808350300980026125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5154121644534938560139333 966397808350300980026125)
            ·
              refine ⟨362399178131362867509797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 966397808350300980026125 362399178131362867509797)
              ·
                refine ⟨67949845899630537658087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362399178131362867509797 67949845899630537658087)
                ·
                  rfl

theorem cell19_223310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_223310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223310 prefixEnd_223310 := by exact prefixLift 223310
  have htrace : WordTrace (prefixWord ++ tailWord_223310) baseStart_223310 baseEnd_223310 := by
    simpa [prefixWord, tailWord_223310, baseEnd_223310] using wordTrace_append hprefix tailTrace_223310
  have hstable : (prefixWord ++ tailWord_223310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223310).length < 2 ^ (prefixWord ++ tailWord_223310).sum := by decide
  have hdescent : baseEnd_223310 < baseStart_223310 := by decide
  rcases family_descends (prefixWord ++ tailWord_223310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223325 : List Nat := [1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_223325 : Nat := 118140960795 + 223325 * 2 ^ 59
def prefixEnd_223325 : Nat := 4983230072969 + 3 ^ 40 * 223325 * 2
def baseEnd_223325 : Nat := 67954410172114947324713

theorem tailTrace_223325 : CollatzResearch.WordTrace tailWord_223325 prefixEnd_223325 67954410172114947324713 := by
  unfold tailWord_223325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145331915939140718559429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5430221277292760479039619 8145331915939140718559429)
  ·
    refine ⟨1527249734238588884729893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8145331915939140718559429 1527249734238588884729893)
    ·
      refine ⟨286359325169735415886855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1527249734238588884729893 286359325169735415886855)
      ·
        refine ⟨429538987754603123830283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286359325169735415886855 429538987754603123830283)
        ·
          refine ⟨644308481631904685745425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429538987754603123830283 644308481631904685745425)
          ·
            refine ⟨483231361223928514309069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644308481631904685745425 483231361223928514309069)
            ·
              refine ⟨181211760458973192865901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483231361223928514309069 181211760458973192865901)
              ·
                refine ⟨67954410172114947324713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181211760458973192865901 67954410172114947324713)
                ·
                  rfl

theorem cell19_223325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_223325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223325 prefixEnd_223325 := by exact prefixLift 223325
  have htrace : WordTrace (prefixWord ++ tailWord_223325) baseStart_223325 baseEnd_223325 := by
    simpa [prefixWord, tailWord_223325, baseEnd_223325] using wordTrace_append hprefix tailTrace_223325
  have hstable : (prefixWord ++ tailWord_223325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223325).length < 2 ^ (prefixWord ++ tailWord_223325).sum := by decide
  have hdescent : baseEnd_223325 < baseStart_223325 := by decide
  rcases family_descends (prefixWord ++ tailWord_223325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223331 : List Nat := [1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_223331 : Nat := 118140960795 + 223331 * 2 ^ 59
def prefixEnd_223331 : Nat := 4983230072969 + 3 ^ 40 * 223331 * 2
def baseEnd_223331 : Nat := 67956235881108711191363

theorem tailTrace_223331 : CollatzResearch.WordTrace tailWord_223331 prefixEnd_223331 67956235881108711191363 := by
  unfold tailWord_223331
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145550753917403743277847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5430367169278269162185231 8145550753917403743277847)
  ·
    refine ⟨12218326130876105614916771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8145550753917403743277847 12218326130876105614916771)
    ·
      refine ⟨18327489196314158422375157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12218326130876105614916771 18327489196314158422375157)
      ·
        refine ⟨1718202112154452352097671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18327489196314158422375157 1718202112154452352097671)
        ·
          refine ⟨2577303168231678528146507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718202112154452352097671 2577303168231678528146507)
          ·
            refine ⟨3865954752347517792219761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577303168231678528146507 3865954752347517792219761)
            ·
              refine ⟨2899466064260638344164821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865954752347517792219761 2899466064260638344164821)
              ·
                refine ⟨67956235881108711191363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899466064260638344164821 67956235881108711191363)
                ·
                  rfl

theorem cell19_223331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_223331 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223331 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223331 prefixEnd_223331 := by exact prefixLift 223331
  have htrace : WordTrace (prefixWord ++ tailWord_223331) baseStart_223331 baseEnd_223331 := by
    simpa [prefixWord, tailWord_223331, baseEnd_223331] using wordTrace_append hprefix tailTrace_223331
  have hstable : (prefixWord ++ tailWord_223331).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223331).length < 2 ^ (prefixWord ++ tailWord_223331).sum := by decide
  have hdescent : baseEnd_223331 < baseStart_223331 := by decide
  rcases family_descends (prefixWord ++ tailWord_223331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223369 : List Nat := [1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_223369 : Nat := 118140960795 + 223369 * 2 ^ 59
def prefixEnd_223369 : Nat := 4983230072969 + 3 ^ 40 * 223369 * 2
def baseEnd_223369 : Nat := 67967798704735882346815

theorem tailTrace_223369 : CollatzResearch.WordTrace tailWord_223369 prefixEnd_223369 67967798704735882346815 := by
  unfold tailWord_223369
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146936727779736233161161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5431291151853157488774107 8146936727779736233161161)
  ·
    refine ⟨6110202545834802174870871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8146936727779736233161161 6110202545834802174870871)
    ·
      refine ⟨9165303818752203262306307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110202545834802174870871 9165303818752203262306307)
      ·
        refine ⟨13747955728128304893459461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9165303818752203262306307 13747955728128304893459461)
        ·
          refine ⟨2577741699024057167523649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13747955728128304893459461 2577741699024057167523649)
          ·
            refine ⟨1933306274268042875642737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577741699024057167523649 1933306274268042875642737)
            ·
              refine ⟨1449979705701032156732053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933306274268042875642737 1449979705701032156732053)
              ·
                refine ⟨67967798704735882346815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1449979705701032156732053 67967798704735882346815)
                ·
                  rfl

theorem cell19_223369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_223369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223369 prefixEnd_223369 := by exact prefixLift 223369
  have htrace : WordTrace (prefixWord ++ tailWord_223369) baseStart_223369 baseEnd_223369 := by
    simpa [prefixWord, tailWord_223369, baseEnd_223369] using wordTrace_append hprefix tailTrace_223369
  have hstable : (prefixWord ++ tailWord_223369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223369).length < 2 ^ (prefixWord ++ tailWord_223369).sum := by decide
  have hdescent : baseEnd_223369 < baseStart_223369 := by decide
  rcases family_descends (prefixWord ++ tailWord_223369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223380 : List Nat := [2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_223380 : Nat := 118140960795 + 223380 * 2 ^ 59
def prefixEnd_223380 : Nat := 4983230072969 + 3 ^ 40 * 223380 * 2
def baseEnd_223380 : Nat := 67971145837891116102341

theorem tailTrace_223380 : CollatzResearch.WordTrace tailWord_223380 prefixEnd_223380 67971145837891116102341 := by
  unfold tailWord_223380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073668965369942555905797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5431558620493256741207729 4073668965369942555905797)
  ·
    refine ⟨763812931006864229232337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4073668965369942555905797 763812931006864229232337)
    ·
      refine ⟨572859698255148171924253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763812931006864229232337 572859698255148171924253)
      ·
        refine ⟨214822386845680564471595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572859698255148171924253 214822386845680564471595)
        ·
          refine ⟨322233580268520846707393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214822386845680564471595 322233580268520846707393)
          ·
            refine ⟨241675185201390635030545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322233580268520846707393 241675185201390635030545)
            ·
              refine ⟨181256388901042976272909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241675185201390635030545 181256388901042976272909)
              ·
                refine ⟨67971145837891116102341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181256388901042976272909 67971145837891116102341)
                ·
                  rfl

theorem cell19_223380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_223380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223380 prefixEnd_223380 := by exact prefixLift 223380
  have htrace : WordTrace (prefixWord ++ tailWord_223380) baseStart_223380 baseEnd_223380 := by
    simpa [prefixWord, tailWord_223380, baseEnd_223380] using wordTrace_append hprefix tailTrace_223380
  have hstable : (prefixWord ++ tailWord_223380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223380).length < 2 ^ (prefixWord ++ tailWord_223380).sum := by decide
  have hdescent : baseEnd_223380 < baseStart_223380 := by decide
  rcases family_descends (prefixWord ++ tailWord_223380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223405 : List Nat := [1, 5, 2, 1, 2, 1, 7]
def baseStart_223405 : Nat := 118140960795 + 223405 * 2 ^ 59
def prefixEnd_223405 : Nat := 4983230072969 + 3 ^ 40 * 223405 * 2
def baseEnd_223405 : Nat := 22659584319566155182239

theorem tailTrace_223405 : CollatzResearch.WordTrace tailWord_223405 prefixEnd_223405 22659584319566155182239 := by
  unfold tailWord_223405
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148249755649314381471669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5432166503766209587647779 8148249755649314381471669)
  ·
    refine ⟨763898414592123223262969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8148249755649314381471669 763898414592123223262969)
    ·
      refine ⟨572923810944092417447227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763898414592123223262969 572923810944092417447227)
      ·
        refine ⟨859385716416138626170841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572923810944092417447227 859385716416138626170841)
        ·
          refine ⟨644539287312103969628131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859385716416138626170841 644539287312103969628131)
          ·
            refine ⟨966808930968155954442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644539287312103969628131 966808930968155954442197)
            ·
              refine ⟨22659584319566155182239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 966808930968155954442197 22659584319566155182239)
              ·
                rfl

theorem cell19_223405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_223405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223405 prefixEnd_223405 := by exact prefixLift 223405
  have htrace : WordTrace (prefixWord ++ tailWord_223405) baseStart_223405 baseEnd_223405 := by
    simpa [prefixWord, tailWord_223405, baseEnd_223405] using wordTrace_append hprefix tailTrace_223405
  have hstable : (prefixWord ++ tailWord_223405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223405).length < 2 ^ (prefixWord ++ tailWord_223405).sum := by decide
  have hdescent : baseEnd_223405 < baseStart_223405 := by decide
  rcases family_descends (prefixWord ++ tailWord_223405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223422 : List Nat := [4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_223422 : Nat := 118140960795 + 223422 * 2 ^ 59
def prefixEnd_223422 : Nat := 4983230072969 + 3 ^ 40 * 223422 * 2
def baseEnd_223422 : Nat := 67983925800847463168893

theorem tailTrace_223422 : CollatzResearch.WordTrace tailWord_223422 prefixEnd_223422 67983925800847463168893 := by
  unfold tailWord_223422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018608724573465785605065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5432579864391817523227013 1018608724573465785605065)
  ·
    refine ⟨763956543430099339203799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1018608724573465785605065 763956543430099339203799)
    ·
      refine ⟨1145934815145149008805699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763956543430099339203799 1145934815145149008805699)
      ·
        refine ⟨1718902222717723513208549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145934815145149008805699 1718902222717723513208549)
        ·
          refine ⟨322294166759573158726603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1718902222717723513208549 322294166759573158726603)
          ·
            refine ⟨483441250139359738089905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322294166759573158726603 483441250139359738089905)
            ·
              refine ⟨362580937604519803567429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483441250139359738089905 362580937604519803567429)
              ·
                refine ⟨67983925800847463168893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362580937604519803567429 67983925800847463168893)
                ·
                  rfl

theorem cell19_223422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_223422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223422 prefixEnd_223422 := by exact prefixLift 223422
  have htrace : WordTrace (prefixWord ++ tailWord_223422) baseStart_223422 baseEnd_223422 := by
    simpa [prefixWord, tailWord_223422, baseEnd_223422] using wordTrace_append hprefix tailTrace_223422
  have hstable : (prefixWord ++ tailWord_223422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223422).length < 2 ^ (prefixWord ++ tailWord_223422).sum := by decide
  have hdescent : baseEnd_223422 < baseStart_223422 := by decide
  rcases family_descends (prefixWord ++ tailWord_223422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223424 : List Nat := [2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_223424 : Nat := 118140960795 + 223424 * 2 ^ 59
def prefixEnd_223424 : Nat := 4983230072969 + 3 ^ 40 * 223424 * 2
def baseEnd_223424 : Nat := 67984534370512051124443

theorem tailTrace_223424 : CollatzResearch.WordTrace tailWord_223424 prefixEnd_223424 67984534370512051124443 := by
  unfold tailWord_223424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074471371290240313206663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5432628495053653750942217 4074471371290240313206663)
  ·
    refine ⟨6111707056935360469809995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074471371290240313206663 6111707056935360469809995)
    ·
      refine ⟨9167560585403040704714993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6111707056935360469809995 9167560585403040704714993)
      ·
        refine ⟨6875670439052280528536245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9167560585403040704714993 6875670439052280528536245)
        ·
          refine ⟨644594103661151299550273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6875670439052280528536245 644594103661151299550273)
          ·
            refine ⟨483445577745863474662705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644594103661151299550273 483445577745863474662705)
            ·
              refine ⟨362584183309397605997029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483445577745863474662705 362584183309397605997029)
              ·
                refine ⟨67984534370512051124443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362584183309397605997029 67984534370512051124443)
                ·
                  rfl

theorem cell19_223424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_223424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223424 prefixEnd_223424 := by exact prefixLift 223424
  have htrace : WordTrace (prefixWord ++ tailWord_223424) baseStart_223424 baseEnd_223424 := by
    simpa [prefixWord, tailWord_223424, baseEnd_223424] using wordTrace_append hprefix tailTrace_223424
  have hstable : (prefixWord ++ tailWord_223424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223424).length < 2 ^ (prefixWord ++ tailWord_223424).sum := by decide
  have hdescent : baseEnd_223424 < baseStart_223424 := by decide
  rcases family_descends (prefixWord ++ tailWord_223424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223458 : List Nat := [3, 3, 4, 1, 1, 7]
def baseStart_223458 : Nat := 118140960795 + 223458 * 2 ^ 59
def prefixEnd_223458 : Nat := 4983230072969 + 3 ^ 40 * 223458 * 2
def baseEnd_223458 : Nat := 7554986672756671818755

theorem tailTrace_223458 : CollatzResearch.WordTrace tailWord_223458 prefixEnd_223458 7554986672756671818755 := by
  unfold tailWord_223458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037545706114326108287757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5433455216304869622100685 2037545706114326108287757)
  ·
    refine ⟨764079639792872290607909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2037545706114326108287757 764079639792872290607909)
    ·
      refine ⟨143264932461163554488983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 764079639792872290607909 143264932461163554488983)
      ·
        refine ⟨214897398691745331733475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143264932461163554488983 214897398691745331733475)
        ·
          refine ⟨322346098037617997600213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214897398691745331733475 322346098037617997600213)
          ·
            refine ⟨7554986672756671818755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 322346098037617997600213 7554986672756671818755)
            ·
              rfl

theorem cell19_223458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_223458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223458 prefixEnd_223458 := by exact prefixLift 223458
  have htrace : WordTrace (prefixWord ++ tailWord_223458) baseStart_223458 baseEnd_223458 := by
    simpa [prefixWord, tailWord_223458, baseEnd_223458] using wordTrace_append hprefix tailTrace_223458
  have hstable : (prefixWord ++ tailWord_223458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223458).length < 2 ^ (prefixWord ++ tailWord_223458).sum := by decide
  have hdescent : baseEnd_223458 < baseStart_223458 := by decide
  rcases family_descends (prefixWord ++ tailWord_223458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223464 : List Nat := [2, 1, 4, 1, 2, 9]
def baseStart_223464 : Nat := 118140960795 + 223464 * 2 ^ 59
def prefixEnd_223464 : Nat := 4983230072969 + 3 ^ 40 * 223464 * 2
def baseEnd_223464 : Nat := 7555189529311534470605

theorem tailTrace_223464 : CollatzResearch.WordTrace tailWord_223464 prefixEnd_223464 7555189529311534470605 := by
  unfold tailWord_223464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075200831217783728934723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5433601108290378305246297 4075200831217783728934723)
  ·
    refine ⟨6112801246826675593402085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075200831217783728934723 6112801246826675593402085)
    ·
      refine ⟨1146150233780001673762891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6112801246826675593402085 1146150233780001673762891)
      ·
        refine ⟨1719225350670002510644337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146150233780001673762891 1719225350670002510644337)
        ·
          refine ⟨1289419013002501882983253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719225350670002510644337 1289419013002501882983253)
          ·
            refine ⟨7555189529311534470605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1289419013002501882983253 7555189529311534470605)
            ·
              rfl

theorem cell19_223464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_223464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223464 prefixEnd_223464 := by exact prefixLift 223464
  have htrace : WordTrace (prefixWord ++ tailWord_223464) baseStart_223464 baseEnd_223464 := by
    simpa [prefixWord, tailWord_223464, baseEnd_223464] using wordTrace_append hprefix tailTrace_223464
  have hstable : (prefixWord ++ tailWord_223464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223464).length < 2 ^ (prefixWord ++ tailWord_223464).sum := by decide
  have hdescent : baseEnd_223464 < baseStart_223464 := by decide
  rcases family_descends (prefixWord ++ tailWord_223464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223500 : List Nat := [2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_223500 : Nat := 118140960795 + 223500 * 2 ^ 59
def prefixEnd_223500 : Nat := 4983230072969 + 3 ^ 40 * 223500 * 2
def baseEnd_223500 : Nat := 68007660017766393435347

theorem tailTrace_223500 : CollatzResearch.WordTrace tailWord_223500 prefixEnd_223500 68007660017766393435347 := by
  unfold tailWord_223500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075857345152572803089977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5434476460203430404119969 4075857345152572803089977)
  ·
    refine ⟨3056893008864429602317483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4075857345152572803089977 3056893008864429602317483)
    ·
      refine ⟨4585339513296644403476225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056893008864429602317483 4585339513296644403476225)
      ·
        refine ⟨3439004634972483302607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585339513296644403476225 3439004634972483302607169)
        ·
          refine ⟨2579253476229362476955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439004634972483302607169 2579253476229362476955377)
          ·
            refine ⟨1934440107172021857716533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579253476229362476955377 1934440107172021857716533)
            ·
              refine ⟨181353760047377049160925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1934440107172021857716533 181353760047377049160925)
              ·
                refine ⟨68007660017766393435347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181353760047377049160925 68007660017766393435347)
                ·
                  rfl

theorem cell19_223500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_223500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223500 prefixEnd_223500 := by exact prefixLift 223500
  have htrace : WordTrace (prefixWord ++ tailWord_223500) baseStart_223500 baseEnd_223500 := by
    simpa [prefixWord, tailWord_223500, baseEnd_223500] using wordTrace_append hprefix tailTrace_223500
  have hstable : (prefixWord ++ tailWord_223500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223500).length < 2 ^ (prefixWord ++ tailWord_223500).sum := by decide
  have hdescent : baseEnd_223500 < baseStart_223500 := by decide
  rcases family_descends (prefixWord ++ tailWord_223500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223553 : List Nat := [1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_223553 : Nat := 118140960795 + 223553 * 2 ^ 59
def prefixEnd_223553 : Nat := 4983230072969 + 3 ^ 40 * 223553 * 2
def baseEnd_223553 : Nat := 68023787113877974257425

theorem tailTrace_223553 : CollatzResearch.WordTrace tailWord_223553 prefixEnd_223553 68023787113877974257425 := by
  unfold tailWord_223553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153647759113135657859313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5435765172742090438572875 8153647759113135657859313)
  ·
    refine ⟨6115235819334851743394485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8153647759113135657859313 6115235819334851743394485)
    ·
      refine ⟨573303358062642350943233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6115235819334851743394485 573303358062642350943233)
      ·
        refine ⟨429977518546981763207425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573303358062642350943233 429977518546981763207425)
        ·
          refine ⟨322483138910236322405569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429977518546981763207425 322483138910236322405569)
          ·
            refine ⟨241862354182677241804177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322483138910236322405569 241862354182677241804177)
            ·
              refine ⟨181396765637007931353133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241862354182677241804177 181396765637007931353133)
              ·
                refine ⟨68023787113877974257425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181396765637007931353133 68023787113877974257425)
                ·
                  rfl

theorem cell19_223553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_223553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223553 prefixEnd_223553 := by exact prefixLift 223553
  have htrace : WordTrace (prefixWord ++ tailWord_223553) baseStart_223553 baseEnd_223553 := by
    simpa [prefixWord, tailWord_223553, baseEnd_223553] using wordTrace_append hprefix tailTrace_223553
  have hstable : (prefixWord ++ tailWord_223553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223553).length < 2 ^ (prefixWord ++ tailWord_223553).sum := by decide
  have hdescent : baseEnd_223553 < baseStart_223553 := by decide
  rcases family_descends (prefixWord ++ tailWord_223553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223559 : List Nat := [1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_223559 : Nat := 118140960795 + 223559 * 2 ^ 59
def prefixEnd_223559 : Nat := 4983230072969 + 3 ^ 40 * 223559 * 2
def baseEnd_223559 : Nat := 68025612822871738124075

theorem tailTrace_223559 : CollatzResearch.WordTrace tailWord_223559 prefixEnd_223559 68025612822871738124075 := by
  unfold tailWord_223559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153866597091398682577731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5435911064727599121718487 8153866597091398682577731)
  ·
    refine ⟨12230799895637098023866597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153866597091398682577731 12230799895637098023866597)
    ·
      refine ⟨2293274980431955879474987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12230799895637098023866597 2293274980431955879474987)
      ·
        refine ⟨3439912470647933819212481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2293274980431955879474987 3439912470647933819212481)
        ·
          refine ⟨2579934352985950364409361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439912470647933819212481 2579934352985950364409361)
          ·
            refine ⟨1934950764739462773307021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579934352985950364409361 1934950764739462773307021)
            ·
              refine ⟨725606536777298539990133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1934950764739462773307021 725606536777298539990133)
              ·
                refine ⟨68025612822871738124075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 725606536777298539990133 68025612822871738124075)
                ·
                  rfl

theorem cell19_223559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_223559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223559 prefixEnd_223559 := by exact prefixLift 223559
  have htrace : WordTrace (prefixWord ++ tailWord_223559) baseStart_223559 baseEnd_223559 := by
    simpa [prefixWord, tailWord_223559, baseEnd_223559] using wordTrace_append hprefix tailTrace_223559
  have hstable : (prefixWord ++ tailWord_223559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223559).length < 2 ^ (prefixWord ++ tailWord_223559).sum := by decide
  have hdescent : baseEnd_223559 < baseStart_223559 := by decide
  rcases family_descends (prefixWord ++ tailWord_223559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223669 : List Nat := [1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_223669 : Nat := 118140960795 + 223669 * 2 ^ 59
def prefixEnd_223669 : Nat := 4983230072969 + 3 ^ 40 * 223669 * 2
def baseEnd_223669 : Nat := 68059084154424075679331

theorem tailTrace_223669 : CollatzResearch.WordTrace tailWord_223669 prefixEnd_223669 68059084154424075679331 := by
  unfold tailWord_223669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157878626692887469082061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5438585751128591646054707 8157878626692887469082061)
  ·
    refine ⟨3059204485009832800905773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8157878626692887469082061 3059204485009832800905773)
    ·
      refine ⟨1147201681878687300339665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3059204485009832800905773 1147201681878687300339665)
      ·
        refine ⟨860401261409015475254749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1147201681878687300339665 860401261409015475254749)
        ·
          refine ⟨322650473028380803220531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860401261409015475254749 322650473028380803220531)
          ·
            refine ⟨483975709542571204830797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322650473028380803220531 483975709542571204830797)
            ·
              refine ⟨181490891078464201811549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483975709542571204830797 181490891078464201811549)
              ·
                refine ⟨68059084154424075679331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181490891078464201811549 68059084154424075679331)
                ·
                  rfl

theorem cell19_223669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_223669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223669 prefixEnd_223669 := by exact prefixLift 223669
  have htrace : WordTrace (prefixWord ++ tailWord_223669) baseStart_223669 baseEnd_223669 := by
    simpa [prefixWord, tailWord_223669, baseEnd_223669] using wordTrace_append hprefix tailTrace_223669
  have hstable : (prefixWord ++ tailWord_223669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223669).length < 2 ^ (prefixWord ++ tailWord_223669).sum := by decide
  have hdescent : baseEnd_223669 < baseStart_223669 := by decide
  rcases family_descends (prefixWord ++ tailWord_223669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223671 : List Nat := [1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_223671 : Nat := 118140960795 + 223671 * 2 ^ 59
def prefixEnd_223671 : Nat := 4983230072969 + 3 ^ 40 * 223671 * 2
def baseEnd_223671 : Nat := 68059692724088663634881

theorem tailTrace_223671 : CollatzResearch.WordTrace tailWord_223671 prefixEnd_223671 68059692724088663634881 := by
  unfold tailWord_223671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157951572685641810654867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5438634381790427873769911 8157951572685641810654867)
  ·
    refine ⟨12236927359028462715982301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157951572685641810654867 12236927359028462715982301)
    ·
      refine ⟨4588847759635673518493363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12236927359028462715982301 4588847759635673518493363)
      ·
        refine ⟨6883271639453510277740045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588847759635673518493363 6883271639453510277740045)
        ·
          refine ⟨2581226864795066354152517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6883271639453510277740045 2581226864795066354152517)
          ·
            refine ⟨483980037149074941403597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2581226864795066354152517 483980037149074941403597)
            ·
              refine ⟨181492513930903103026349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483980037149074941403597 181492513930903103026349)
              ·
                refine ⟨68059692724088663634881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181492513930903103026349 68059692724088663634881)
                ·
                  rfl

theorem cell19_223671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_223671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223671 prefixEnd_223671 := by exact prefixLift 223671
  have htrace : WordTrace (prefixWord ++ tailWord_223671) baseStart_223671 baseEnd_223671 := by
    simpa [prefixWord, tailWord_223671, baseEnd_223671] using wordTrace_append hprefix tailTrace_223671
  have hstable : (prefixWord ++ tailWord_223671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223671).length < 2 ^ (prefixWord ++ tailWord_223671).sum := by decide
  have hdescent : baseEnd_223671 < baseStart_223671 := by decide
  rcases family_descends (prefixWord ++ tailWord_223671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223726 : List Nat := [4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_223726 : Nat := 118140960795 + 223726 * 2 ^ 59
def prefixEnd_223726 : Nat := 4983230072969 + 3 ^ 40 * 223726 * 2
def baseEnd_223726 : Nat := 68076428389864832412509

theorem tailTrace_223726 : CollatzResearch.WordTrace tailWord_223726 prefixEnd_223726 68076428389864832412509 := by
  unfold tailWord_223726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019994698435798275488379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5439971724990924135938021 1019994698435798275488379)
  ·
    refine ⟨1529992047653697413232569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019994698435798275488379 1529992047653697413232569)
    ·
      refine ⟨1147494035740273059924427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1529992047653697413232569 1147494035740273059924427)
      ·
        refine ⟨1721241053610409589886641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147494035740273059924427 1721241053610409589886641)
        ·
          refine ⟨1290930790207807192414981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721241053610409589886641 1290930790207807192414981)
          ·
            refine ⟨242049523163963848577809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1290930790207807192414981 242049523163963848577809)
            ·
              refine ⟨181537142372972886433357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242049523163963848577809 181537142372972886433357)
              ·
                refine ⟨68076428389864832412509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181537142372972886433357 68076428389864832412509)
                ·
                  rfl

theorem cell19_223726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_223726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223726 prefixEnd_223726 := by exact prefixLift 223726
  have htrace : WordTrace (prefixWord ++ tailWord_223726) baseStart_223726 baseEnd_223726 := by
    simpa [prefixWord, tailWord_223726, baseEnd_223726] using wordTrace_append hprefix tailTrace_223726
  have hstable : (prefixWord ++ tailWord_223726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223726).length < 2 ^ (prefixWord ++ tailWord_223726).sum := by decide
  have hdescent : baseEnd_223726 < baseStart_223726 := by decide
  rcases family_descends (prefixWord ++ tailWord_223726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223764 : List Nat := [2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_223764 : Nat := 118140960795 + 223764 * 2 ^ 59
def prefixEnd_223764 : Nat := 4983230072969 + 3 ^ 40 * 223764 * 2
def baseEnd_223764 : Nat := 68087991213492003567961

theorem tailTrace_223764 : CollatzResearch.WordTrace tailWord_223764 prefixEnd_223764 68087991213492003567961 := by
  unfold tailWord_223764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080671780674359346895173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5440895707565812462526897 4080671780674359346895173)
  ·
    refine ⟨765125958876442377542845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4080671780674359346895173 765125958876442377542845)
    ·
      refine ⟨286922234578665891578567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 765125958876442377542845 286922234578665891578567)
      ·
        refine ⟨430383351867998837367851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286922234578665891578567 430383351867998837367851)
        ·
          refine ⟨645575027801998256051777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430383351867998837367851 645575027801998256051777)
          ·
            refine ⟨484181270851498692038833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645575027801998256051777 484181270851498692038833)
            ·
              refine ⟨363135953138624019029125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484181270851498692038833 363135953138624019029125)
              ·
                refine ⟨68087991213492003567961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363135953138624019029125 68087991213492003567961)
                ·
                  rfl

theorem cell19_223764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_223764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223764 prefixEnd_223764 := by exact prefixLift 223764
  have htrace : WordTrace (prefixWord ++ tailWord_223764) baseStart_223764 baseEnd_223764 := by
    simpa [prefixWord, tailWord_223764, baseEnd_223764] using wordTrace_append hprefix tailTrace_223764
  have hstable : (prefixWord ++ tailWord_223764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223764).length < 2 ^ (prefixWord ++ tailWord_223764).sum := by decide
  have hdescent : baseEnd_223764 < baseStart_223764 := by decide
  rcases family_descends (prefixWord ++ tailWord_223764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223768 : List Nat := [2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_223768 : Nat := 118140960795 + 223768 * 2 ^ 59
def prefixEnd_223768 : Nat := 4983230072969 + 3 ^ 40 * 223768 * 2
def baseEnd_223768 : Nat := 68089208352821179479061

theorem tailTrace_223768 : CollatzResearch.WordTrace tailWord_223768 prefixEnd_223768 68089208352821179479061 := by
  unfold tailWord_223768
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080744726667113688467979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5440992968889484917957305 4080744726667113688467979)
  ·
    refine ⟨6121117090000670532701969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4080744726667113688467979 6121117090000670532701969)
    ·
      refine ⟨4590837817500502899526477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6121117090000670532701969 4590837817500502899526477)
      ·
        refine ⟨1721564181562688587322429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4590837817500502899526477 1721564181562688587322429)
        ·
          refine ⟨645586568086008220245911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1721564181562688587322429 645586568086008220245911)
          ·
            refine ⟨968379852129012330368867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645586568086008220245911 968379852129012330368867)
            ·
              refine ⟨1452569778193518495553301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968379852129012330368867 1452569778193518495553301)
              ·
                refine ⟨68089208352821179479061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1452569778193518495553301 68089208352821179479061)
                ·
                  rfl

theorem cell19_223768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_223768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223768 prefixEnd_223768 := by exact prefixLift 223768
  have htrace : WordTrace (prefixWord ++ tailWord_223768) baseStart_223768 baseEnd_223768 := by
    simpa [prefixWord, tailWord_223768, baseEnd_223768] using wordTrace_append hprefix tailTrace_223768
  have hstable : (prefixWord ++ tailWord_223768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223768).length < 2 ^ (prefixWord ++ tailWord_223768).sum := by decide
  have hdescent : baseEnd_223768 < baseStart_223768 := by decide
  rcases family_descends (prefixWord ++ tailWord_223768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223821 : List Nat := [1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_223821 : Nat := 118140960795 + 223821 * 2 ^ 59
def prefixEnd_223821 : Nat := 4983230072969 + 3 ^ 40 * 223821 * 2
def baseEnd_223821 : Nat := 68105335448932760301139

theorem tailTrace_223821 : CollatzResearch.WordTrace tailWord_223821 prefixEnd_223821 68105335448932760301139 := by
  unfold tailWord_223821
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163422522142217428615317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442281681428144952410211 8163422522142217428615317)
  ·
    refine ⟨382660430725416441966343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8163422522142217428615317 382660430725416441966343)
    ·
      refine ⟨573990646088124662949515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382660430725416441966343 573990646088124662949515)
      ·
        refine ⟨860985969132186994424273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573990646088124662949515 860985969132186994424273)
        ·
          refine ⟨645739476849140245818205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860985969132186994424273 645739476849140245818205)
          ·
            refine ⟨242152303818427592181827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645739476849140245818205 242152303818427592181827)
            ·
              refine ⟨363228455727641388272741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242152303818427592181827 363228455727641388272741)
              ·
                refine ⟨68105335448932760301139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363228455727641388272741 68105335448932760301139)
                ·
                  rfl

theorem cell19_223821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_223821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223821 prefixEnd_223821 := by exact prefixLift 223821
  have htrace : WordTrace (prefixWord ++ tailWord_223821) baseStart_223821 baseEnd_223821 := by
    simpa [prefixWord, tailWord_223821, baseEnd_223821] using wordTrace_append hprefix tailTrace_223821
  have hstable : (prefixWord ++ tailWord_223821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223821).length < 2 ^ (prefixWord ++ tailWord_223821).sum := by decide
  have hdescent : baseEnd_223821 < baseStart_223821 := by decide
  rcases family_descends (prefixWord ++ tailWord_223821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223825 : List Nat := [1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_223825 : Nat := 118140960795 + 223825 * 2 ^ 59
def prefixEnd_223825 : Nat := 4983230072969 + 3 ^ 40 * 223825 * 2
def baseEnd_223825 : Nat := 68106552588261936212239

theorem tailTrace_223825 : CollatzResearch.WordTrace tailWord_223825 prefixEnd_223825 68106552588261936212239 := by
  unfold tailWord_223825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163568414127726111760929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442378942751817407840619 8163568414127726111760929)
  ·
    refine ⟨6122676310595794583820697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8163568414127726111760929 6122676310595794583820697)
    ·
      refine ⟨4592007232946845937865523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6122676310595794583820697 4592007232946845937865523)
      ·
        refine ⟨6888010849420268906798285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592007232946845937865523 6888010849420268906798285)
        ·
          refine ⟨2583004068532600840049357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6888010849420268906798285 2583004068532600840049357)
          ·
            refine ⟨968626525699725315018509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2583004068532600840049357 968626525699725315018509)
            ·
              refine ⟨363234947137396993131941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 968626525699725315018509 363234947137396993131941)
              ·
                refine ⟨68106552588261936212239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363234947137396993131941 68106552588261936212239)
                ·
                  rfl

theorem cell19_223825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_223825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223825 prefixEnd_223825 := by exact prefixLift 223825
  have htrace : WordTrace (prefixWord ++ tailWord_223825) baseStart_223825 baseEnd_223825 := by
    simpa [prefixWord, tailWord_223825, baseEnd_223825] using wordTrace_append hprefix tailTrace_223825
  have hstable : (prefixWord ++ tailWord_223825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223825).length < 2 ^ (prefixWord ++ tailWord_223825).sum := by decide
  have hdescent : baseEnd_223825 < baseStart_223825 := by decide
  rcases family_descends (prefixWord ++ tailWord_223825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223861 : List Nat := [1, 3, 4, 2, 2, 1, 6]
def baseStart_223861 : Nat := 118140960795 + 223861 * 2 ^ 59
def prefixEnd_223861 : Nat := 4983230072969 + 3 ^ 40 * 223861 * 2
def baseEnd_223861 : Nat := 22705835614074839804047

theorem tailTrace_223861 : CollatzResearch.WordTrace tailWord_223861 prefixEnd_223861 22705835614074839804047 := by
  unfold tailWord_223861
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164881441997304260071437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5443254294664869506714291 8164881441997304260071437)
  ·
    refine ⟨3061830540748989097526789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8164881441997304260071437 3061830540748989097526789)
    ·
      refine ⟨574093226390435455786273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3061830540748989097526789 574093226390435455786273)
      ·
        refine ⟨430569919792826591839705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574093226390435455786273 430569919792826591839705)
        ·
          refine ⟨322927439844619943879779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430569919792826591839705 322927439844619943879779)
          ·
            refine ⟨484391159766929915819669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322927439844619943879779 484391159766929915819669)
            ·
              refine ⟨22705835614074839804047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484391159766929915819669 22705835614074839804047)
              ·
                rfl

theorem cell19_223861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_223861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223861 prefixEnd_223861 := by exact prefixLift 223861
  have htrace : WordTrace (prefixWord ++ tailWord_223861) baseStart_223861 baseEnd_223861 := by
    simpa [prefixWord, tailWord_223861, baseEnd_223861] using wordTrace_append hprefix tailTrace_223861
  have hstable : (prefixWord ++ tailWord_223861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223861).length < 2 ^ (prefixWord ++ tailWord_223861).sum := by decide
  have hdescent : baseEnd_223861 < baseStart_223861 := by decide
  rcases family_descends (prefixWord ++ tailWord_223861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223914 : List Nat := [3, 1, 5, 2, 2, 1, 5]
def baseStart_223914 : Nat := 118140960795 + 223914 * 2 ^ 59
def prefixEnd_223914 : Nat := 4983230072969 + 3 ^ 40 * 223914 * 2
def baseEnd_223914 : Nat := 22711211312778700078073

theorem tailTrace_223914 : CollatzResearch.WordTrace tailWord_223914 prefixEnd_223914 22711211312778700078073 := by
  unfold tailWord_223914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041703627701323577937699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5444543007203529541167197 2041703627701323577937699)
  ·
    refine ⟨3062555441551985366906549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041703627701323577937699 3062555441551985366906549)
    ·
      refine ⟨287114572645498628147489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3062555441551985366906549 287114572645498628147489)
      ·
        refine ⟨215335929484123971110617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287114572645498628147489 215335929484123971110617)
        ·
          refine ⟨161501947113092978332963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215335929484123971110617 161501947113092978332963)
          ·
            refine ⟨242252920669639467499445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161501947113092978332963 242252920669639467499445)
            ·
              refine ⟨22711211312778700078073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242252920669639467499445 22711211312778700078073)
              ·
                rfl

theorem cell19_223914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_223914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223914 prefixEnd_223914 := by exact prefixLift 223914
  have htrace : WordTrace (prefixWord ++ tailWord_223914) baseStart_223914 baseEnd_223914 := by
    simpa [prefixWord, tailWord_223914, baseEnd_223914] using wordTrace_append hprefix tailTrace_223914
  have hstable : (prefixWord ++ tailWord_223914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223914).length < 2 ^ (prefixWord ++ tailWord_223914).sum := by decide
  have hdescent : baseEnd_223914 < baseStart_223914 := by decide
  rcases family_descends (prefixWord ++ tailWord_223914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223918 : List Nat := [4, 1, 4, 1, 1, 1, 7]
def baseStart_223918 : Nat := 118140960795 + 223918 * 2 ^ 59
def prefixEnd_223918 : Nat := 4983230072969 + 3 ^ 40 * 223918 * 2
def baseEnd_223918 : Nat := 22711617025888425381773

theorem tailTrace_223918 : CollatzResearch.WordTrace tailWord_223918 prefixEnd_223918 22711617025888425381773 := by
  unfold tailWord_223918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020870050348850374362051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5444640268527201996597605 1020870050348850374362051)
  ·
    refine ⟨1531305075523275561543077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020870050348850374362051 1531305075523275561543077)
    ·
      refine ⟨287119701660614167789327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1531305075523275561543077 287119701660614167789327)
      ·
        refine ⟨430679552490921251683991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287119701660614167789327 430679552490921251683991)
        ·
          refine ⟨646019328736381877525987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430679552490921251683991 646019328736381877525987)
          ·
            refine ⟨969028993104572816288981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646019328736381877525987 969028993104572816288981)
            ·
              refine ⟨22711617025888425381773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 969028993104572816288981 22711617025888425381773)
              ·
                rfl

theorem cell19_223918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_223918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223918 prefixEnd_223918 := by exact prefixLift 223918
  have htrace : WordTrace (prefixWord ++ tailWord_223918) baseStart_223918 baseEnd_223918 := by
    simpa [prefixWord, tailWord_223918, baseEnd_223918] using wordTrace_append hprefix tailTrace_223918
  have hstable : (prefixWord ++ tailWord_223918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223918).length < 2 ^ (prefixWord ++ tailWord_223918).sum := by decide
  have hdescent : baseEnd_223918 < baseStart_223918 := by decide
  rcases family_descends (prefixWord ++ tailWord_223918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223988 : List Nat := [2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_223988 : Nat := 118140960795 + 223988 * 2 ^ 59
def prefixEnd_223988 : Nat := 4983230072969 + 3 ^ 40 * 223988 * 2
def baseEnd_223988 : Nat := 68156151015925854589573

theorem tailTrace_223988 : CollatzResearch.WordTrace tailWord_223988 prefixEnd_223988 68156151015925854589573 := by
  unfold tailWord_223988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084756756268602474972309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5446342341691469966629745 4084756756268602474972309)
  ·
    refine ⟨191472972950090741014327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4084756756268602474972309 191472972950090741014327)
    ·
      refine ⟨287209459425136111521491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191472972950090741014327 287209459425136111521491)
      ·
        refine ⟨430814189137704167282237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287209459425136111521491 430814189137704167282237)
        ·
          refine ⟨161555320926639062730839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430814189137704167282237 161555320926639062730839)
          ·
            refine ⟨242332981389958594096259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161555320926639062730839 242332981389958594096259)
            ·
              refine ⟨363499472084937891144389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242332981389958594096259 363499472084937891144389)
              ·
                refine ⟨68156151015925854589573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363499472084937891144389 68156151015925854589573)
                ·
                  rfl

theorem cell19_223988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_223988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223988 prefixEnd_223988 := by exact prefixLift 223988
  have htrace : WordTrace (prefixWord ++ tailWord_223988) baseStart_223988 baseEnd_223988 := by
    simpa [prefixWord, tailWord_223988, baseEnd_223988] using wordTrace_append hprefix tailTrace_223988
  have hstable : (prefixWord ++ tailWord_223988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223988).length < 2 ^ (prefixWord ++ tailWord_223988).sum := by decide
  have hdescent : baseEnd_223988 < baseStart_223988 := by decide
  rcases family_descends (prefixWord ++ tailWord_223988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223996 : List Nat := [2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_223996 : Nat := 118140960795 + 223996 * 2 ^ 59
def prefixEnd_223996 : Nat := 4983230072969 + 3 ^ 40 * 223996 * 2
def baseEnd_223996 : Nat := 68158585294584206411773

theorem tailTrace_223996 : CollatzResearch.WordTrace tailWord_223996 prefixEnd_223996 68158585294584206411773 := by
  unfold tailWord_223996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084902648254111158117921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5446536864338814877490561 4084902648254111158117921)
  ·
    refine ⟨3063676986190583368588441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4084902648254111158117921 3063676986190583368588441)
    ·
      refine ⟨2297757739642937526441331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3063676986190583368588441 2297757739642937526441331)
      ·
        refine ⟨3446636609464406289661997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297757739642937526441331 3446636609464406289661997)
        ·
          refine ⟨1292488728549152358623249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3446636609464406289661997 1292488728549152358623249)
          ·
            refine ⟨969366546411864268967437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292488728549152358623249 969366546411864268967437)
            ·
              refine ⟨363512454904449100862789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969366546411864268967437 363512454904449100862789)
              ·
                refine ⟨68158585294584206411773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363512454904449100862789 68158585294584206411773)
                ·
                  rfl

theorem cell19_223996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_223996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_223996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_223996 prefixEnd_223996 := by exact prefixLift 223996
  have htrace : WordTrace (prefixWord ++ tailWord_223996) baseStart_223996 baseEnd_223996 := by
    simpa [prefixWord, tailWord_223996, baseEnd_223996] using wordTrace_append hprefix tailTrace_223996
  have hstable : (prefixWord ++ tailWord_223996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223996).length < 2 ^ (prefixWord ++ tailWord_223996).sum := by decide
  have hdescent : baseEnd_223996 < baseStart_223996 := by decide
  rcases family_descends (prefixWord ++ tailWord_223996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224015 : List Nat := [1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_224015 : Nat := 118140960795 + 224015 * 2 ^ 59
def prefixEnd_224015 : Nat := 4983230072969 + 3 ^ 40 * 224015 * 2
def baseEnd_224015 : Nat := 68164366706397791989499

theorem tailTrace_224015 : CollatzResearch.WordTrace tailWord_224015 prefixEnd_224015 68164366706397791989499 := by
  unfold tailWord_224015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170498283439388561177499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446998855626259040784999 8170498283439388561177499)
  ·
    refine ⟨12255747425159082841766249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8170498283439388561177499 12255747425159082841766249)
    ·
      refine ⟨9191810568869312131324687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12255747425159082841766249 9191810568869312131324687)
      ·
        refine ⟨13787715853303968196987031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191810568869312131324687 13787715853303968196987031)
        ·
          refine ⟨20681573779955952295480547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13787715853303968196987031 20681573779955952295480547)
          ·
            refine ⟨31022360669933928443220821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20681573779955952295480547 31022360669933928443220821)
            ·
              refine ⟨181771644550394111971997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 31022360669933928443220821 181771644550394111971997)
              ·
                refine ⟨68164366706397791989499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181771644550394111971997 68164366706397791989499)
                ·
                  rfl

theorem cell19_224015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_224015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224015 prefixEnd_224015 := by exact prefixLift 224015
  have htrace : WordTrace (prefixWord ++ tailWord_224015) baseStart_224015 baseEnd_224015 := by
    simpa [prefixWord, tailWord_224015, baseEnd_224015] using wordTrace_append hprefix tailTrace_224015
  have hstable : (prefixWord ++ tailWord_224015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224015).length < 2 ^ (prefixWord ++ tailWord_224015).sum := by decide
  have hdescent : baseEnd_224015 < baseStart_224015 := by decide
  rcases family_descends (prefixWord ++ tailWord_224015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224017 : List Nat := [1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_224017 : Nat := 118140960795 + 224017 * 2 ^ 59
def prefixEnd_224017 : Nat := 4983230072969 + 3 ^ 40 * 224017 * 2
def baseEnd_224017 : Nat := 68164975276062379945049

theorem tailTrace_224017 : CollatzResearch.WordTrace tailWord_224017 prefixEnd_224017 68164975276062379945049 := by
  unfold tailWord_224017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8170571229432142902750305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5447047486288095268500203 8170571229432142902750305)
  ·
    refine ⟨6127928422074107177062729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8170571229432142902750305 6127928422074107177062729)
    ·
      refine ⟨4595946316555580382797047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6127928422074107177062729 4595946316555580382797047)
      ·
        refine ⟨6893919474833370574195571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595946316555580382797047 6893919474833370574195571)
        ·
          refine ⟨10340879212250055861293357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893919474833370574195571 10340879212250055861293357)
          ·
            refine ⟨3877829704593770947985009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10340879212250055861293357 3877829704593770947985009)
            ·
              refine ⟨2908372278445328210988757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877829704593770947985009 2908372278445328210988757)
              ·
                refine ⟨68164975276062379945049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2908372278445328210988757 68164975276062379945049)
                ·
                  rfl

theorem cell19_224017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_224017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224017 prefixEnd_224017 := by exact prefixLift 224017
  have htrace : WordTrace (prefixWord ++ tailWord_224017) baseStart_224017 baseEnd_224017 := by
    simpa [prefixWord, tailWord_224017, baseEnd_224017] using wordTrace_append hprefix tailTrace_224017
  have hstable : (prefixWord ++ tailWord_224017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224017).length < 2 ^ (prefixWord ++ tailWord_224017).sum := by decide
  have hdescent : baseEnd_224017 < baseStart_224017 := by decide
  rcases family_descends (prefixWord ++ tailWord_224017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224034 : List Nat := [3, 3, 1, 1, 2, 3, 6]
def baseStart_224034 : Nat := 118140960795 + 224034 * 2 ^ 59
def prefixEnd_224034 : Nat := 4983230072969 + 3 ^ 40 * 224034 * 2
def baseEnd_224034 : Nat := 22723382706070459189075

theorem tailTrace_224034 : CollatzResearch.WordTrace tailWord_224034 prefixEnd_224034 22723382706070459189075 := by
  unfold tailWord_224034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042797817592638701529789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5447460846913703204079437 2042797817592638701529789)
  ·
    refine ⟨766049181597239513073671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2042797817592638701529789 766049181597239513073671)
    ·
      refine ⟨1149073772395859269610507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766049181597239513073671 1149073772395859269610507)
      ·
        refine ⟨1723610658593788904415761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149073772395859269610507 1723610658593788904415761)
        ·
          refine ⟨1292707993945341678311821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723610658593788904415761 1292707993945341678311821)
          ·
            refine ⟨484765497729503129366933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292707993945341678311821 484765497729503129366933)
            ·
              refine ⟨22723382706070459189075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484765497729503129366933 22723382706070459189075)
              ·
                rfl

theorem cell19_224034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_224034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224034 prefixEnd_224034 := by exact prefixLift 224034
  have htrace : WordTrace (prefixWord ++ tailWord_224034) baseStart_224034 baseEnd_224034 := by
    simpa [prefixWord, tailWord_224034, baseEnd_224034] using wordTrace_append hprefix tailTrace_224034
  have hstable : (prefixWord ++ tailWord_224034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224034).length < 2 ^ (prefixWord ++ tailWord_224034).sum := by decide
  have hdescent : baseEnd_224034 < baseStart_224034 := by decide
  rcases family_descends (prefixWord ++ tailWord_224034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224055 : List Nat := [1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_224055 : Nat := 118140960795 + 224055 * 2 ^ 59
def prefixEnd_224055 : Nat := 4983230072969 + 3 ^ 40 * 224055 * 2
def baseEnd_224055 : Nat := 68176538099689551100501

theorem tailTrace_224055 : CollatzResearch.WordTrace tailWord_224055 prefixEnd_224055 68176538099689551100501 := by
  unfold tailWord_224055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8171957203294475392633619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5447971468862983595089079 8171957203294475392633619)
  ·
    refine ⟨12257935804941713088950429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8171957203294475392633619 12257935804941713088950429)
    ·
      refine ⟨4596725926853142408356411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12257935804941713088950429 4596725926853142408356411)
      ·
        refine ⟨6895088890279713612534617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596725926853142408356411 6895088890279713612534617)
        ·
          refine ⟨5171316667709785209400963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6895088890279713612534617 5171316667709785209400963)
          ·
            refine ⟨7756975001564677814101445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171316667709785209400963 7756975001564677814101445)
            ·
              refine ⟨1454432812793377090144021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7756975001564677814101445 1454432812793377090144021)
              ·
                refine ⟨68176538099689551100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454432812793377090144021 68176538099689551100501)
                ·
                  rfl

theorem cell19_224055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_224055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224055 prefixEnd_224055 := by exact prefixLift 224055
  have htrace : WordTrace (prefixWord ++ tailWord_224055) baseStart_224055 baseEnd_224055 := by
    simpa [prefixWord, tailWord_224055, baseEnd_224055] using wordTrace_append hprefix tailTrace_224055
  have hstable : (prefixWord ++ tailWord_224055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224055).length < 2 ^ (prefixWord ++ tailWord_224055).sum := by decide
  have hdescent : baseEnd_224055 < baseStart_224055 := by decide
  rcases family_descends (prefixWord ++ tailWord_224055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224068 : List Nat := [2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_224068 : Nat := 118140960795 + 224068 * 2 ^ 59
def prefixEnd_224068 : Nat := 4983230072969 + 3 ^ 40 * 224068 * 2
def baseEnd_224068 : Nat := 68180493802509372811577

theorem tailTrace_224068 : CollatzResearch.WordTrace tailWord_224068 prefixEnd_224068 68180493802509372811577 := by
  unfold tailWord_224068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086215676123689306428429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5448287568164919075237905 4086215676123689306428429)
  ·
    refine ⟨1532330878546383489910661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4086215676123689306428429 1532330878546383489910661)
    ·
      refine ⟨287312039727446904358249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1532330878546383489910661 287312039727446904358249)
      ·
        refine ⟨215484029795585178268687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287312039727446904358249 215484029795585178268687)
        ·
          refine ⟨323226044693377767403031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215484029795585178268687 323226044693377767403031)
          ·
            refine ⟨484839067040066651104547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323226044693377767403031 484839067040066651104547)
            ·
              refine ⟨727258600560099976656821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484839067040066651104547 727258600560099976656821)
              ·
                refine ⟨68180493802509372811577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 727258600560099976656821 68180493802509372811577)
                ·
                  rfl

theorem cell19_224068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_224068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224068 prefixEnd_224068 := by exact prefixLift 224068
  have htrace : WordTrace (prefixWord ++ tailWord_224068) baseStart_224068 baseEnd_224068 := by
    simpa [prefixWord, tailWord_224068, baseEnd_224068] using wordTrace_append hprefix tailTrace_224068
  have hstable : (prefixWord ++ tailWord_224068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224068).length < 2 ^ (prefixWord ++ tailWord_224068).sum := by decide
  have hdescent : baseEnd_224068 < baseStart_224068 := by decide
  rcases family_descends (prefixWord ++ tailWord_224068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224112 : List Nat := [2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_224112 : Nat := 118140960795 + 224112 * 2 ^ 59
def prefixEnd_224112 : Nat := 4983230072969 + 3 ^ 40 * 224112 * 2
def baseEnd_224112 : Nat := 68193882335130307833679

theorem tailTrace_224112 : CollatzResearch.WordTrace tailWord_224112 prefixEnd_224112 68193882335130307833679 := by
  unfold tailWord_224112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4087018082043987063729295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5449357442725316084972393 4087018082043987063729295)
  ·
    refine ⟨6130527123065980595593943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4087018082043987063729295 6130527123065980595593943)
    ·
      refine ⟨9195790684598970893390915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6130527123065980595593943 9195790684598970893390915)
      ·
        refine ⟨13793686026898456340086373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195790684598970893390915 13793686026898456340086373)
        ·
          refine ⟨2586316130043460563766195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13793686026898456340086373 2586316130043460563766195)
          ·
            refine ⟨3879474195065190845649293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586316130043460563766195 3879474195065190845649293)
            ·
              refine ⟨1454802823149446567118485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879474195065190845649293 1454802823149446567118485)
              ·
                refine ⟨68193882335130307833679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454802823149446567118485 68193882335130307833679)
                ·
                  rfl

theorem cell19_224112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_224112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224112 prefixEnd_224112 := by exact prefixLift 224112
  have htrace : WordTrace (prefixWord ++ tailWord_224112) baseStart_224112 baseEnd_224112 := by
    simpa [prefixWord, tailWord_224112, baseEnd_224112] using wordTrace_append hprefix tailTrace_224112
  have hstable : (prefixWord ++ tailWord_224112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224112).length < 2 ^ (prefixWord ++ tailWord_224112).sum := by decide
  have hdescent : baseEnd_224112 < baseStart_224112 := by decide
  rcases family_descends (prefixWord ++ tailWord_224112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224131 : List Nat := [1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_224131 : Nat := 118140960795 + 224131 * 2 ^ 59
def prefixEnd_224131 : Nat := 4983230072969 + 3 ^ 40 * 224131 * 2
def baseEnd_224131 : Nat := 68199663746943893411405

theorem tailTrace_224131 : CollatzResearch.WordTrace tailWord_224131 prefixEnd_224131 68199663746943893411405 := by
  unfold tailWord_224131
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174729151019140372400247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5449819434012760248266831 8174729151019140372400247)
  ·
    refine ⟨12262093726528710558600371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8174729151019140372400247 12262093726528710558600371)
    ·
      refine ⟨18393140589793065837900557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262093726528710558600371 18393140589793065837900557)
      ·
        refine ⟨6897427721172399689212709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18393140589793065837900557 6897427721172399689212709)
        ·
          refine ⟨1293267697719824941727383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6897427721172399689212709 1293267697719824941727383)
          ·
            refine ⟨1939901546579737412591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293267697719824941727383 1939901546579737412591075)
            ·
              refine ⟨2909852319869606118886613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939901546579737412591075 2909852319869606118886613)
              ·
                refine ⟨68199663746943893411405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2909852319869606118886613 68199663746943893411405)
                ·
                  rfl

theorem cell19_224131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_224131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224131 prefixEnd_224131 := by exact prefixLift 224131
  have htrace : WordTrace (prefixWord ++ tailWord_224131) baseStart_224131 baseEnd_224131 := by
    simpa [prefixWord, tailWord_224131, baseEnd_224131] using wordTrace_append hprefix tailTrace_224131
  have hstable : (prefixWord ++ tailWord_224131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224131).length < 2 ^ (prefixWord ++ tailWord_224131).sum := by decide
  have hdescent : baseEnd_224131 < baseStart_224131 := by decide
  rcases family_descends (prefixWord ++ tailWord_224131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224146 : List Nat := [3, 2, 3, 2, 3, 6]
def baseStart_224146 : Nat := 118140960795 + 224146 * 2 ^ 59
def prefixEnd_224146 : Nat := 4983230072969 + 3 ^ 40 * 224146 * 2
def baseEnd_224146 : Nat := 7578247557714255897559

theorem tailTrace_224146 : CollatzResearch.WordTrace tailWord_224146 prefixEnd_224146 7578247557714255897559 := by
  unfold tailWord_224146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043819061491199483549073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5450184163976531956130861 2043819061491199483549073)
  ·
    refine ⟨1532864296118399612661805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043819061491199483549073 1532864296118399612661805)
    ·
      refine ⟨574824111044399854748177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1532864296118399612661805 574824111044399854748177)
      ·
        refine ⟨431118083283299891061133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574824111044399854748177 431118083283299891061133)
        ·
          refine ⟨161669281231237459147925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431118083283299891061133 161669281231237459147925)
          ·
            refine ⟨7578247557714255897559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161669281231237459147925 7578247557714255897559)
            ·
              rfl

theorem cell19_224146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_224146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224146 prefixEnd_224146 := by exact prefixLift 224146
  have htrace : WordTrace (prefixWord ++ tailWord_224146) baseStart_224146 baseEnd_224146 := by
    simpa [prefixWord, tailWord_224146, baseEnd_224146] using wordTrace_append hprefix tailTrace_224146
  have hstable : (prefixWord ++ tailWord_224146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224146).length < 2 ^ (prefixWord ++ tailWord_224146).sum := by decide
  have hdescent : baseEnd_224146 < baseStart_224146 := by decide
  rcases family_descends (prefixWord ++ tailWord_224146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224186 : List Nat := [3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_224186 : Nat := 118140960795 + 224186 * 2 ^ 59
def prefixEnd_224186 : Nat := 4983230072969 + 3 ^ 40 * 224186 * 2
def baseEnd_224186 : Nat := 68216399412720062189033

theorem tailTrace_224186 : CollatzResearch.WordTrace tailWord_224186 prefixEnd_224186 68216399412720062189033 := by
  unfold tailWord_224186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044183791454971191413103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5451156777213256510434941 2044183791454971191413103)
  ·
    refine ⟨3066275687182456787119655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2044183791454971191413103 3066275687182456787119655)
    ·
      refine ⟨4599413530773685180679483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066275687182456787119655 4599413530773685180679483)
      ·
        refine ⟨6899120296160527771019225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599413530773685180679483 6899120296160527771019225)
        ·
          refine ⟨5174340222120395828264419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899120296160527771019225 5174340222120395828264419)
          ·
            refine ⟨7761510333180593742396629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174340222120395828264419 7761510333180593742396629)
            ·
              refine ⟨181910398433920165837421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7761510333180593742396629 181910398433920165837421)
              ·
                refine ⟨68216399412720062189033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181910398433920165837421 68216399412720062189033)
                ·
                  rfl

theorem cell19_224186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_224186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224186 prefixEnd_224186 := by exact prefixLift 224186
  have htrace : WordTrace (prefixWord ++ tailWord_224186) baseStart_224186 baseEnd_224186 := by
    simpa [prefixWord, tailWord_224186, baseEnd_224186] using wordTrace_append hprefix tailTrace_224186
  have hstable : (prefixWord ++ tailWord_224186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224186).length < 2 ^ (prefixWord ++ tailWord_224186).sum := by decide
  have hdescent : baseEnd_224186 < baseStart_224186 := by decide
  rcases family_descends (prefixWord ++ tailWord_224186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224207 : List Nat := [1, 1, 2, 1, 1, 7, 6]
def baseStart_224207 : Nat := 118140960795 + 224207 * 2 ^ 59
def prefixEnd_224207 : Nat := 4983230072969 + 3 ^ 40 * 224207 * 2
def baseEnd_224207 : Nat := 22740929798066078574103

theorem tailTrace_224207 : CollatzResearch.WordTrace tailWord_224207 prefixEnd_224207 22740929798066078574103 := by
  unfold tailWord_224207
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177501098743805352166875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5451667399162536901444583 8177501098743805352166875)
  ·
    refine ⟨12266251648115708028250313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8177501098743805352166875 12266251648115708028250313)
    ·
      refine ⟨9199688736086781021187735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12266251648115708028250313 9199688736086781021187735)
      ·
        refine ⟨13799533104130171531781603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199688736086781021187735 13799533104130171531781603)
        ·
          refine ⟨20699299656195257297672405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13799533104130171531781603 20699299656195257297672405)
          ·
            refine ⟨485139835692076342914197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20699299656195257297672405 485139835692076342914197)
            ·
              refine ⟨22740929798066078574103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 485139835692076342914197 22740929798066078574103)
              ·
                rfl

theorem cell19_224207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_224207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224207 prefixEnd_224207 := by exact prefixLift 224207
  have htrace : WordTrace (prefixWord ++ tailWord_224207) baseStart_224207 baseEnd_224207 := by
    simpa [prefixWord, tailWord_224207, baseEnd_224207] using wordTrace_append hprefix tailTrace_224207
  have hstable : (prefixWord ++ tailWord_224207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224207).length < 2 ^ (prefixWord ++ tailWord_224207).sum := by decide
  have hdescent : baseEnd_224207 < baseStart_224207 := by decide
  rcases family_descends (prefixWord ++ tailWord_224207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224241 : List Nat := [1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_224241 : Nat := 118140960795 + 224241 * 2 ^ 59
def prefixEnd_224241 : Nat := 4983230072969 + 3 ^ 40 * 224241 * 2
def baseEnd_224241 : Nat := 68233135078496230966661

theorem tailTrace_224241 : CollatzResearch.WordTrace tailWord_224241 prefixEnd_224241 68233135078496230966661 := by
  unfold tailWord_224241
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178741180620629158904577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5452494120413752772603051 8178741180620629158904577)
  ·
    refine ⟨6134055885465471869178433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8178741180620629158904577 6134055885465471869178433)
    ·
      refine ⟨4600541914099103901883825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6134055885465471869178433 4600541914099103901883825)
      ·
        refine ⟨3450406435574327926412869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600541914099103901883825 3450406435574327926412869)
        ·
          refine ⟨646951206670186486202413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3450406435574327926412869 646951206670186486202413)
          ·
            refine ⟨242606702501319932325905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646951206670186486202413 242606702501319932325905)
            ·
              refine ⟨181955026875989949244429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242606702501319932325905 181955026875989949244429)
              ·
                refine ⟨68233135078496230966661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181955026875989949244429 68233135078496230966661)
                ·
                  rfl

theorem cell19_224241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_224241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224241 prefixEnd_224241 := by exact prefixLift 224241
  have htrace : WordTrace (prefixWord ++ tailWord_224241) baseStart_224241 baseEnd_224241 := by
    simpa [prefixWord, tailWord_224241, baseEnd_224241] using wordTrace_append hprefix tailTrace_224241
  have hstable : (prefixWord ++ tailWord_224241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224241).length < 2 ^ (prefixWord ++ tailWord_224241).sum := by decide
  have hdescent : baseEnd_224241 < baseStart_224241 := by decide
  rcases family_descends (prefixWord ++ tailWord_224241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224258 : List Nat := [3, 4, 1, 3, 1, 2, 5]
def baseStart_224258 : Nat := 118140960795 + 224258 * 2 ^ 59
def prefixEnd_224258 : Nat := 4983230072969 + 3 ^ 40 * 224258 * 2
def baseEnd_224258 : Nat := 22746102640215076196279

theorem tailTrace_224258 : CollatzResearch.WordTrace tailWord_224258 prefixEnd_224258 22746102640215076196279 := by
  unfold tailWord_224258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044840305389760265568357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5452907481039360708182285 2044840305389760265568357)
  ·
    refine ⟨383407557260580049794067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2044840305389760265568357 383407557260580049794067)
    ·
      refine ⟨575111335890870074691101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383407557260580049794067 575111335890870074691101)
      ·
        refine ⟨215666750959076278009163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575111335890870074691101 215666750959076278009163)
        ·
          refine ⟨323500126438614417013745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215666750959076278009163 323500126438614417013745)
          ·
            refine ⟨242625094828960812760309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323500126438614417013745 242625094828960812760309)
            ·
              refine ⟨22746102640215076196279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242625094828960812760309 22746102640215076196279)
              ·
                rfl

theorem cell19_224258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_224258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224258 prefixEnd_224258 := by exact prefixLift 224258
  have htrace : WordTrace (prefixWord ++ tailWord_224258) baseStart_224258 baseEnd_224258 := by
    simpa [prefixWord, tailWord_224258, baseEnd_224258] using wordTrace_append hprefix tailTrace_224258
  have hstable : (prefixWord ++ tailWord_224258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224258).length < 2 ^ (prefixWord ++ tailWord_224258).sum := by decide
  have hdescent : baseEnd_224258 < baseStart_224258 := by decide
  rcases family_descends (prefixWord ++ tailWord_224258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224264 : List Nat := [2, 1, 3, 2, 1, 3, 7]
def baseStart_224264 : Nat := 118140960795 + 224264 * 2 ^ 59
def prefixEnd_224264 : Nat := 4983230072969 + 3 ^ 40 * 224264 * 2
def baseEnd_224264 : Nat := 22746711209879664151829

theorem tailTrace_224264 : CollatzResearch.WordTrace tailWord_224264 prefixEnd_224264 22746711209879664151829 := by
  unfold tailWord_224264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089790029768652043495923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5453053373024869391327897 4089790029768652043495923)
  ·
    refine ⟨6134685044652978065243885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089790029768652043495923 6134685044652978065243885)
    ·
      refine ⟨2300506891744866774466457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6134685044652978065243885 2300506891744866774466457)
      ·
        refine ⟨1725380168808650080849843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300506891744866774466457 1725380168808650080849843)
        ·
          refine ⟨2588070253212975121274765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725380168808650080849843 2588070253212975121274765)
          ·
            refine ⟨970526344954865670478037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2588070253212975121274765 970526344954865670478037)
            ·
              refine ⟨22746711209879664151829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 970526344954865670478037 22746711209879664151829)
              ·
                rfl

theorem cell19_224264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_224264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224264 prefixEnd_224264 := by exact prefixLift 224264
  have htrace : WordTrace (prefixWord ++ tailWord_224264) baseStart_224264 baseEnd_224264 := by
    simpa [prefixWord, tailWord_224264, baseEnd_224264] using wordTrace_append hprefix tailTrace_224264
  have hstable : (prefixWord ++ tailWord_224264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224264).length < 2 ^ (prefixWord ++ tailWord_224264).sum := by decide
  have hdescent : baseEnd_224264 < baseStart_224264 := by decide
  rcases family_descends (prefixWord ++ tailWord_224264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224321 : List Nat := [1, 2, 5, 1, 10]
def baseStart_224321 : Nat := 118140960795 + 224321 * 2 ^ 59
def prefixEnd_224321 : Nat := 4983230072969 + 3 ^ 40 * 224321 * 2
def baseEnd_224321 : Nat := 2528054735743694414395

theorem tailTrace_224321 : CollatzResearch.WordTrace tailWord_224321 prefixEnd_224321 2528054735743694414395 := by
  unfold tailWord_224321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181659020330802821816817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5454439346887201881211211 8181659020330802821816817)
  ·
    refine ⟨6136244265248102116362613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8181659020330802821816817 6136244265248102116362613)
    ·
      refine ⟨575272899867009573408995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6136244265248102116362613 575272899867009573408995)
      ·
        refine ⟨862909349800514360113493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575272899867009573408995 862909349800514360113493)
        ·
          refine ⟨2528054735743694414395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 862909349800514360113493 2528054735743694414395)
          ·
            rfl

theorem cell19_224321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_224321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224321 prefixEnd_224321 := by exact prefixLift 224321
  have htrace : WordTrace (prefixWord ++ tailWord_224321) baseStart_224321 baseEnd_224321 := by
    simpa [prefixWord, tailWord_224321, baseEnd_224321] using wordTrace_append hprefix tailTrace_224321
  have hstable : (prefixWord ++ tailWord_224321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224321).length < 2 ^ (prefixWord ++ tailWord_224321).sum := by decide
  have hdescent : baseEnd_224321 < baseStart_224321 := by decide
  rcases family_descends (prefixWord ++ tailWord_224321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224338 : List Nat := [3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_224338 : Nat := 118140960795 + 224338 * 2 ^ 59
def prefixEnd_224338 : Nat := 4983230072969 + 3 ^ 40 * 224338 * 2
def baseEnd_224338 : Nat := 68262650707228746810841

theorem tailTrace_224338 : CollatzResearch.WordTrace tailWord_224338 prefixEnd_224338 68262650707228746810841 := by
  unfold tailWord_224338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045569765317303681296417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5454852707512809816790445 2045569765317303681296417)
  ·
    refine ⟨1534177323987977760972313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2045569765317303681296417 1534177323987977760972313)
    ·
      refine ⟨1150632992990983320729235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1534177323987977760972313 1150632992990983320729235)
      ·
        refine ⟨1725949489486474981093853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150632992990983320729235 1725949489486474981093853)
        ·
          refine ⟨647231058557428117910195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1725949489486474981093853 647231058557428117910195)
          ·
            refine ⟨970846587836142176865293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647231058557428117910195 970846587836142176865293)
            ·
              refine ⟨364067470438553316324485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970846587836142176865293 364067470438553316324485)
              ·
                refine ⟨68262650707228746810841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364067470438553316324485 68262650707228746810841)
                ·
                  rfl

theorem cell19_224338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_224338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224338 prefixEnd_224338 := by exact prefixLift 224338
  have htrace : WordTrace (prefixWord ++ tailWord_224338) baseStart_224338 baseEnd_224338 := by
    simpa [prefixWord, tailWord_224338, baseEnd_224338] using wordTrace_append hprefix tailTrace_224338
  have hstable : (prefixWord ++ tailWord_224338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224338).length < 2 ^ (prefixWord ++ tailWord_224338).sum := by decide
  have hdescent : baseEnd_224338 < baseStart_224338 := by decide
  rcases family_descends (prefixWord ++ tailWord_224338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224357 : List Nat := [1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_224357 : Nat := 118140960795 + 224357 * 2 ^ 59
def prefixEnd_224357 : Nat := 4983230072969 + 3 ^ 40 * 224357 * 2
def baseEnd_224357 : Nat := 68268432119042332388567

theorem tailTrace_224357 : CollatzResearch.WordTrace tailWord_224357 prefixEnd_224357 68268432119042332388567 := by
  unfold tailWord_224357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182972048200380970127325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5455314698800253980084883 8182972048200380970127325)
  ·
    refine ⟨3068614518075142863797747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8182972048200380970127325 3068614518075142863797747)
    ·
      refine ⟨4602921777112714295696621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068614518075142863797747 4602921777112714295696621)
      ·
        refine ⟨1726095666417267860886233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4602921777112714295696621 1726095666417267860886233)
        ·
          refine ⟨1294571749812950895664675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726095666417267860886233 1294571749812950895664675)
          ·
            refine ⟨1941857624719426343497013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294571749812950895664675 1941857624719426343497013)
            ·
              refine ⟨182049152317446219702845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1941857624719426343497013 182049152317446219702845)
              ·
                refine ⟨68268432119042332388567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182049152317446219702845 68268432119042332388567)
                ·
                  rfl

theorem cell19_224357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_224357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224357 prefixEnd_224357 := by exact prefixLift 224357
  have htrace : WordTrace (prefixWord ++ tailWord_224357) baseStart_224357 baseEnd_224357 := by
    simpa [prefixWord, tailWord_224357, baseEnd_224357] using wordTrace_append hprefix tailTrace_224357
  have hstable : (prefixWord ++ tailWord_224357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224357).length < 2 ^ (prefixWord ++ tailWord_224357).sum := by decide
  have hdescent : baseEnd_224357 < baseStart_224357 := by decide
  rcases family_descends (prefixWord ++ tailWord_224357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224412 : List Nat := [2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_224412 : Nat := 118140960795 + 224412 * 2 ^ 59
def prefixEnd_224412 : Nat := 4983230072969 + 3 ^ 40 * 224412 * 2
def baseEnd_224412 : Nat := 68285167784818501166195

theorem tailTrace_224412 : CollatzResearch.WordTrace tailWord_224412 prefixEnd_224412 68285167784818501166195 := by
  unfold tailWord_224412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092489031500562681689745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5456652042000750242252993 4092489031500562681689745)
  ·
    refine ⟨3069366773625422011267309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092489031500562681689745 3069366773625422011267309)
    ·
      refine ⟨1151012540109533254225241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3069366773625422011267309 1151012540109533254225241)
      ·
        refine ⟨863259405082149940668931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151012540109533254225241 863259405082149940668931)
        ·
          refine ⟨1294889107623224911003397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863259405082149940668931 1294889107623224911003397)
          ·
            refine ⟨242791707679354670813137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1294889107623224911003397 242791707679354670813137)
            ·
              refine ⟨182093780759516003109853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242791707679354670813137 182093780759516003109853)
              ·
                refine ⟨68285167784818501166195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182093780759516003109853 68285167784818501166195)
                ·
                  rfl

theorem cell19_224412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_224412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224412 prefixEnd_224412 := by exact prefixLift 224412
  have htrace : WordTrace (prefixWord ++ tailWord_224412) baseStart_224412 baseEnd_224412 := by
    simpa [prefixWord, tailWord_224412, baseEnd_224412] using wordTrace_append hprefix tailTrace_224412
  have hstable : (prefixWord ++ tailWord_224412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224412).length < 2 ^ (prefixWord ++ tailWord_224412).sum := by decide
  have hdescent : baseEnd_224412 < baseStart_224412 := by decide
  rcases family_descends (prefixWord ++ tailWord_224412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224416 : List Nat := [2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_224416 : Nat := 118140960795 + 224416 * 2 ^ 59
def prefixEnd_224416 : Nat := 4983230072969 + 3 ^ 40 * 224416 * 2
def baseEnd_224416 : Nat := 68286384924147677077295

theorem tailTrace_224416 : CollatzResearch.WordTrace tailWord_224416 prefixEnd_224416 68286384924147677077295 := by
  unfold tailWord_224416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092561977493317023262551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5456749303324422697683401 4092561977493317023262551)
  ·
    refine ⟨6138842966239975534893827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4092561977493317023262551 6138842966239975534893827)
    ·
      refine ⟨9208264449359963302340741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138842966239975534893827 9208264449359963302340741)
      ·
        refine ⟨1726549584254993119188889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9208264449359963302340741 1726549584254993119188889)
        ·
          refine ⟨1294912188191244839391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1726549584254993119188889 1294912188191244839391667)
          ·
            refine ⟨1942368282286867259087501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294912188191244839391667 1942368282286867259087501)
            ·
              refine ⟨728388105857575222157813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942368282286867259087501 728388105857575222157813)
              ·
                refine ⟨68286384924147677077295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 728388105857575222157813 68286384924147677077295)
                ·
                  rfl

theorem cell19_224416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_224416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224416 prefixEnd_224416 := by exact prefixLift 224416
  have htrace : WordTrace (prefixWord ++ tailWord_224416) baseStart_224416 baseEnd_224416 := by
    simpa [prefixWord, tailWord_224416, baseEnd_224416] using wordTrace_append hprefix tailTrace_224416
  have hstable : (prefixWord ++ tailWord_224416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224416).length < 2 ^ (prefixWord ++ tailWord_224416).sum := by decide
  have hdescent : baseEnd_224416 < baseStart_224416 := by decide
  rcases family_descends (prefixWord ++ tailWord_224416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224433 : List Nat := [1, 2, 2, 5, 1, 3, 5]
def baseStart_224433 : Nat := 118140960795 + 224433 * 2 ^ 59
def prefixEnd_224433 : Nat := 4983230072969 + 3 ^ 40 * 224433 * 2
def baseEnd_224433 : Nat := 22763852588765558233157

theorem tailTrace_224433 : CollatzResearch.WordTrace tailWord_224433 prefixEnd_224433 22763852588765558233157 := by
  unfold tailWord_224433
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185743995925045949893953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5457162663950030633262635 8185743995925045949893953)
  ·
    refine ⟨6139307996943784462420465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8185743995925045949893953 6139307996943784462420465)
    ·
      refine ⟨4604480997707838346815349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139307996943784462420465 4604480997707838346815349)
      ·
        refine ⟨431670093535109845013939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4604480997707838346815349 431670093535109845013939)
        ·
          refine ⟨647505140302664767520909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431670093535109845013939 647505140302664767520909)
          ·
            refine ⟨242814427613499287820341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647505140302664767520909 242814427613499287820341)
            ·
              refine ⟨22763852588765558233157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242814427613499287820341 22763852588765558233157)
              ·
                rfl

theorem cell19_224433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_224433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224433 prefixEnd_224433 := by exact prefixLift 224433
  have htrace : WordTrace (prefixWord ++ tailWord_224433) baseStart_224433 baseEnd_224433 := by
    simpa [prefixWord, tailWord_224433, baseEnd_224433] using wordTrace_append hprefix tailTrace_224433
  have hstable : (prefixWord ++ tailWord_224433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224433).length < 2 ^ (prefixWord ++ tailWord_224433).sum := by decide
  have hdescent : baseEnd_224433 < baseStart_224433 := by decide
  rcases family_descends (prefixWord ++ tailWord_224433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224511 : List Nat := [1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_224511 : Nat := 118140960795 + 224511 * 2 ^ 59
def prefixEnd_224511 : Nat := 4983230072969 + 3 ^ 40 * 224511 * 2
def baseEnd_224511 : Nat := 68315291983215604965925

theorem tailTrace_224511 : CollatzResearch.WordTrace tailWord_224511 prefixEnd_224511 68315291983215604965925 := by
  unfold tailWord_224511
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188588889642465271233387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459059259761643514155591 8188588889642465271233387)
  ·
    refine ⟨12282883334463697906850081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188588889642465271233387 12282883334463697906850081)
    ·
      refine ⟨9212162500847773430137561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282883334463697906850081 9212162500847773430137561)
      ·
        refine ⟨6909121875635830072603171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9212162500847773430137561 6909121875635830072603171)
        ·
          refine ⟨10363682813453745108904757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909121875635830072603171 10363682813453745108904757)
          ·
            refine ⟨971595263761288603959821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10363682813453745108904757 971595263761288603959821)
            ·
              refine ⟨364348223910483226484933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971595263761288603959821 364348223910483226484933)
              ·
                refine ⟨68315291983215604965925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364348223910483226484933 68315291983215604965925)
                ·
                  rfl

theorem cell19_224511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_224511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224511 prefixEnd_224511 := by exact prefixLift 224511
  have htrace : WordTrace (prefixWord ++ tailWord_224511) baseStart_224511 baseEnd_224511 := by
    simpa [prefixWord, tailWord_224511, baseEnd_224511] using wordTrace_append hprefix tailTrace_224511
  have hstable : (prefixWord ++ tailWord_224511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224511).length < 2 ^ (prefixWord ++ tailWord_224511).sum := by decide
  have hdescent : baseEnd_224511 < baseStart_224511 := by decide
  rcases family_descends (prefixWord ++ tailWord_224511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224549 : List Nat := [1, 3, 1, 2, 4, 2, 6]
def baseStart_224549 : Nat := 118140960795 + 224549 * 2 ^ 59
def prefixEnd_224549 : Nat := 4983230072969 + 3 ^ 40 * 224549 * 2
def baseEnd_224549 : Nat := 22775618268947592040459

theorem tailTrace_224549 : CollatzResearch.WordTrace tailWord_224549 prefixEnd_224549 22775618268947592040459 := by
  unfold tailWord_224549
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189974863504797761116701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459983242336531840744467 8189974863504797761116701)
  ·
    refine ⟨3071240573814299160418763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8189974863504797761116701 3071240573814299160418763)
    ·
      refine ⟨4606860860721448740628145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071240573814299160418763 4606860860721448740628145)
      ·
        refine ⟨3455145645541086555471109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606860860721448740628145 3455145645541086555471109)
        ·
          refine ⟨647839808538953729150833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3455145645541086555471109 647839808538953729150833)
          ·
            refine ⟨485879856404215296863125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647839808538953729150833 485879856404215296863125)
            ·
              refine ⟨22775618268947592040459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 485879856404215296863125 22775618268947592040459)
              ·
                rfl

theorem cell19_224549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_224549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224549 prefixEnd_224549 := by exact prefixLift 224549
  have htrace : WordTrace (prefixWord ++ tailWord_224549) baseStart_224549 baseEnd_224549 := by
    simpa [prefixWord, tailWord_224549, baseEnd_224549] using wordTrace_append hprefix tailTrace_224549
  have hstable : (prefixWord ++ tailWord_224549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224549).length < 2 ^ (prefixWord ++ tailWord_224549).sum := by decide
  have hdescent : baseEnd_224549 < baseStart_224549 := by decide
  rcases family_descends (prefixWord ++ tailWord_224549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224598 : List Nat := [5, 2, 3, 1, 1, 2, 5]
def baseStart_224598 : Nat := 118140960795 + 224598 * 2 ^ 59
def prefixEnd_224598 : Nat := 4983230072969 + 3 ^ 40 * 224598 * 2
def baseEnd_224598 : Nat := 22780588254541727010785

theorem tailTrace_224598 : CollatzResearch.WordTrace tailWord_224598 prefixEnd_224598 22780588254541727010785 := by
  unfold tailWord_224598
  simp only [CollatzResearch.WordTrace]
  refine ⟨511985127520454945603153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5461174693551519419766965 511985127520454945603153)
  ·
    refine ⟨383988845640341209202365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 511985127520454945603153 383988845640341209202365)
    ·
      refine ⟨143995817115127953450887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383988845640341209202365 143995817115127953450887)
      ·
        refine ⟨215993725672691930176331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143995817115127953450887 215993725672691930176331)
        ·
          refine ⟨323990588509037895264497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215993725672691930176331 323990588509037895264497)
          ·
            refine ⟨242992941381778421448373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323990588509037895264497 242992941381778421448373)
            ·
              refine ⟨22780588254541727010785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242992941381778421448373 22780588254541727010785)
              ·
                rfl

theorem cell19_224598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_224598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224598 prefixEnd_224598 := by exact prefixLift 224598
  have htrace : WordTrace (prefixWord ++ tailWord_224598) baseStart_224598 baseEnd_224598 := by
    simpa [prefixWord, tailWord_224598, baseEnd_224598] using wordTrace_append hprefix tailTrace_224598
  have hstable : (prefixWord ++ tailWord_224598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224598).length < 2 ^ (prefixWord ++ tailWord_224598).sum := by decide
  have hdescent : baseEnd_224598 < baseStart_224598 := by decide
  rcases family_descends (prefixWord ++ tailWord_224598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224644 : List Nat := [2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_224644 : Nat := 118140960795 + 224644 * 2 ^ 59
def prefixEnd_224644 : Nat := 4983230072969 + 3 ^ 40 * 224644 * 2
def baseEnd_224644 : Nat := 68355761865910704010007

theorem tailTrace_224644 : CollatzResearch.WordTrace tailWord_224644 prefixEnd_224644 68355761865910704010007 := by
  unfold tailWord_224644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096719899080314492912493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5462293198773752657216657 4096719899080314492912493)
  ·
    refine ⟨1536269962155117934842185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4096719899080314492912493 1536269962155117934842185)
    ·
      refine ⟨1152202471616338451131639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1536269962155117934842185 1152202471616338451131639)
      ·
        refine ⟨1728303707424507676697459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152202471616338451131639 1728303707424507676697459)
        ·
          refine ⟨2592455561136761515046189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728303707424507676697459 2592455561136761515046189)
          ·
            refine ⟨972170835426285568142321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2592455561136761515046189 972170835426285568142321)
            ·
              refine ⟨729128126569714176106741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972170835426285568142321 729128126569714176106741)
              ·
                refine ⟨68355761865910704010007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 729128126569714176106741 68355761865910704010007)
                ·
                  rfl

theorem cell19_224644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_224644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224644 prefixEnd_224644 := by exact prefixLift 224644
  have htrace : WordTrace (prefixWord ++ tailWord_224644) baseStart_224644 baseEnd_224644 := by
    simpa [prefixWord, tailWord_224644, baseEnd_224644] using wordTrace_append hprefix tailTrace_224644
  have hstable : (prefixWord ++ tailWord_224644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224644).length < 2 ^ (prefixWord ++ tailWord_224644).sum := by decide
  have hdescent : baseEnd_224644 < baseStart_224644 := by decide
  rcases family_descends (prefixWord ++ tailWord_224644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224665 : List Nat := [1, 2, 1, 2, 1, 12]
def baseStart_224665 : Nat := 118140960795 + 224665 * 2 ^ 59
def prefixEnd_224665 : Nat := 4983230072969 + 3 ^ 40 * 224665 * 2
def baseEnd_224665 : Nat := 7595794649709875282587

theorem tailTrace_224665 : CollatzResearch.WordTrace tailWord_224665 prefixEnd_224665 7595794649709875282587 := by
  unfold tailWord_224665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194205731084549572339449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5462803820723033048226299 8194205731084549572339449)
  ·
    refine ⟨6145654298313412179254587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8194205731084549572339449 6145654298313412179254587)
    ·
      refine ⟨9218481447470118268881881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145654298313412179254587 9218481447470118268881881)
      ·
        refine ⟨6913861085602588701661411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9218481447470118268881881 6913861085602588701661411)
        ·
          refine ⟨10370791628403883052492117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913861085602588701661411 10370791628403883052492117)
          ·
            refine ⟨7595794649709875282587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10370791628403883052492117 7595794649709875282587)
            ·
              rfl

theorem cell19_224665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_224665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224665 prefixEnd_224665 := by exact prefixLift 224665
  have htrace : WordTrace (prefixWord ++ tailWord_224665) baseStart_224665 baseEnd_224665 := by
    simpa [prefixWord, tailWord_224665, baseEnd_224665] using wordTrace_append hprefix tailTrace_224665
  have hstable : (prefixWord ++ tailWord_224665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224665).length < 2 ^ (prefixWord ++ tailWord_224665).sum := by decide
  have hdescent : baseEnd_224665 < baseStart_224665 := by decide
  rcases family_descends (prefixWord ++ tailWord_224665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224703 : List Nat := [1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_224703 : Nat := 118140960795 + 224703 * 2 ^ 59
def prefixEnd_224703 : Nat := 4983230072969 + 3 ^ 40 * 224703 * 2
def baseEnd_224703 : Nat := 68373714671016048698735

theorem tailTrace_224703 : CollatzResearch.WordTrace tailWord_224703 prefixEnd_224703 68373714671016048698735 := by
  unfold tailWord_224703
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195591704946882062222763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5463727803297921374815175 8195591704946882062222763)
  ·
    refine ⟨12293387557420323093334145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195591704946882062222763 12293387557420323093334145)
    ·
      refine ⟨9220040668065242320000609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12293387557420323093334145 9220040668065242320000609)
      ·
        refine ⟨6915030501048931740000457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220040668065242320000609 6915030501048931740000457)
        ·
          refine ⟨5186272875786698805000343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915030501048931740000457 5186272875786698805000343)
          ·
            refine ⟨7779409313680048207500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186272875786698805000343 7779409313680048207500515)
            ·
              refine ⟨11669113970520072311250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779409313680048207500515 11669113970520072311250773)
              ·
                refine ⟨68373714671016048698735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11669113970520072311250773 68373714671016048698735)
                ·
                  rfl

theorem cell19_224703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_224703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224703 prefixEnd_224703 := by exact prefixLift 224703
  have htrace : WordTrace (prefixWord ++ tailWord_224703) baseStart_224703 baseEnd_224703 := by
    simpa [prefixWord, tailWord_224703, baseEnd_224703] using wordTrace_append hprefix tailTrace_224703
  have hstable : (prefixWord ++ tailWord_224703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224703).length < 2 ^ (prefixWord ++ tailWord_224703).sum := by decide
  have hdescent : baseEnd_224703 < baseStart_224703 := by decide
  rcases family_descends (prefixWord ++ tailWord_224703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224754 : List Nat := [3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_224754 : Nat := 118140960795 + 224754 * 2 ^ 59
def prefixEnd_224754 : Nat := 4983230072969 + 3 ^ 40 * 224754 * 2
def baseEnd_224754 : Nat := 68389233197463041565263

theorem tailTrace_224754 : CollatzResearch.WordTrace tailWord_224754 prefixEnd_224754 68389233197463041565263 := by
  unfold tailWord_224754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049362956940529443082329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5464967885174745181552877 2049362956940529443082329)
  ·
    refine ⟨1537022217705397082311747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2049362956940529443082329 1537022217705397082311747)
    ·
      refine ⟨2305533326558095623467621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537022217705397082311747 2305533326558095623467621)
      ·
        refine ⟨432287498729642929400179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2305533326558095623467621 432287498729642929400179)
        ·
          refine ⟨648431248094464394100269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432287498729642929400179 648431248094464394100269)
          ·
            refine ⟨243161718035424147787601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 648431248094464394100269 243161718035424147787601)
            ·
              refine ⟨182371288526568110840701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243161718035424147787601 182371288526568110840701)
              ·
                refine ⟨68389233197463041565263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182371288526568110840701 68389233197463041565263)
                ·
                  rfl

theorem cell19_224754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_224754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224754 prefixEnd_224754 := by exact prefixLift 224754
  have htrace : WordTrace (prefixWord ++ tailWord_224754) baseStart_224754 baseEnd_224754 := by
    simpa [prefixWord, tailWord_224754, baseEnd_224754] using wordTrace_append hprefix tailTrace_224754
  have hstable : (prefixWord ++ tailWord_224754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224754).length < 2 ^ (prefixWord ++ tailWord_224754).sum := by decide
  have hdescent : baseEnd_224754 < baseStart_224754 := by decide
  rcases family_descends (prefixWord ++ tailWord_224754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224796 : List Nat := [2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_224796 : Nat := 118140960795 + 224796 * 2 ^ 59
def prefixEnd_224796 : Nat := 4983230072969 + 3 ^ 40 * 224796 * 2
def baseEnd_224796 : Nat := 68402013160419388631815

theorem tailTrace_224796 : CollatzResearch.WordTrace tailWord_224796 prefixEnd_224796 68402013160419388631815 := by
  unfold tailWord_224796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099491846804979472679121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5465989129073305963572161 4099491846804979472679121)
  ·
    refine ⟨3074618885103734604509341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4099491846804979472679121 3074618885103734604509341)
    ·
      refine ⟨1152982081913900476691003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3074618885103734604509341 1152982081913900476691003)
      ·
        refine ⟨1729473122870850715036505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152982081913900476691003 1729473122870850715036505)
        ·
          refine ⟨1297104842153138036277379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729473122870850715036505 1297104842153138036277379)
          ·
            refine ⟨1945657263229707054416069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297104842153138036277379 1945657263229707054416069)
            ·
              refine ⟨364810736855570072703013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1945657263229707054416069 364810736855570072703013)
              ·
                refine ⟨68402013160419388631815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364810736855570072703013 68402013160419388631815)
                ·
                  rfl

theorem cell19_224796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_224796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224796 prefixEnd_224796 := by exact prefixLift 224796
  have htrace : WordTrace (prefixWord ++ tailWord_224796) baseStart_224796 baseEnd_224796 := by
    simpa [prefixWord, tailWord_224796, baseEnd_224796] using wordTrace_append hprefix tailTrace_224796
  have hstable : (prefixWord ++ tailWord_224796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224796).length < 2 ^ (prefixWord ++ tailWord_224796).sum := by decide
  have hdescent : baseEnd_224796 < baseStart_224796 := by decide
  rcases family_descends (prefixWord ++ tailWord_224796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224927 : List Nat := [1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_224927 : Nat := 118140960795 + 224927 * 2 ^ 59
def prefixEnd_224927 : Nat := 4983230072969 + 3 ^ 40 * 224927 * 2
def baseEnd_224927 : Nat := 68441874473449899720347

theorem tailTrace_224927 : CollatzResearch.WordTrace tailWord_224927 prefixEnd_224927 68441874473449899720347 := by
  unfold tailWord_224927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203761656135368318377035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5469174437423578878918023 8203761656135368318377035)
  ·
    refine ⟨12305642484203052477565553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8203761656135368318377035 12305642484203052477565553)
    ·
      refine ⟨9229231863152289358174165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12305642484203052477565553 9229231863152289358174165)
      ·
        refine ⟨216310121792631781832207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9229231863152289358174165 216310121792631781832207)
        ·
          refine ⟨324465182688947672748311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216310121792631781832207 324465182688947672748311)
          ·
            refine ⟨486697774033421509122467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324465182688947672748311 486697774033421509122467)
            ·
              refine ⟨730046661050132263683701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486697774033421509122467 730046661050132263683701)
              ·
                refine ⟨68441874473449899720347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730046661050132263683701 68441874473449899720347)
                ·
                  rfl

theorem cell19_224927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_224927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224927 prefixEnd_224927 := by exact prefixLift 224927
  have htrace : WordTrace (prefixWord ++ tailWord_224927) baseStart_224927 baseEnd_224927 := by
    simpa [prefixWord, tailWord_224927, baseEnd_224927] using wordTrace_append hprefix tailTrace_224927
  have hstable : (prefixWord ++ tailWord_224927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224927).length < 2 ^ (prefixWord ++ tailWord_224927).sum := by decide
  have hdescent : baseEnd_224927 < baseStart_224927 := by decide
  rcases family_descends (prefixWord ++ tailWord_224927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224929 : List Nat := [1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_224929 : Nat := 118140960795 + 224929 * 2 ^ 59
def prefixEnd_224929 : Nat := 4983230072969 + 3 ^ 40 * 224929 * 2
def baseEnd_224929 : Nat := 68442483043114487675897

theorem tailTrace_224929 : CollatzResearch.WordTrace tailWord_224929 prefixEnd_224929 68442483043114487675897 := by
  unfold tailWord_224929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203834602128122659949841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5469223068085415106633227 8203834602128122659949841)
  ·
    refine ⟨6152875951596091994962381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8203834602128122659949841 6152875951596091994962381)
    ·
      refine ⟨2307328481848534498110893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6152875951596091994962381 2307328481848534498110893)
      ·
        refine ⟨865248180693200436791585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2307328481848534498110893 865248180693200436791585)
        ·
          refine ⟨648936135519900327593689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865248180693200436791585 648936135519900327593689)
          ·
            refine ⟨486702101639925245695267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648936135519900327593689 486702101639925245695267)
            ·
              refine ⟨730053152459887868542901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486702101639925245695267 730053152459887868542901)
              ·
                refine ⟨68442483043114487675897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730053152459887868542901 68442483043114487675897)
                ·
                  rfl

theorem cell19_224929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_224929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224929 prefixEnd_224929 := by exact prefixLift 224929
  have htrace : WordTrace (prefixWord ++ tailWord_224929) baseStart_224929 baseEnd_224929 := by
    simpa [prefixWord, tailWord_224929, baseEnd_224929] using wordTrace_append hprefix tailTrace_224929
  have hstable : (prefixWord ++ tailWord_224929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224929).length < 2 ^ (prefixWord ++ tailWord_224929).sum := by decide
  have hdescent : baseEnd_224929 < baseStart_224929 := by decide
  rcases family_descends (prefixWord ++ tailWord_224929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224931 : List Nat := [1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_224931 : Nat := 118140960795 + 224931 * 2 ^ 59
def prefixEnd_224931 : Nat := 4983230072969 + 3 ^ 40 * 224931 * 2
def baseEnd_224931 : Nat := 68443091612779075631447

theorem tailTrace_224931 : CollatzResearch.WordTrace tailWord_224931 prefixEnd_224931 68443091612779075631447 := by
  unfold tailWord_224931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203907548120877001522647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5469271698747251334348431 8203907548120877001522647)
  ·
    refine ⟨12305861322181315502283971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8203907548120877001522647 12305861322181315502283971)
    ·
      refine ⟨18458791983271973253425957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12305861322181315502283971 18458791983271973253425957)
      ·
        refine ⟨3461023496863494985017367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18458791983271973253425957 3461023496863494985017367)
        ·
          refine ⟨5191535245295242477526051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461023496863494985017367 5191535245295242477526051)
          ·
            refine ⟨7787302867942863716289077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191535245295242477526051 7787302867942863716289077)
            ·
              refine ⟨730059643869643473402101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7787302867942863716289077 730059643869643473402101)
              ·
                refine ⟨68443091612779075631447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730059643869643473402101 68443091612779075631447)
                ·
                  rfl

theorem cell19_224931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_224931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_224931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_224931 prefixEnd_224931 := by exact prefixLift 224931
  have htrace : WordTrace (prefixWord ++ tailWord_224931) baseStart_224931 baseEnd_224931 := by
    simpa [prefixWord, tailWord_224931, baseEnd_224931] using wordTrace_append hprefix tailTrace_224931
  have hstable : (prefixWord ++ tailWord_224931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224931).length < 2 ^ (prefixWord ++ tailWord_224931).sum := by decide
  have hdescent : baseEnd_224931 < baseStart_224931 := by decide
  rcases family_descends (prefixWord ++ tailWord_224931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225094 : List Nat := [6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_225094 : Nat := 118140960795 + 225094 * 2 ^ 59
def prefixEnd_225094 : Nat := 4983230072969 + 3 ^ 40 * 225094 * 2
def baseEnd_225094 : Nat := 68492690040442994008781

theorem tailTrace_225094 : CollatzResearch.WordTrace tailWord_225094 prefixEnd_225094 68492690040442994008781 := by
  unfold tailWord_225094
  simp only [CollatzResearch.WordTrace]
  refine ⟨256557895204073619990823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5473235097686903893137557 256557895204073619990823)
  ·
    refine ⟨384836842806110429986235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256557895204073619990823 384836842806110429986235)
    ·
      refine ⟨577255264209165644979353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384836842806110429986235 577255264209165644979353)
      ·
        refine ⟨432941448156874233734515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577255264209165644979353 432941448156874233734515)
        ·
          refine ⟨649412172235311350601773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432941448156874233734515 649412172235311350601773)
          ·
            refine ⟨243529564588241756475665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649412172235311350601773 243529564588241756475665)
            ·
              refine ⟨182647173441181317356749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243529564588241756475665 182647173441181317356749)
              ·
                refine ⟨68492690040442994008781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182647173441181317356749 68492690040442994008781)
                ·
                  rfl

theorem cell19_225094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_225094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225094 prefixEnd_225094 := by exact prefixLift 225094
  have htrace : WordTrace (prefixWord ++ tailWord_225094) baseStart_225094 baseEnd_225094 := by
    simpa [prefixWord, tailWord_225094, baseEnd_225094] using wordTrace_append hprefix tailTrace_225094
  have hstable : (prefixWord ++ tailWord_225094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225094).length < 2 ^ (prefixWord ++ tailWord_225094).sum := by decide
  have hdescent : baseEnd_225094 < baseStart_225094 := by decide
  rcases family_descends (prefixWord ++ tailWord_225094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225100 : List Nat := [2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_225100 : Nat := 118140960795 + 225100 * 2 ^ 59
def prefixEnd_225100 : Nat := 4983230072969 + 3 ^ 40 * 225100 * 2
def baseEnd_225100 : Nat := 68494515749436757875431

theorem tailTrace_225100 : CollatzResearch.WordTrace tailWord_225100 prefixEnd_225100 68494515749436757875431 := by
  unfold tailWord_225100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105035742254309432212377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5473380989672412576283169 4105035742254309432212377)
  ·
    refine ⟨3078776806690732074159283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4105035742254309432212377 3078776806690732074159283)
    ·
      refine ⟨4618165210036098111238925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078776806690732074159283 4618165210036098111238925)
      ·
        refine ⟨1731811953763536791714597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4618165210036098111238925 1731811953763536791714597)
        ·
          refine ⟨324714741330663148446487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1731811953763536791714597 324714741330663148446487)
          ·
            refine ⟨487072111995994722669731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324714741330663148446487 487072111995994722669731)
            ·
              refine ⟨730608167993992084004597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487072111995994722669731 730608167993992084004597)
              ·
                refine ⟨68494515749436757875431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 730608167993992084004597 68494515749436757875431)
                ·
                  rfl

theorem cell19_225100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_225100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225100 prefixEnd_225100 := by exact prefixLift 225100
  have htrace : WordTrace (prefixWord ++ tailWord_225100) baseStart_225100 baseEnd_225100 := by
    simpa [prefixWord, tailWord_225100, baseEnd_225100] using wordTrace_append hprefix tailTrace_225100
  have hstable : (prefixWord ++ tailWord_225100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225100).length < 2 ^ (prefixWord ++ tailWord_225100).sum := by decide
  have hdescent : baseEnd_225100 < baseStart_225100 := by decide
  rcases family_descends (prefixWord ++ tailWord_225100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225174 : List Nat := [5, 3, 1, 1, 9]
def baseStart_225174 : Nat := 118140960795 + 225174 * 2 ^ 59
def prefixEnd_225174 : Nat := 4983230072969 + 3 ^ 40 * 225174 * 2
def baseEnd_225174 : Nat := 2537667882482463415955

theorem tailTrace_225174 : CollatzResearch.WordTrace tailWord_225174 prefixEnd_225174 2537667882482463415955 := by
  unfold tailWord_225174
  simp only [CollatzResearch.WordTrace]
  refine ⟨513298155390033093913661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5475180324160353001745717 513298155390033093913661)
  ·
    refine ⟨192486808271262410217623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 513298155390033093913661 192486808271262410217623)
    ·
      refine ⟨288730212406893615326435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192486808271262410217623 288730212406893615326435)
      ·
        refine ⟨433095318610340422989653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288730212406893615326435 433095318610340422989653)
        ·
          refine ⟨2537667882482463415955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 433095318610340422989653 2537667882482463415955)
          ·
            rfl

theorem cell19_225174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_225174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225174 prefixEnd_225174 := by exact prefixLift 225174
  have htrace : WordTrace (prefixWord ++ tailWord_225174) baseStart_225174 baseEnd_225174 := by
    simpa [prefixWord, tailWord_225174, baseEnd_225174] using wordTrace_append hprefix tailTrace_225174
  have hstable : (prefixWord ++ tailWord_225174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225174).length < 2 ^ (prefixWord ++ tailWord_225174).sum := by decide
  have hdescent : baseEnd_225174 < baseStart_225174 := by decide
  rcases family_descends (prefixWord ++ tailWord_225174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225176 : List Nat := [2, 1, 2, 6, 1, 7]
def baseStart_225176 : Nat := 118140960795 + 225176 * 2 ^ 59
def prefixEnd_225176 : Nat := 4983230072969 + 3 ^ 40 * 225176 * 2
def baseEnd_225176 : Nat := 7613071266299011131815

theorem tailTrace_225176 : CollatzResearch.WordTrace tailWord_225176 prefixEnd_225176 7613071266299011131815 := by
  unfold tailWord_225176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106421716116641922095691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475228954822189229460921 4106421716116641922095691)
  ·
    refine ⟨6159632574174962883143537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106421716116641922095691 6159632574174962883143537)
    ·
      refine ⟨4619724430631222162357653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6159632574174962883143537 4619724430631222162357653)
      ·
        refine ⟨216549582685838538860515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4619724430631222162357653 216549582685838538860515)
        ·
          refine ⟨324824374028757808290773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216549582685838538860515 324824374028757808290773)
          ·
            refine ⟨7613071266299011131815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 324824374028757808290773 7613071266299011131815)
            ·
              rfl

theorem cell19_225176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_225176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225176 prefixEnd_225176 := by exact prefixLift 225176
  have htrace : WordTrace (prefixWord ++ tailWord_225176) baseStart_225176 baseEnd_225176 := by
    simpa [prefixWord, tailWord_225176, baseEnd_225176] using wordTrace_append hprefix tailTrace_225176
  have hstable : (prefixWord ++ tailWord_225176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225176).length < 2 ^ (prefixWord ++ tailWord_225176).sum := by decide
  have hdescent : baseEnd_225176 < baseStart_225176 := by decide
  rcases family_descends (prefixWord ++ tailWord_225176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225178 : List Nat := [3, 1, 1, 4, 2, 8]
def baseStart_225178 : Nat := 118140960795 + 225178 * 2 ^ 59
def prefixEnd_225178 : Nat := 4983230072969 + 3 ^ 40 * 225178 * 2
def baseEnd_225178 : Nat := 7613138885150632015765

theorem tailTrace_225178 : CollatzResearch.WordTrace tailWord_225178 prefixEnd_225178 7613138885150632015765 := by
  unfold tailWord_225178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053229094556509546441047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5475277585484025457176125 2053229094556509546441047)
  ·
    refine ⟨3079843641834764319661571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2053229094556509546441047 3079843641834764319661571)
    ·
      refine ⟨4619765462752146479492357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079843641834764319661571 4619765462752146479492357)
      ·
        refine ⟨866206024266027464904817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4619765462752146479492357 866206024266027464904817)
        ·
          refine ⟨649654518199520598678613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866206024266027464904817 649654518199520598678613)
          ·
            refine ⟨7613138885150632015765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 649654518199520598678613 7613138885150632015765)
            ·
              rfl

theorem cell19_225178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_225178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225178 prefixEnd_225178 := by exact prefixLift 225178
  have htrace : WordTrace (prefixWord ++ tailWord_225178) baseStart_225178 baseEnd_225178 := by
    simpa [prefixWord, tailWord_225178, baseEnd_225178] using wordTrace_append hprefix tailTrace_225178
  have hstable : (prefixWord ++ tailWord_225178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225178).length < 2 ^ (prefixWord ++ tailWord_225178).sum := by decide
  have hdescent : baseEnd_225178 < baseStart_225178 := by decide
  rcases family_descends (prefixWord ++ tailWord_225178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225273 : List Nat := [1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_225273 : Nat := 118140960795 + 225273 * 2 ^ 59
def prefixEnd_225273 : Nat := 4983230072969 + 3 ^ 40 * 225273 * 2
def baseEnd_225273 : Nat := 68547157025423616030515

theorem tailTrace_225273 : CollatzResearch.WordTrace tailWord_225273 prefixEnd_225273 68547157025423616030515 := by
  unfold tailWord_225273
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216381312881869410472473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5477587541921246273648315 8216381312881869410472473)
  ·
    refine ⟨6162285984661402057854355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8216381312881869410472473 6162285984661402057854355)
    ·
      refine ⟨9243428976992103086781533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162285984661402057854355 9243428976992103086781533)
      ·
        refine ⟨3466285866372038657543075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9243428976992103086781533 3466285866372038657543075)
        ·
          refine ⟨5199428799558057986314613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466285866372038657543075 5199428799558057986314613)
          ·
            refine ⟨487446449958567936216995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5199428799558057986314613 487446449958567936216995)
            ·
              refine ⟨731169674937851904325493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487446449958567936216995 731169674937851904325493)
              ·
                refine ⟨68547157025423616030515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731169674937851904325493 68547157025423616030515)
                ·
                  rfl

theorem cell19_225273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_225273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225273 prefixEnd_225273 := by exact prefixLift 225273
  have htrace : WordTrace (prefixWord ++ tailWord_225273) baseStart_225273 baseEnd_225273 := by
    simpa [prefixWord, tailWord_225273, baseEnd_225273] using wordTrace_append hprefix tailTrace_225273
  have hstable : (prefixWord ++ tailWord_225273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225273).length < 2 ^ (prefixWord ++ tailWord_225273).sum := by decide
  have hdescent : baseEnd_225273 < baseStart_225273 := by decide
  rcases family_descends (prefixWord ++ tailWord_225273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225290 : List Nat := [3, 1, 2, 2, 4, 2, 5]
def baseStart_225290 : Nat := 118140960795 + 225290 * 2 ^ 59
def prefixEnd_225290 : Nat := 4983230072969 + 3 ^ 40 * 225290 * 2
def baseEnd_225290 : Nat := 22850776622524204550897

theorem tailTrace_225290 : CollatzResearch.WordTrace tailWord_225290 prefixEnd_225290 22850776622524204550897 := by
  unfold tailWord_225290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054250338455070328460331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5478000902546854209227549 2054250338455070328460331)
  ·
    refine ⟨3081375507682605492690497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054250338455070328460331 3081375507682605492690497)
    ·
      refine ⟨2311031630761954119517873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3081375507682605492690497 2311031630761954119517873)
      ·
        refine ⟨1733273723071465589638405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311031630761954119517873 1733273723071465589638405)
        ·
          refine ⟨324988823075899798057201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1733273723071465589638405 324988823075899798057201)
          ·
            refine ⟨243741617306924848542901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324988823075899798057201 243741617306924848542901)
            ·
              refine ⟨22850776622524204550897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243741617306924848542901 22850776622524204550897)
              ·
                rfl

theorem cell19_225290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_225290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225290 prefixEnd_225290 := by exact prefixLift 225290
  have htrace : WordTrace (prefixWord ++ tailWord_225290) baseStart_225290 baseEnd_225290 := by
    simpa [prefixWord, tailWord_225290, baseEnd_225290] using wordTrace_append hprefix tailTrace_225290
  have hstable : (prefixWord ++ tailWord_225290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225290).length < 2 ^ (prefixWord ++ tailWord_225290).sum := by decide
  have hdescent : baseEnd_225290 < baseStart_225290 := by decide
  rcases family_descends (prefixWord ++ tailWord_225290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225309 : List Nat := [1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_225309 : Nat := 118140960795 + 225309 * 2 ^ 59
def prefixEnd_225309 : Nat := 4983230072969 + 3 ^ 40 * 225309 * 2
def baseEnd_225309 : Nat := 68558111279386199230417

theorem tailTrace_225309 : CollatzResearch.WordTrace tailWord_225309 prefixEnd_225309 68558111279386199230417 := by
  unfold tailWord_225309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217694340751447558782981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478462893834298372521987 8217694340751447558782981)
  ·
    refine ⟨1540817688890896417271809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8217694340751447558782981 1540817688890896417271809)
    ·
      refine ⟨1155613266668172312953857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1540817688890896417271809 1155613266668172312953857)
      ·
        refine ⟨866709950001129234715393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1155613266668172312953857 866709950001129234715393)
        ·
          refine ⟨650032462500846926036545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866709950001129234715393 650032462500846926036545)
          ·
            refine ⟨487524346875635194527409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650032462500846926036545 487524346875635194527409)
            ·
              refine ⟨365643260156726395895557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487524346875635194527409 365643260156726395895557)
              ·
                refine ⟨68558111279386199230417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365643260156726395895557 68558111279386199230417)
                ·
                  rfl

theorem cell19_225309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_225309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225309 prefixEnd_225309 := by exact prefixLift 225309
  have htrace : WordTrace (prefixWord ++ tailWord_225309) baseStart_225309 baseEnd_225309 := by
    simpa [prefixWord, tailWord_225309, baseEnd_225309] using wordTrace_append hprefix tailTrace_225309
  have hstable : (prefixWord ++ tailWord_225309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225309).length < 2 ^ (prefixWord ++ tailWord_225309).sum := by decide
  have hdescent : baseEnd_225309 < baseStart_225309 := by decide
  rcases family_descends (prefixWord ++ tailWord_225309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225311 : List Nat := [1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_225311 : Nat := 118140960795 + 225311 * 2 ^ 59
def prefixEnd_225311 : Nat := 4983230072969 + 3 ^ 40 * 225311 * 2
def baseEnd_225311 : Nat := 68558719849050787185967

theorem tailTrace_225311 : CollatzResearch.WordTrace tailWord_225311 prefixEnd_225311 68558719849050787185967 := by
  unfold tailWord_225311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217767286744201900355787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478511524496134600237191 8217767286744201900355787)
  ·
    refine ⟨12326650930116302850533681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8217767286744201900355787 12326650930116302850533681)
    ·
      refine ⟨9244988197587227137900261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12326650930116302850533681 9244988197587227137900261)
      ·
        refine ⟨1733435287047605088356299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9244988197587227137900261 1733435287047605088356299)
        ·
          refine ⟨2600152930571407632534449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733435287047605088356299 2600152930571407632534449)
          ·
            refine ⟨1950114697928555724400837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600152930571407632534449 1950114697928555724400837)
            ·
              refine ⟨365646505861604198325157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1950114697928555724400837 365646505861604198325157)
              ·
                refine ⟨68558719849050787185967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365646505861604198325157 68558719849050787185967)
                ·
                  rfl

theorem cell19_225311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_225311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225311 prefixEnd_225311 := by exact prefixLift 225311
  have htrace : WordTrace (prefixWord ++ tailWord_225311) baseStart_225311 baseEnd_225311 := by
    simpa [prefixWord, tailWord_225311, baseEnd_225311] using wordTrace_append hprefix tailTrace_225311
  have hstable : (prefixWord ++ tailWord_225311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225311).length < 2 ^ (prefixWord ++ tailWord_225311).sum := by decide
  have hdescent : baseEnd_225311 < baseStart_225311 := by decide
  rcases family_descends (prefixWord ++ tailWord_225311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225330 : List Nat := [3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_225330 : Nat := 118140960795 + 225330 * 2 ^ 59
def prefixEnd_225330 : Nat := 4983230072969 + 3 ^ 40 * 225330 * 2
def baseEnd_225330 : Nat := 68564501260864372763693

theorem tailTrace_225330 : CollatzResearch.WordTrace tailWord_225330 prefixEnd_225330 68564501260864372763693 := by
  unfold tailWord_225330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054615068418842036324361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5478973515783578763531629 2054615068418842036324361)
  ·
    refine ⟨1540961301314131527243271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2054615068418842036324361 1540961301314131527243271)
    ·
      refine ⟨2311441951971197290864907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1540961301314131527243271 2311441951971197290864907)
      ·
        refine ⟨3467162927956795936297361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311441951971197290864907 3467162927956795936297361)
        ·
          refine ⟨2600372195967596952223021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467162927956795936297361 2600372195967596952223021)
          ·
            refine ⟨975139573487848857083633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2600372195967596952223021 975139573487848857083633)
            ·
              refine ⟨731354680115886642812725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975139573487848857083633 731354680115886642812725)
              ·
                refine ⟨68564501260864372763693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731354680115886642812725 68564501260864372763693)
                ·
                  rfl

theorem cell19_225330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_225330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225330 prefixEnd_225330 := by exact prefixLift 225330
  have htrace : WordTrace (prefixWord ++ tailWord_225330) baseStart_225330 baseEnd_225330 := by
    simpa [prefixWord, tailWord_225330, baseEnd_225330] using wordTrace_append hprefix tailTrace_225330
  have hstable : (prefixWord ++ tailWord_225330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225330).length < 2 ^ (prefixWord ++ tailWord_225330).sum := by decide
  have hdescent : baseEnd_225330 < baseStart_225330 := by decide
  rcases family_descends (prefixWord ++ tailWord_225330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225368 : List Nat := [2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_225368 : Nat := 118140960795 + 225368 * 2 ^ 59
def prefixEnd_225368 : Nat := 4983230072969 + 3 ^ 40 * 225368 * 2
def baseEnd_225368 : Nat := 68576064084491543919145

theorem tailTrace_225368 : CollatzResearch.WordTrace tailWord_225368 prefixEnd_225368 68576064084491543919145 := by
  unfold tailWord_225368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109923123768850317590379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5479897498358467090120505 4109923123768850317590379)
  ·
    refine ⟨6164884685653275476385569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109923123768850317590379 6164884685653275476385569)
    ·
      refine ⟨4623663514239956607289177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6164884685653275476385569 4623663514239956607289177)
      ·
        refine ⟨3467747635679967455466883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4623663514239956607289177 3467747635679967455466883)
        ·
          refine ⟨5201621453519951183200325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467747635679967455466883 5201621453519951183200325)
          ·
            refine ⟨975304022534990846850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5201621453519951183200325 975304022534990846850061)
            ·
              refine ⟨365739008450621567568773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 975304022534990846850061 365739008450621567568773)
              ·
                refine ⟨68576064084491543919145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365739008450621567568773 68576064084491543919145)
                ·
                  rfl

theorem cell19_225368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_225368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225368 prefixEnd_225368 := by exact prefixLift 225368
  have htrace : WordTrace (prefixWord ++ tailWord_225368) baseStart_225368 baseEnd_225368 := by
    simpa [prefixWord, tailWord_225368, baseEnd_225368] using wordTrace_append hprefix tailTrace_225368
  have hstable : (prefixWord ++ tailWord_225368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225368).length < 2 ^ (prefixWord ++ tailWord_225368).sum := by decide
  have hdescent : baseEnd_225368 < baseStart_225368 := by decide
  rcases family_descends (prefixWord ++ tailWord_225368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225427 : List Nat := [1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_225427 : Nat := 118140960795 + 225427 * 2 ^ 59
def prefixEnd_225427 : Nat := 4983230072969 + 3 ^ 40 * 225427 * 2
def baseEnd_225427 : Nat := 68594016889596888607873

theorem tailTrace_225427 : CollatzResearch.WordTrace tailWord_225427 prefixEnd_225427 68594016889596888607873 := by
  unfold tailWord_225427
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221998154323953711578535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481332102882635807719023 8221998154323953711578535)
  ·
    refine ⟨12332997231485930567367803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221998154323953711578535 12332997231485930567367803)
    ·
      refine ⟨18499495847228895851051705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12332997231485930567367803 18499495847228895851051705)
      ·
        refine ⟨13874621885421671888288779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18499495847228895851051705 13874621885421671888288779)
        ·
          refine ⟨20811932828132507832433169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874621885421671888288779 20811932828132507832433169)
          ·
            refine ⟨15608949621099380874324877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20811932828132507832433169 15608949621099380874324877)
            ·
              refine ⟨5853356107912267827871829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15608949621099380874324877 5853356107912267827871829)
              ·
                refine ⟨68594016889596888607873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5853356107912267827871829 68594016889596888607873)
                ·
                  rfl

theorem cell19_225427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_225427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225427 prefixEnd_225427 := by exact prefixLift 225427
  have htrace : WordTrace (prefixWord ++ tailWord_225427) baseStart_225427 baseEnd_225427 := by
    simpa [prefixWord, tailWord_225427, baseEnd_225427] using wordTrace_append hprefix tailTrace_225427
  have hstable : (prefixWord ++ tailWord_225427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225427).length < 2 ^ (prefixWord ++ tailWord_225427).sum := by decide
  have hdescent : baseEnd_225427 < baseStart_225427 := by decide
  rcases family_descends (prefixWord ++ tailWord_225427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225438 : List Nat := [4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_225438 : Nat := 118140960795 + 225438 * 2 ^ 59
def prefixEnd_225438 : Nat := 4983230072969 + 3 ^ 40 * 225438 * 2
def baseEnd_225438 : Nat := 68597364022752122363399

theorem tailTrace_225438 : CollatzResearch.WordTrace tailWord_225438 prefixEnd_225438 68597364022752122363399 := by
  unfold tailWord_225438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027799919660512823778621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5481599571522735060152645 1027799919660512823778621)
  ·
    refine ⟨385424969872692308916983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1027799919660512823778621 385424969872692308916983)
    ·
      refine ⟨578137454809038463375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385424969872692308916983 578137454809038463375475)
      ·
        refine ⟨867206182213557695063213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578137454809038463375475 867206182213557695063213)
        ·
          refine ⟨325202318330084135648705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 867206182213557695063213 325202318330084135648705)
          ·
            refine ⟨243901738747563101736529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325202318330084135648705 243901738747563101736529)
            ·
              refine ⟨182926304060672326302397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243901738747563101736529 182926304060672326302397)
              ·
                refine ⟨68597364022752122363399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182926304060672326302397 68597364022752122363399)
                ·
                  rfl

theorem cell19_225438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_225438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225438 prefixEnd_225438 := by exact prefixLift 225438
  have htrace : WordTrace (prefixWord ++ tailWord_225438) baseStart_225438 baseEnd_225438 := by
    simpa [prefixWord, tailWord_225438, baseEnd_225438] using wordTrace_append hprefix tailTrace_225438
  have hstable : (prefixWord ++ tailWord_225438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225438).length < 2 ^ (prefixWord ++ tailWord_225438).sum := by decide
  have hdescent : baseEnd_225438 < baseStart_225438 := by decide
  rcases family_descends (prefixWord ++ tailWord_225438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225442 : List Nat := [3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_225442 : Nat := 118140960795 + 225442 * 2 ^ 59
def prefixEnd_225442 : Nat := 4983230072969 + 3 ^ 40 * 225442 * 2
def baseEnd_225442 : Nat := 68598581162081298274499

theorem tailTrace_225442 : CollatzResearch.WordTrace tailWord_225442 prefixEnd_225442 68598581162081298274499 := by
  unfold tailWord_225442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055636312317402818343645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5481696832846407515583053 2055636312317402818343645)
  ·
    refine ⟨770863617119026056878867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2055636312317402818343645 770863617119026056878867)
    ·
      refine ⟨1156295425678539085318301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770863617119026056878867 1156295425678539085318301)
      ·
        refine ⟨433610784629452156994363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1156295425678539085318301 433610784629452156994363)
        ·
          refine ⟨650416176944178235491545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433610784629452156994363 650416176944178235491545)
          ·
            refine ⟨487812132708133676618659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650416176944178235491545 487812132708133676618659)
            ·
              refine ⟨731718199062200514927989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487812132708133676618659 731718199062200514927989)
              ·
                refine ⟨68598581162081298274499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731718199062200514927989 68598581162081298274499)
                ·
                  rfl

theorem cell19_225442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_225442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225442 prefixEnd_225442 := by exact prefixLift 225442
  have htrace : WordTrace (prefixWord ++ tailWord_225442) baseStart_225442 baseEnd_225442 := by
    simpa [prefixWord, tailWord_225442, baseEnd_225442] using wordTrace_append hprefix tailTrace_225442
  have hstable : (prefixWord ++ tailWord_225442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225442).length < 2 ^ (prefixWord ++ tailWord_225442).sum := by decide
  have hdescent : baseEnd_225442 < baseStart_225442 := by decide
  rcases family_descends (prefixWord ++ tailWord_225442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225463 : List Nat := [1, 1, 3, 1, 4, 4, 5]
def baseStart_225463 : Nat := 118140960795 + 225463 * 2 ^ 59
def prefixEnd_225463 : Nat := 4983230072969 + 3 ^ 40 * 225463 * 2
def baseEnd_225463 : Nat := 22868323714519823935925

theorem tailTrace_225463 : CollatzResearch.WordTrace tailWord_225463 prefixEnd_225463 22868323714519823935925 := by
  unfold tailWord_225463
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223311182193531859889043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5482207454795687906592695 8223311182193531859889043)
  ·
    refine ⟨12334966773290297789833565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8223311182193531859889043 12334966773290297789833565)
    ·
      refine ⟨4625612539983861671187587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12334966773290297789833565 4625612539983861671187587)
      ·
        refine ⟨6938418809975792506781381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625612539983861671187587 6938418809975792506781381)
        ·
          refine ⟨1300953526870461095021509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6938418809975792506781381 1300953526870461095021509)
          ·
            refine ⟨243928786288211455316533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1300953526870461095021509 243928786288211455316533)
            ·
              refine ⟨22868323714519823935925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243928786288211455316533 22868323714519823935925)
              ·
                rfl

theorem cell19_225463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_225463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225463 prefixEnd_225463 := by exact prefixLift 225463
  have htrace : WordTrace (prefixWord ++ tailWord_225463) baseStart_225463 baseEnd_225463 := by
    simpa [prefixWord, tailWord_225463, baseEnd_225463] using wordTrace_append hprefix tailTrace_225463
  have hstable : (prefixWord ++ tailWord_225463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225463).length < 2 ^ (prefixWord ++ tailWord_225463).sum := by decide
  have hdescent : baseEnd_225463 < baseStart_225463 := by decide
  rcases family_descends (prefixWord ++ tailWord_225463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225482 : List Nat := [3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_225482 : Nat := 118140960795 + 225482 * 2 ^ 59
def prefixEnd_225482 : Nat := 4983230072969 + 3 ^ 40 * 225482 * 2
def baseEnd_225482 : Nat := 68610752555373057385501

theorem tailTrace_225482 : CollatzResearch.WordTrace tailWord_225482 prefixEnd_225482 68610752555373057385501 := by
  unfold tailWord_225482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056001042281174526207675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5482669446083132069887133 2056001042281174526207675)
  ·
    refine ⟨3084001563421761789311513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2056001042281174526207675 3084001563421761789311513)
    ·
      refine ⟨2313001172566321341983635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3084001563421761789311513 2313001172566321341983635)
      ·
        refine ⟨3469501758849482012975453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313001172566321341983635 3469501758849482012975453)
        ·
          refine ⟨1301063159568555754865795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3469501758849482012975453 1301063159568555754865795)
          ·
            refine ⟨1951594739352833632298693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301063159568555754865795 1951594739352833632298693)
            ·
              refine ⟨365924013628656306056005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1951594739352833632298693 365924013628656306056005)
              ·
                refine ⟨68610752555373057385501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365924013628656306056005 68610752555373057385501)
                ·
                  rfl

theorem cell19_225482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_225482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225482 prefixEnd_225482 := by exact prefixLift 225482
  have htrace : WordTrace (prefixWord ++ tailWord_225482) baseStart_225482 baseEnd_225482 := by
    simpa [prefixWord, tailWord_225482, baseEnd_225482] using wordTrace_append hprefix tailTrace_225482
  have hstable : (prefixWord ++ tailWord_225482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225482).length < 2 ^ (prefixWord ++ tailWord_225482).sum := by decide
  have hdescent : baseEnd_225482 < baseStart_225482 := by decide
  rcases family_descends (prefixWord ++ tailWord_225482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225541 : List Nat := [1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_225541 : Nat := 118140960795 + 225541 * 2 ^ 59
def prefixEnd_225541 : Nat := 4983230072969 + 3 ^ 40 * 225541 * 2
def baseEnd_225541 : Nat := 68628705360478402074229

theorem tailTrace_225541 : CollatzResearch.WordTrace tailWord_225541 prefixEnd_225541 68628705360478402074229 := by
  unfold tailWord_225541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226156075910951181228477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484104050607300787485651 8226156075910951181228477)
  ·
    refine ⟨3084808528466606692960679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8226156075910951181228477 3084808528466606692960679)
    ·
      refine ⟨4627212792699910039441019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084808528466606692960679 4627212792699910039441019)
      ·
        refine ⟨6940819189049865059161529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627212792699910039441019 6940819189049865059161529)
        ·
          refine ⟨5205614391787398794371147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940819189049865059161529 5205614391787398794371147)
          ·
            refine ⟨7808421587681098191556721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205614391787398794371147 7808421587681098191556721)
            ·
              refine ⟨5856316190760823643667541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808421587681098191556721 5856316190760823643667541)
              ·
                refine ⟨68628705360478402074229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5856316190760823643667541 68628705360478402074229)
                ·
                  rfl

theorem cell19_225541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_225541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225541 prefixEnd_225541 := by exact prefixLift 225541
  have htrace : WordTrace (prefixWord ++ tailWord_225541) baseStart_225541 baseEnd_225541 := by
    simpa [prefixWord, tailWord_225541, baseEnd_225541] using wordTrace_append hprefix tailTrace_225541
  have hstable : (prefixWord ++ tailWord_225541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225541).length < 2 ^ (prefixWord ++ tailWord_225541).sum := by decide
  have hdescent : baseEnd_225541 < baseStart_225541 := by decide
  rcases family_descends (prefixWord ++ tailWord_225541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225632 : List Nat := [2, 1, 1, 3, 6, 1, 5]
def baseStart_225632 : Nat := 118140960795 + 225632 * 2 ^ 59
def prefixEnd_225632 : Nat := 4983230072969 + 3 ^ 40 * 225632 * 2
def baseEnd_225632 : Nat := 22885465093405718017253

theorem tailTrace_225632 : CollatzResearch.WordTrace tailWord_225632 prefixEnd_225632 22885465093405718017253 := by
  unfold tailWord_225632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114737559290636861395575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5486316745720849148527433 4114737559290636861395575)
  ·
    refine ⟨6172106338935955292093363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114737559290636861395575 6172106338935955292093363)
    ·
      refine ⟨9258159508403932938140045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172106338935955292093363 9258159508403932938140045)
      ·
        refine ⟨3471809815651474851802517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9258159508403932938140045 3471809815651474851802517)
        ·
          refine ⟨162741085108662883678243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3471809815651474851802517 162741085108662883678243)
          ·
            refine ⟨244111627662994325517365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162741085108662883678243 244111627662994325517365)
            ·
              refine ⟨22885465093405718017253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244111627662994325517365 22885465093405718017253)
              ·
                rfl

theorem cell19_225632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_225632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225632 prefixEnd_225632 := by exact prefixLift 225632
  have htrace : WordTrace (prefixWord ++ tailWord_225632) baseStart_225632 baseEnd_225632 := by
    simpa [prefixWord, tailWord_225632, baseEnd_225632] using wordTrace_append hprefix tailTrace_225632
  have hstable : (prefixWord ++ tailWord_225632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225632).length < 2 ^ (prefixWord ++ tailWord_225632).sum := by decide
  have hdescent : baseEnd_225632 < baseStart_225632 := by decide
  rcases family_descends (prefixWord ++ tailWord_225632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225634 : List Nat := [3, 3, 2, 1, 1, 2, 7]
def baseStart_225634 : Nat := 118140960795 + 225634 * 2 ^ 59
def prefixEnd_225634 : Nat := 4983230072969 + 3 ^ 40 * 225634 * 2
def baseEnd_225634 : Nat := 22885667949960580669103

theorem tailTrace_225634 : CollatzResearch.WordTrace tailWord_225634 prefixEnd_225634 22885667949960580669103 := by
  unfold tailWord_225634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057387016143507016090989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5486365376382685376242637 2057387016143507016090989)
  ·
    refine ⟨771520131053815131034121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2057387016143507016090989 771520131053815131034121)
    ·
      refine ⟨578640098290361348275591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 771520131053815131034121 578640098290361348275591)
      ·
        refine ⟨867960147435542022413387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578640098290361348275591 867960147435542022413387)
        ·
          refine ⟨1301940221153313033620081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867960147435542022413387 1301940221153313033620081)
          ·
            refine ⟨976455165864984775215061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301940221153313033620081 976455165864984775215061)
            ·
              refine ⟨22885667949960580669103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 976455165864984775215061 22885667949960580669103)
              ·
                rfl

theorem cell19_225634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_225634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225634 prefixEnd_225634 := by exact prefixLift 225634
  have htrace : WordTrace (prefixWord ++ tailWord_225634) baseStart_225634 baseEnd_225634 := by
    simpa [prefixWord, tailWord_225634, baseEnd_225634] using wordTrace_append hprefix tailTrace_225634
  have hstable : (prefixWord ++ tailWord_225634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225634).length < 2 ^ (prefixWord ++ tailWord_225634).sum := by decide
  have hdescent : baseEnd_225634 < baseStart_225634 := by decide
  rcases family_descends (prefixWord ++ tailWord_225634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225653 : List Nat := [1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_225653 : Nat := 118140960795 + 225653 * 2 ^ 59
def prefixEnd_225653 : Nat := 4983230072969 + 3 ^ 40 * 225653 * 2
def baseEnd_225653 : Nat := 68662785261695327585035

theorem tailTrace_225653 : CollatzResearch.WordTrace tailWord_225653 prefixEnd_225653 68662785261695327585035 := by
  unfold tailWord_225653
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230241051505194309305613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5486827367670129539537075 8230241051505194309305613)
  ·
    refine ⟨3086340394314447865989605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8230241051505194309305613 3086340394314447865989605)
    ·
      refine ⟨578688823933958974873051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3086340394314447865989605 578688823933958974873051)
      ·
        refine ⟨868033235900938462309577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578688823933958974873051 868033235900938462309577)
        ·
          refine ⟨651024926925703846732183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868033235900938462309577 651024926925703846732183)
          ·
            refine ⟨976537390388555770098275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651024926925703846732183 976537390388555770098275)
            ·
              refine ⟨1464806085582833655147413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976537390388555770098275 1464806085582833655147413)
              ·
                refine ⟨68662785261695327585035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1464806085582833655147413 68662785261695327585035)
                ·
                  rfl

theorem cell19_225653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_225653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225653 prefixEnd_225653 := by exact prefixLift 225653
  have htrace : WordTrace (prefixWord ++ tailWord_225653) baseStart_225653 baseEnd_225653 := by
    simpa [prefixWord, tailWord_225653, baseEnd_225653] using wordTrace_append hprefix tailTrace_225653
  have hstable : (prefixWord ++ tailWord_225653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225653).length < 2 ^ (prefixWord ++ tailWord_225653).sum := by decide
  have hdescent : baseEnd_225653 < baseStart_225653 := by decide
  rcases family_descends (prefixWord ++ tailWord_225653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225693 : List Nat := [1, 4, 2, 1, 11]
def baseStart_225693 : Nat := 118140960795 + 225693 * 2 ^ 59
def prefixEnd_225693 : Nat := 4983230072969 + 3 ^ 40 * 225693 * 2
def baseEnd_225693 : Nat := 2543516913147669877631

theorem tailTrace_225693 : CollatzResearch.WordTrace tailWord_225693 prefixEnd_225693 2543516913147669877631 := by
  unfold tailWord_225693
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231699971360281140761733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5487799980906854093841155 8231699971360281140761733)
  ·
    refine ⟨1543443744630052713892825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8231699971360281140761733 1543443744630052713892825)
    ·
      refine ⟨1157582808472539535419619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1543443744630052713892825 1157582808472539535419619)
      ·
        refine ⟨1736374212708809303129429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157582808472539535419619 1736374212708809303129429)
        ·
          refine ⟨2543516913147669877631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1736374212708809303129429 2543516913147669877631)
          ·
            rfl

theorem cell19_225693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_225693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225693 prefixEnd_225693 := by exact prefixLift 225693
  have htrace : WordTrace (prefixWord ++ tailWord_225693) baseStart_225693 baseEnd_225693 := by
    simpa [prefixWord, tailWord_225693, baseEnd_225693] using wordTrace_append hprefix tailTrace_225693
  have hstable : (prefixWord ++ tailWord_225693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225693).length < 2 ^ (prefixWord ++ tailWord_225693).sum := by decide
  have hdescent : baseEnd_225693 < baseStart_225693 := by decide
  rcases family_descends (prefixWord ++ tailWord_225693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225746 : List Nat := [3, 2, 2, 4, 1, 1, 6]
def baseStart_225746 : Nat := 118140960795 + 225746 * 2 ^ 59
def prefixEnd_225746 : Nat := 4983230072969 + 3 ^ 40 * 225746 * 2
def baseEnd_225746 : Nat := 22897027917032889172705

theorem tailTrace_225746 : CollatzResearch.WordTrace tailWord_225746 prefixEnd_225746 22897027917032889172705 := by
  unfold tailWord_225746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058408260042067798110273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5489088693445514128294061 2058408260042067798110273)
  ·
    refine ⟨1543806195031550848582705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2058408260042067798110273 1543806195031550848582705)
    ·
      refine ⟨1157854646273663136437029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1543806195031550848582705 1157854646273663136437029)
      ·
        refine ⟨217097746176311838081943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1157854646273663136437029 217097746176311838081943)
        ·
          refine ⟨325646619264467757122915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217097746176311838081943 325646619264467757122915)
          ·
            refine ⟨488469928896701635684373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325646619264467757122915 488469928896701635684373)
            ·
              refine ⟨22897027917032889172705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 488469928896701635684373 22897027917032889172705)
              ·
                rfl

theorem cell19_225746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_225746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225746 prefixEnd_225746 := by exact prefixLift 225746
  have htrace : WordTrace (prefixWord ++ tailWord_225746) baseStart_225746 baseEnd_225746 := by
    simpa [prefixWord, tailWord_225746, baseEnd_225746] using wordTrace_append hprefix tailTrace_225746
  have hstable : (prefixWord ++ tailWord_225746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225746).length < 2 ^ (prefixWord ++ tailWord_225746).sum := by decide
  have hdescent : baseEnd_225746 < baseStart_225746 := by decide
  rcases family_descends (prefixWord ++ tailWord_225746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225748 : List Nat := [2, 4, 1, 2, 2, 2, 6]
def baseStart_225748 : Nat := 118140960795 + 225748 * 2 ^ 59
def prefixEnd_225748 : Nat := 4983230072969 + 3 ^ 40 * 225748 * 2
def baseEnd_225748 : Nat := 22897230773587751824555

theorem tailTrace_225748 : CollatzResearch.WordTrace tailWord_225748 prefixEnd_225748 22897230773587751824555 := by
  unfold tailWord_225748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116852993080512767006949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5489137324107350356009265 4116852993080512767006949)
  ·
    refine ⟨771909936202596143813803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4116852993080512767006949 771909936202596143813803)
    ·
      refine ⟨1157864904303894215720705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771909936202596143813803 1157864904303894215720705)
      ·
        refine ⟨868398678227920661790529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157864904303894215720705 868398678227920661790529)
        ·
          refine ⟨651299008670940496342897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 868398678227920661790529 651299008670940496342897)
          ·
            refine ⟨488474256503205372257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651299008670940496342897 488474256503205372257173)
            ·
              refine ⟨22897230773587751824555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 488474256503205372257173 22897230773587751824555)
              ·
                rfl

theorem cell19_225748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_225748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225748 prefixEnd_225748 := by exact prefixLift 225748
  have htrace : WordTrace (prefixWord ++ tailWord_225748) baseStart_225748 baseEnd_225748 := by
    simpa [prefixWord, tailWord_225748, baseEnd_225748] using wordTrace_append hprefix tailTrace_225748
  have hstable : (prefixWord ++ tailWord_225748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225748).length < 2 ^ (prefixWord ++ tailWord_225748).sum := by decide
  have hdescent : baseEnd_225748 < baseStart_225748 := by decide
  rcases family_descends (prefixWord ++ tailWord_225748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225845 : List Nat := [1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_225845 : Nat := 118140960795 + 225845 * 2 ^ 59
def prefixEnd_225845 : Nat := 4983230072969 + 3 ^ 40 * 225845 * 2
def baseEnd_225845 : Nat := 68721207949495771317845

theorem tailTrace_225845 : CollatzResearch.WordTrace tailWord_225845 prefixEnd_225845 68721207949495771317845 := by
  unfold tailWord_225845
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237243866809611100294989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5491495911206407400196659 8237243866809611100294989)
  ·
    refine ⟨3088966450053604162610621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8237243866809611100294989 3088966450053604162610621)
    ·
      refine ⟨1158362418770101560978983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3088966450053604162610621 1158362418770101560978983)
      ·
        refine ⟨1737543628155152341468475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158362418770101560978983 1737543628155152341468475)
        ·
          refine ⟨2606315442232728512202713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737543628155152341468475 2606315442232728512202713)
          ·
            refine ⟨1954736581674546384152035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606315442232728512202713 1954736581674546384152035)
            ·
              refine ⟨2932104872511819576228053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954736581674546384152035 2932104872511819576228053)
              ·
                refine ⟨68721207949495771317845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2932104872511819576228053 68721207949495771317845)
                ·
                  rfl

theorem cell19_225845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_225845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225845 prefixEnd_225845 := by exact prefixLift 225845
  have htrace : WordTrace (prefixWord ++ tailWord_225845) baseStart_225845 baseEnd_225845 := by
    simpa [prefixWord, tailWord_225845, baseEnd_225845] using wordTrace_append hprefix tailTrace_225845
  have hstable : (prefixWord ++ tailWord_225845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225845).length < 2 ^ (prefixWord ++ tailWord_225845).sum := by decide
  have hdescent : baseEnd_225845 < baseStart_225845 := by decide
  rcases family_descends (prefixWord ++ tailWord_225845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225860 : List Nat := [2, 3, 5, 1, 8]
def baseStart_225860 : Nat := 118140960795 + 225860 * 2 ^ 59
def prefixEnd_225860 : Nat := 4983230072969 + 3 ^ 40 * 225860 * 2
def baseEnd_225860 : Nat := 2545398971184451147573

theorem tailTrace_225860 : CollatzResearch.WordTrace tailWord_225860 prefixEnd_225860 2545398971184451147573 := by
  unfold tailWord_225860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118895480877634331045517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5491860641170179108060689 4118895480877634331045517)
  ·
    refine ⟨1544585805329112874142069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4118895480877634331045517 1544585805329112874142069)
    ·
      refine ⟨144804919249604331950819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1544585805329112874142069 144804919249604331950819)
      ·
        refine ⟨217207378874406497926229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144804919249604331950819 217207378874406497926229)
        ·
          refine ⟨2545398971184451147573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 217207378874406497926229 2545398971184451147573)
          ·
            rfl

theorem cell19_225860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_225860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225860 prefixEnd_225860 := by exact prefixLift 225860
  have htrace : WordTrace (prefixWord ++ tailWord_225860) baseStart_225860 baseEnd_225860 := by
    simpa [prefixWord, tailWord_225860, baseEnd_225860] using wordTrace_append hprefix tailTrace_225860
  have hstable : (prefixWord ++ tailWord_225860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225860).length < 2 ^ (prefixWord ++ tailWord_225860).sum := by decide
  have hdescent : baseEnd_225860 < baseStart_225860 := by decide
  rcases family_descends (prefixWord ++ tailWord_225860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225921 : List Nat := [1, 2, 4, 2, 1, 1, 8]
def baseStart_225921 : Nat := 118140960795 + 225921 * 2 ^ 59
def prefixEnd_225921 : Nat := 4983230072969 + 3 ^ 40 * 225921 * 2
def baseEnd_225921 : Nat := 22914777865583371209583

theorem tailTrace_225921 : CollatzResearch.WordTrace tailWord_225921 prefixEnd_225921 22914777865583371209583 := by
  unfold tailWord_225921
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240015814534276080061617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5493343876356184053374411 8240015814534276080061617)
  ·
    refine ⟨6180011860900707060046213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8240015814534276080061617 6180011860900707060046213)
    ·
      refine ⟨1158752223918882573758665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6180011860900707060046213 1158752223918882573758665)
      ·
        refine ⟨869064167939161930318999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158752223918882573758665 869064167939161930318999)
        ·
          refine ⟨1303596251908742895478499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869064167939161930318999 1303596251908742895478499)
          ·
            refine ⟨1955394377863114343217749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303596251908742895478499 1955394377863114343217749)
            ·
              refine ⟨22914777865583371209583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1955394377863114343217749 22914777865583371209583)
              ·
                rfl

theorem cell19_225921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_225921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225921 prefixEnd_225921 := by exact prefixLift 225921
  have htrace : WordTrace (prefixWord ++ tailWord_225921) baseStart_225921 baseEnd_225921 := by
    simpa [prefixWord, tailWord_225921, baseEnd_225921] using wordTrace_append hprefix tailTrace_225921
  have hstable : (prefixWord ++ tailWord_225921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225921).length < 2 ^ (prefixWord ++ tailWord_225921).sum := by decide
  have hdescent : baseEnd_225921 < baseStart_225921 := by decide
  rcases family_descends (prefixWord ++ tailWord_225921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225953 : List Nat := [1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_225953 : Nat := 118140960795 + 225953 * 2 ^ 59
def prefixEnd_225953 : Nat := 4983230072969 + 3 ^ 40 * 225953 * 2
def baseEnd_225953 : Nat := 68754070711383520917551

theorem tailTrace_225953 : CollatzResearch.WordTrace tailWord_225953 prefixEnd_225953 68754070711383520917551 := by
  unfold tailWord_225953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241182950418345545226513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5494121966945563696817675 8241182950418345545226513)
  ·
    refine ⟨6180887212813759158919885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8241182950418345545226513 6180887212813759158919885)
    ·
      refine ⟨2317832704805159684594957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6180887212813759158919885 2317832704805159684594957)
      ·
        refine ⟨869187264301934881723109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2317832704805159684594957 869187264301934881723109)
        ·
          refine ⟨162972612056612790323083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 869187264301934881723109 162972612056612790323083)
          ·
            refine ⟨244458918084919185484625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162972612056612790323083 244458918084919185484625)
            ·
              refine ⟨183344188563689389113469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244458918084919185484625 183344188563689389113469)
              ·
                refine ⟨68754070711383520917551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183344188563689389113469 68754070711383520917551)
                ·
                  rfl

theorem cell19_225953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_225953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_225953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_225953 prefixEnd_225953 := by exact prefixLift 225953
  have htrace : WordTrace (prefixWord ++ tailWord_225953) baseStart_225953 baseEnd_225953 := by
    simpa [prefixWord, tailWord_225953, baseEnd_225953] using wordTrace_append hprefix tailTrace_225953
  have hstable : (prefixWord ++ tailWord_225953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225953).length < 2 ^ (prefixWord ++ tailWord_225953).sum := by decide
  have hdescent : baseEnd_225953 < baseStart_225953 := by decide
  rcases family_descends (prefixWord ++ tailWord_225953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226050 : List Nat := [3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_226050 : Nat := 118140960795 + 226050 * 2 ^ 59
def prefixEnd_226050 : Nat := 4983230072969 + 3 ^ 40 * 226050 * 2
def baseEnd_226050 : Nat := 68783586340116036761731

theorem tailTrace_226050 : CollatzResearch.WordTrace tailWord_226050 prefixEnd_226050 68783586340116036761731 := by
  unfold tailWord_226050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061180207766732777876901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5496480554044620741005069 2061180207766732777876901)
  ·
    refine ⟨386471288956262395851919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2061180207766732777876901 386471288956262395851919)
    ·
      refine ⟨579706933434393593777879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386471288956262395851919 579706933434393593777879)
      ·
        refine ⟨869560400151590390666819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579706933434393593777879 869560400151590390666819)
        ·
          refine ⟨1304340600227385586000229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869560400151590390666819 1304340600227385586000229)
          ·
            refine ⟨244563862542634797375043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1304340600227385586000229 244563862542634797375043)
            ·
              refine ⟨366845793813952196062565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244563862542634797375043 366845793813952196062565)
              ·
                refine ⟨68783586340116036761731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366845793813952196062565 68783586340116036761731)
                ·
                  rfl

theorem cell19_226050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_226050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226050 prefixEnd_226050 := by exact prefixLift 226050
  have htrace : WordTrace (prefixWord ++ tailWord_226050) baseStart_226050 baseEnd_226050 := by
    simpa [prefixWord, tailWord_226050, baseEnd_226050] using wordTrace_append hprefix tailTrace_226050
  have hstable : (prefixWord ++ tailWord_226050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226050).length < 2 ^ (prefixWord ++ tailWord_226050).sum := by decide
  have hdescent : baseEnd_226050 < baseStart_226050 := by decide
  rcases family_descends (prefixWord ++ tailWord_226050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226130 : List Nat := [3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_226130 : Nat := 118140960795 + 226130 * 2 ^ 59
def prefixEnd_226130 : Nat := 4983230072969 + 3 ^ 40 * 226130 * 2
def baseEnd_226130 : Nat := 68807929126699554983735

theorem tailTrace_226130 : CollatzResearch.WordTrace tailWord_226130 prefixEnd_226130 68807929126699554983735 := by
  unfold tailWord_226130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061909667694276193604961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5498425780518069849613229 2061909667694276193604961)
  ·
    refine ⟨1546432250770707145203721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2061909667694276193604961 1546432250770707145203721)
    ·
      refine ⟨1159824188078030358902791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546432250770707145203721 1159824188078030358902791)
      ·
        refine ⟨1739736282117045538354187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159824188078030358902791 1739736282117045538354187)
        ·
          refine ⟨2609604423175568307531281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739736282117045538354187 2609604423175568307531281)
          ·
            refine ⟨1957203317381676230648461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609604423175568307531281 1957203317381676230648461)
            ·
              refine ⟨733951244018128586493173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957203317381676230648461 733951244018128586493173)
              ·
                refine ⟨68807929126699554983735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733951244018128586493173 68807929126699554983735)
                ·
                  rfl

theorem cell19_226130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_226130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226130 prefixEnd_226130 := by exact prefixLift 226130
  have htrace : WordTrace (prefixWord ++ tailWord_226130) baseStart_226130 baseEnd_226130 := by
    simpa [prefixWord, tailWord_226130, baseEnd_226130] using wordTrace_append hprefix tailTrace_226130
  have hstable : (prefixWord ++ tailWord_226130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226130).length < 2 ^ (prefixWord ++ tailWord_226130).sum := by decide
  have hdescent : baseEnd_226130 < baseStart_226130 := by decide
  rcases family_descends (prefixWord ++ tailWord_226130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226166 : List Nat := [5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_226166 : Nat := 118140960795 + 226166 * 2 ^ 59
def prefixEnd_226166 : Nat := 4983230072969 + 3 ^ 40 * 226166 * 2
def baseEnd_226166 : Nat := 68818883380662138183637

theorem tailTrace_226166 : CollatzResearch.WordTrace tailWord_226166 prefixEnd_226166 68818883380662138183637 := by
  unfold tailWord_226166
  simp only [CollatzResearch.WordTrace]
  refine ⟨515559481165417682670647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5499301132431121948486901 515559481165417682670647)
  ·
    refine ⟨773339221748126524005971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 515559481165417682670647 773339221748126524005971)
    ·
      refine ⟨1160008832622189786008957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773339221748126524005971 1160008832622189786008957)
      ·
        refine ⟨435003312233321169753359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1160008832622189786008957 435003312233321169753359)
        ·
          refine ⟨652504968349981754630039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435003312233321169753359 652504968349981754630039)
          ·
            refine ⟨978757452524972631945059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652504968349981754630039 978757452524972631945059)
            ·
              refine ⟨1468136178787458947917589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978757452524972631945059 1468136178787458947917589)
              ·
                refine ⟨68818883380662138183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1468136178787458947917589 68818883380662138183637)
                ·
                  rfl

theorem cell19_226166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_226166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226166 prefixEnd_226166 := by exact prefixLift 226166
  have htrace : WordTrace (prefixWord ++ tailWord_226166) baseStart_226166 baseEnd_226166 := by
    simpa [prefixWord, tailWord_226166, baseEnd_226166] using wordTrace_append hprefix tailTrace_226166
  have hstable : (prefixWord ++ tailWord_226166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226166).length < 2 ^ (prefixWord ++ tailWord_226166).sum := by decide
  have hdescent : baseEnd_226166 < baseStart_226166 := by decide
  rcases family_descends (prefixWord ++ tailWord_226166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226204 : List Nat := [2, 2, 3, 3, 3, 6]
def baseStart_226204 : Nat := 118140960795 + 226204 * 2 ^ 59
def prefixEnd_226204 : Nat := 4983230072969 + 3 ^ 40 * 226204 * 2
def baseEnd_226204 : Nat := 7647827356032145482121

theorem tailTrace_226204 : CollatzResearch.WordTrace tailWord_226204 prefixEnd_226204 7647827356032145482121 := by
  unfold tailWord_226204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125168836254507706306833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5500225115006010275075777 4125168836254507706306833)
  ·
    refine ⟨3093876627190880779730125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4125168836254507706306833 3093876627190880779730125)
    ·
      refine ⟨1160203735196580292398797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3093876627190880779730125 1160203735196580292398797)
      ·
        refine ⟨435076400698717609649549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1160203735196580292398797 435076400698717609649549)
        ·
          refine ⟨163153650262019103618581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435076400698717609649549 163153650262019103618581)
          ·
            refine ⟨7647827356032145482121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163153650262019103618581 7647827356032145482121)
            ·
              rfl

theorem cell19_226204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_226204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226204 prefixEnd_226204 := by exact prefixLift 226204
  have htrace : WordTrace (prefixWord ++ tailWord_226204) baseStart_226204 baseEnd_226204 := by
    simpa [prefixWord, tailWord_226204, baseEnd_226204] using wordTrace_append hprefix tailTrace_226204
  have hstable : (prefixWord ++ tailWord_226204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226204).length < 2 ^ (prefixWord ++ tailWord_226204).sum := by decide
  have hdescent : baseEnd_226204 < baseStart_226204 := by decide
  rcases family_descends (prefixWord ++ tailWord_226204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226206 : List Nat := [4, 3, 1, 11]
def baseStart_226206 : Nat := 118140960795 + 226206 * 2 ^ 59
def prefixEnd_226206 : Nat := 4983230072969 + 3 ^ 40 * 226206 * 2
def baseEnd_226206 : Nat := 849766108320418485119

theorem tailTrace_226206 : CollatzResearch.WordTrace tailWord_226206 prefixEnd_226206 849766108320418485119 := by
  unfold tailWord_226206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031301327312721219273309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5500273745667846502790981 1031301327312721219273309)
  ·
    refine ⟨386737997742270457227491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1031301327312721219273309 386737997742270457227491)
    ·
      refine ⟨580106996613405685841237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386737997742270457227491 580106996613405685841237)
      ·
        refine ⟨849766108320418485119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 580106996613405685841237 849766108320418485119)
        ·
          rfl

theorem cell19_226206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 11].length) (baseStart_226206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226206 prefixEnd_226206 := by exact prefixLift 226206
  have htrace : WordTrace (prefixWord ++ tailWord_226206) baseStart_226206 baseEnd_226206 := by
    simpa [prefixWord, tailWord_226206, baseEnd_226206] using wordTrace_append hprefix tailTrace_226206
  have hstable : (prefixWord ++ tailWord_226206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226206).length < 2 ^ (prefixWord ++ tailWord_226206).sum := by decide
  have hdescent : baseEnd_226206 < baseStart_226206 := by decide
  rcases family_descends (prefixWord ++ tailWord_226206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226227 : List Nat := [1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_226227 : Nat := 118140960795 + 226227 * 2 ^ 59
def prefixEnd_226227 : Nat := 4983230072969 + 3 ^ 40 * 226227 * 2
def baseEnd_226227 : Nat := 68837444755432070827915

theorem tailTrace_226227 : CollatzResearch.WordTrace tailWord_226227 prefixEnd_226227 68837444755432070827915 := by
  unfold tailWord_226227
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251176551425690340700935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5500784367617126893800623 8251176551425690340700935)
  ·
    refine ⟨12376764827138535511051403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251176551425690340700935 12376764827138535511051403)
    ·
      refine ⟨18565147240707803266577105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376764827138535511051403 18565147240707803266577105)
      ·
        refine ⟨13923860430530852449932829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18565147240707803266577105 13923860430530852449932829)
        ·
          refine ⟨5221447661449069668724811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13923860430530852449932829 5221447661449069668724811)
          ·
            refine ⟨7832171492173604503087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221447661449069668724811 7832171492173604503087217)
            ·
              refine ⟨5874128619130203377315413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832171492173604503087217 5874128619130203377315413)
              ·
                refine ⟨68837444755432070827915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5874128619130203377315413 68837444755432070827915)
                ·
                  rfl

theorem cell19_226227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_226227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226227 prefixEnd_226227 := by exact prefixLift 226227
  have htrace : WordTrace (prefixWord ++ tailWord_226227) baseStart_226227 baseEnd_226227 := by
    simpa [prefixWord, tailWord_226227, baseEnd_226227] using wordTrace_append hprefix tailTrace_226227
  have hstable : (prefixWord ++ tailWord_226227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226227).length < 2 ^ (prefixWord ++ tailWord_226227).sum := by decide
  have hdescent : baseEnd_226227 < baseStart_226227 := by decide
  rcases family_descends (prefixWord ++ tailWord_226227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226293 : List Nat := [1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_226293 : Nat := 118140960795 + 226293 * 2 ^ 59
def prefixEnd_226293 : Nat := 4983230072969 + 3 ^ 40 * 226293 * 2
def baseEnd_226293 : Nat := 68857527554363473361069

theorem tailTrace_226293 : CollatzResearch.WordTrace tailWord_226293 prefixEnd_226293 68857527554363473361069 := by
  unfold tailWord_226293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8253583769186583612603533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5502389179457722408402355 8253583769186583612603533)
  ·
    refine ⟨3095093913444968854726325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8253583769186583612603533 3095093913444968854726325)
    ·
      refine ⟨290165054385465830130593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3095093913444968854726325 290165054385465830130593)
      ·
        refine ⟨217623790789099372597945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290165054385465830130593 217623790789099372597945)
        ·
          refine ⟨163217843091824529448459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217623790789099372597945 163217843091824529448459)
          ·
            refine ⟨244826764637736794172689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163217843091824529448459 244826764637736794172689)
            ·
              refine ⟨183620073478302595629517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244826764637736794172689 183620073478302595629517)
              ·
                refine ⟨68857527554363473361069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183620073478302595629517 68857527554363473361069)
                ·
                  rfl

theorem cell19_226293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_226293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226293 prefixEnd_226293 := by exact prefixLift 226293
  have htrace : WordTrace (prefixWord ++ tailWord_226293) baseStart_226293 baseEnd_226293 := by
    simpa [prefixWord, tailWord_226293, baseEnd_226293] using wordTrace_append hprefix tailTrace_226293
  have hstable : (prefixWord ++ tailWord_226293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226293).length < 2 ^ (prefixWord ++ tailWord_226293).sum := by decide
  have hdescent : baseEnd_226293 < baseStart_226293 := by decide
  rcases family_descends (prefixWord ++ tailWord_226293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226339 : List Nat := [1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_226339 : Nat := 118140960795 + 226339 * 2 ^ 59
def prefixEnd_226339 : Nat := 4983230072969 + 3 ^ 40 * 226339 * 2
def baseEnd_226339 : Nat := 68871524656648996338721

theorem tailTrace_226339 : CollatzResearch.WordTrace tailWord_226339 prefixEnd_226339 68871524656648996338721 := by
  unfold tailWord_226339
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255261527019933468778071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5503507684679955645852047 8255261527019933468778071)
  ·
    refine ⟨12382892290529900203167107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8255261527019933468778071 12382892290529900203167107)
    ·
      refine ⟨18574338435794850304750661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382892290529900203167107 18574338435794850304750661)
      ·
        refine ⟨3482688456711534432140749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18574338435794850304750661 3482688456711534432140749)
        ·
          refine ⟨1306008171266825412052781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3482688456711534432140749 1306008171266825412052781)
          ·
            refine ⟨489753064225059529519793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1306008171266825412052781 489753064225059529519793)
            ·
              refine ⟨367314798168794647139845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489753064225059529519793 367314798168794647139845)
              ·
                refine ⟨68871524656648996338721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367314798168794647139845 68871524656648996338721)
                ·
                  rfl

theorem cell19_226339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_226339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226339 prefixEnd_226339 := by exact prefixLift 226339
  have htrace : WordTrace (prefixWord ++ tailWord_226339) baseStart_226339 baseEnd_226339 := by
    simpa [prefixWord, tailWord_226339, baseEnd_226339] using wordTrace_append hprefix tailTrace_226339
  have hstable : (prefixWord ++ tailWord_226339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226339).length < 2 ^ (prefixWord ++ tailWord_226339).sum := by decide
  have hdescent : baseEnd_226339 < baseStart_226339 := by decide
  rcases family_descends (prefixWord ++ tailWord_226339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226356 : List Nat := [2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_226356 : Nat := 118140960795 + 226356 * 2 ^ 59
def prefixEnd_226356 : Nat := 4983230072969 + 3 ^ 40 * 226356 * 2
def baseEnd_226356 : Nat := 68876697498797993960897

theorem tailTrace_226356 : CollatzResearch.WordTrace tailWord_226356 prefixEnd_226356 68876697498797993960897 := by
  unfold tailWord_226356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127940783979172686073461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5503921045305563581431281 4127940783979172686073461)
  ·
    refine ⟨386994448498047439319387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4127940783979172686073461 386994448498047439319387)
    ·
      refine ⟨580491672747071158979081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386994448498047439319387 580491672747071158979081)
      ·
        refine ⟨435368754560303369234311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580491672747071158979081 435368754560303369234311)
        ·
          refine ⟨653053131840455053851467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435368754560303369234311 653053131840455053851467)
          ·
            refine ⟨979579697760682580777201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653053131840455053851467 979579697760682580777201)
            ·
              refine ⟨734684773320511935582901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979579697760682580777201 734684773320511935582901)
              ·
                refine ⟨68876697498797993960897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 734684773320511935582901 68876697498797993960897)
                ·
                  rfl

theorem cell19_226356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_226356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226356 prefixEnd_226356 := by exact prefixLift 226356
  have htrace : WordTrace (prefixWord ++ tailWord_226356) baseStart_226356 baseEnd_226356 := by
    simpa [prefixWord, tailWord_226356, baseEnd_226356] using wordTrace_append hprefix tailTrace_226356
  have hstable : (prefixWord ++ tailWord_226356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226356).length < 2 ^ (prefixWord ++ tailWord_226356).sum := by decide
  have hdescent : baseEnd_226356 < baseStart_226356 := by decide
  rcases family_descends (prefixWord ++ tailWord_226356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226390 : List Nat := [5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_226390 : Nat := 118140960795 + 226390 * 2 ^ 59
def prefixEnd_226390 : Nat := 4983230072969 + 3 ^ 40 * 226390 * 2
def baseEnd_226390 : Nat := 68887043183095989205249

theorem tailTrace_226390 : CollatzResearch.WordTrace tailWord_226390 prefixEnd_226390 68887043183095989205249 := by
  unfold tailWord_226390
  simp only [CollatzResearch.WordTrace]
  refine ⟨516070103114698073680289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5504747766556779452589749 516070103114698073680289)
  ·
    refine ⟨387052577336023555260217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 516070103114698073680289 387052577336023555260217)
    ·
      refine ⟨290289433002017666445163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387052577336023555260217 290289433002017666445163)
      ·
        refine ⟨435434149503026499667745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290289433002017666445163 435434149503026499667745)
        ·
          refine ⟨326575612127269874750809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435434149503026499667745 326575612127269874750809)
          ·
            refine ⟨244931709095452406063107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326575612127269874750809 244931709095452406063107)
            ·
              refine ⟨367397563643178609094661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244931709095452406063107 367397563643178609094661)
              ·
                refine ⟨68887043183095989205249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367397563643178609094661 68887043183095989205249)
                ·
                  rfl

theorem cell19_226390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_226390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226390 prefixEnd_226390 := by exact prefixLift 226390
  have htrace : WordTrace (prefixWord ++ tailWord_226390) baseStart_226390 baseEnd_226390 := by
    simpa [prefixWord, tailWord_226390, baseEnd_226390] using wordTrace_append hprefix tailTrace_226390
  have hstable : (prefixWord ++ tailWord_226390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226390).length < 2 ^ (prefixWord ++ tailWord_226390).sum := by decide
  have hdescent : baseEnd_226390 < baseStart_226390 := by decide
  rcases family_descends (prefixWord ++ tailWord_226390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226413 : List Nat := [1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_226413 : Nat := 118140960795 + 226413 * 2 ^ 59
def prefixEnd_226413 : Nat := 4983230072969 + 3 ^ 40 * 226413 * 2
def baseEnd_226413 : Nat := 68894041734238750694075

theorem tailTrace_226413 : CollatzResearch.WordTrace tailWord_226413 prefixEnd_226413 68894041734238750694075 := by
  unfold tailWord_226413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257960528751844106971893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505307019167896071314595 8257960528751844106971893)
  ·
    refine ⟨774183799570485385028615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8257960528751844106971893 774183799570485385028615)
    ·
      refine ⟨1161275699355728077542923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774183799570485385028615 1161275699355728077542923)
      ·
        refine ⟨1741913549033592116314385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161275699355728077542923 1741913549033592116314385)
        ·
          refine ⟨1306435161775194087235789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741913549033592116314385 1306435161775194087235789)
          ·
            refine ⟨489913185665697782713421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1306435161775194087235789 489913185665697782713421)
            ·
              refine ⟨183717444624636668517533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 489913185665697782713421 183717444624636668517533)
              ·
                refine ⟨68894041734238750694075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183717444624636668517533 68894041734238750694075)
                ·
                  rfl

theorem cell19_226413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_226413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226413 prefixEnd_226413 := by exact prefixLift 226413
  have htrace : WordTrace (prefixWord ++ tailWord_226413) baseStart_226413 baseEnd_226413 := by
    simpa [prefixWord, tailWord_226413, baseEnd_226413] using wordTrace_append hprefix tailTrace_226413
  have hstable : (prefixWord ++ tailWord_226413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226413).length < 2 ^ (prefixWord ++ tailWord_226413).sum := by decide
  have hdescent : baseEnd_226413 < baseStart_226413 := by decide
  rcases family_descends (prefixWord ++ tailWord_226413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226415 : List Nat := [1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_226415 : Nat := 118140960795 + 226415 * 2 ^ 59
def prefixEnd_226415 : Nat := 4983230072969 + 3 ^ 40 * 226415 * 2
def baseEnd_226415 : Nat := 68894650303903338649625

theorem tailTrace_226415 : CollatzResearch.WordTrace tailWord_226415 prefixEnd_226415 68894650303903338649625 := by
  unfold tailWord_226415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258033474744598448544699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5505355649829732299029799 8258033474744598448544699)
  ·
    refine ⟨12387050212116897672817049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8258033474744598448544699 12387050212116897672817049)
    ·
      refine ⟨9290287659087673254612787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12387050212116897672817049 9290287659087673254612787)
      ·
        refine ⟨13935431488631509881919181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9290287659087673254612787 13935431488631509881919181)
        ·
          refine ⟨5225786808236816205719693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13935431488631509881919181 5225786808236816205719693)
          ·
            refine ⟨1959670053088806077144885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5225786808236816205719693 1959670053088806077144885)
            ·
              refine ⟨183719067477075569732333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1959670053088806077144885 183719067477075569732333)
              ·
                refine ⟨68894650303903338649625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183719067477075569732333 68894650303903338649625)
                ·
                  rfl

theorem cell19_226415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_226415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226415 prefixEnd_226415 := by exact prefixLift 226415
  have htrace : WordTrace (prefixWord ++ tailWord_226415) baseStart_226415 baseEnd_226415 := by
    simpa [prefixWord, tailWord_226415, baseEnd_226415] using wordTrace_append hprefix tailTrace_226415
  have hstable : (prefixWord ++ tailWord_226415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226415).length < 2 ^ (prefixWord ++ tailWord_226415).sum := by decide
  have hdescent : baseEnd_226415 < baseStart_226415 := by decide
  rcases family_descends (prefixWord ++ tailWord_226415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226466 : List Nat := [3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_226466 : Nat := 118140960795 + 226466 * 2 ^ 59
def prefixEnd_226466 : Nat := 4983230072969 + 3 ^ 40 * 226466 * 2
def baseEnd_226466 : Nat := 68910168830350331516153

theorem tailTrace_226466 : CollatzResearch.WordTrace tailWord_226466 prefixEnd_226466 68910168830350331516153 := by
  unfold tailWord_226466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064973399389958539662813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5506595731706556105767501 2064973399389958539662813)
  ·
    refine ⟨774365024771234452373555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2064973399389958539662813 774365024771234452373555)
    ·
      refine ⟨1161547537156851678560333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774365024771234452373555 1161547537156851678560333)
      ·
        refine ⟨435580326433819379460125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1161547537156851678560333 435580326433819379460125)
        ·
          refine ⟨163342622412682267297547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435580326433819379460125 163342622412682267297547)
          ·
            refine ⟨245013933619023400946321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163342622412682267297547 245013933619023400946321)
            ·
              refine ⟨183760450214267550709741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245013933619023400946321 183760450214267550709741)
              ·
                refine ⟨68910168830350331516153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183760450214267550709741 68910168830350331516153)
                ·
                  rfl

theorem cell19_226466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_226466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226466 prefixEnd_226466 := by exact prefixLift 226466
  have htrace : WordTrace (prefixWord ++ tailWord_226466) baseStart_226466 baseEnd_226466 := by
    simpa [prefixWord, tailWord_226466, baseEnd_226466] using wordTrace_append hprefix tailTrace_226466
  have hstable : (prefixWord ++ tailWord_226466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226466).length < 2 ^ (prefixWord ++ tailWord_226466).sum := by decide
  have hdescent : baseEnd_226466 < baseStart_226466 := by decide
  rcases family_descends (prefixWord ++ tailWord_226466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226493 : List Nat := [1, 4, 1, 2, 1, 1, 9]
def baseStart_226493 : Nat := 118140960795 + 226493 * 2 ^ 59
def prefixEnd_226493 : Nat := 4983230072969 + 3 ^ 40 * 226493 * 2
def baseEnd_226493 : Nat := 22972794840274089638693

theorem tailTrace_226493 : CollatzResearch.WordTrace tailWord_226493 prefixEnd_226493 22972794840274089638693 := by
  unfold tailWord_226493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260878368462017769884133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5507252245641345179922755 8260878368462017769884133)
  ·
    refine ⟨1548914694086628331853275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8260878368462017769884133 1548914694086628331853275)
    ·
      refine ⟨2323372041129942497779913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548914694086628331853275 2323372041129942497779913)
      ·
        refine ⟨1742529030847456873334935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2323372041129942497779913 1742529030847456873334935)
        ·
          refine ⟨2613793546271185310002403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742529030847456873334935 2613793546271185310002403)
          ·
            refine ⟨3920690319406777965003605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613793546271185310002403 3920690319406777965003605)
            ·
              refine ⟨22972794840274089638693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3920690319406777965003605 22972794840274089638693)
              ·
                rfl

theorem cell19_226493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_226493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226493 prefixEnd_226493 := by exact prefixLift 226493
  have htrace : WordTrace (prefixWord ++ tailWord_226493) baseStart_226493 baseEnd_226493 := by
    simpa [prefixWord, tailWord_226493, baseEnd_226493] using wordTrace_append hprefix tailTrace_226493
  have hstable : (prefixWord ++ tailWord_226493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226493).length < 2 ^ (prefixWord ++ tailWord_226493).sum := by decide
  have hdescent : baseEnd_226493 < baseStart_226493 := by decide
  rcases family_descends (prefixWord ++ tailWord_226493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226588 : List Nat := [2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_226588 : Nat := 118140960795 + 226588 * 2 ^ 59
def prefixEnd_226588 : Nat := 4983230072969 + 3 ^ 40 * 226588 * 2
def baseEnd_226588 : Nat := 68947291579890196804709

theorem tailTrace_226588 : CollatzResearch.WordTrace tailWord_226588 prefixEnd_226588 68947291579890196804709 := by
  unfold tailWord_226588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132171651558924497296209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5509562202078565996394945 4132171651558924497296209)
  ·
    refine ⟨3099128738669193372972157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4132171651558924497296209 3099128738669193372972157)
    ·
      refine ⟨1162173277000947514864559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3099128738669193372972157 1162173277000947514864559)
      ·
        refine ⟨1743259915501421272296839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162173277000947514864559 1743259915501421272296839)
        ·
          refine ⟨2614889873252131908445259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743259915501421272296839 2614889873252131908445259)
          ·
            refine ⟨3922334809878197862667889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614889873252131908445259 3922334809878197862667889)
            ·
              refine ⟨2941751107408648397000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922334809878197862667889 2941751107408648397000917)
              ·
                refine ⟨68947291579890196804709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2941751107408648397000917 68947291579890196804709)
                ·
                  rfl

theorem cell19_226588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_226588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226588 prefixEnd_226588 := by exact prefixLift 226588
  have htrace : WordTrace (prefixWord ++ tailWord_226588) baseStart_226588 baseEnd_226588 := by
    simpa [prefixWord, tailWord_226588, baseEnd_226588] using wordTrace_append hprefix tailTrace_226588
  have hstable : (prefixWord ++ tailWord_226588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226588).length < 2 ^ (prefixWord ++ tailWord_226588).sum := by decide
  have hdescent : baseEnd_226588 < baseStart_226588 := by decide
  rcases family_descends (prefixWord ++ tailWord_226588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226637 : List Nat := [1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_226637 : Nat := 118140960795 + 226637 * 2 ^ 59
def prefixEnd_226637 : Nat := 4983230072969 + 3 ^ 40 * 226637 * 2
def baseEnd_226637 : Nat := 68962201536672601715687

theorem tailTrace_226637 : CollatzResearch.WordTrace tailWord_226637 prefixEnd_226637 68962201536672601715687 := by
  unfold tailWord_226637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266130479940330363126165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5510753653293553575417443 8266130479940330363126165)
  ·
    refine ⟨387474866247202985771539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8266130479940330363126165 387474866247202985771539)
    ·
      refine ⟨581212299370804478657309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387474866247202985771539 581212299370804478657309)
      ·
        refine ⟨217954612264051679496491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581212299370804478657309 217954612264051679496491)
        ·
          refine ⟨326931918396077519244737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217954612264051679496491 326931918396077519244737)
          ·
            refine ⟨245198938797058139433553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326931918396077519244737 245198938797058139433553)
            ·
              refine ⟨183899204097793604575165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245198938797058139433553 183899204097793604575165)
              ·
                refine ⟨68962201536672601715687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183899204097793604575165 68962201536672601715687)
                ·
                  rfl

theorem cell19_226637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_226637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226637 prefixEnd_226637 := by exact prefixLift 226637
  have htrace : WordTrace (prefixWord ++ tailWord_226637) baseStart_226637 baseEnd_226637 := by
    simpa [prefixWord, tailWord_226637, baseEnd_226637] using wordTrace_append hprefix tailTrace_226637
  have hstable : (prefixWord ++ tailWord_226637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226637).length < 2 ^ (prefixWord ++ tailWord_226637).sum := by decide
  have hdescent : baseEnd_226637 < baseStart_226637 := by decide
  rcases family_descends (prefixWord ++ tailWord_226637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226683 : List Nat := [1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_226683 : Nat := 118140960795 + 226683 * 2 ^ 59
def prefixEnd_226683 : Nat := 4983230072969 + 3 ^ 40 * 226683 * 2
def baseEnd_226683 : Nat := 68976198638958124693339

theorem tailTrace_226683 : CollatzResearch.WordTrace tailWord_226683 prefixEnd_226683 68976198638958124693339 := by
  unfold tailWord_226683
  simp only [CollatzResearch.WordTrace]
  refine ⟨8267808237773680219300703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5511872158515786812867135 8267808237773680219300703)
  ·
    refine ⟨12401712356660520328951055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8267808237773680219300703 12401712356660520328951055)
    ·
      refine ⟨18602568534990780493426583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12401712356660520328951055 18602568534990780493426583)
      ·
        refine ⟨27903852802486170740139875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18602568534990780493426583 27903852802486170740139875)
        ·
          refine ⟨41855779203729256110209813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27903852802486170740139875 41855779203729256110209813)
          ·
            refine ⟨1961989650174808880166085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41855779203729256110209813 1961989650174808880166085)
            ·
              refine ⟨367873059407776665031141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1961989650174808880166085 367873059407776665031141)
              ·
                refine ⟨68976198638958124693339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367873059407776665031141 68976198638958124693339)
                ·
                  rfl

theorem cell19_226683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_226683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226683 prefixEnd_226683 := by exact prefixLift 226683
  have htrace : WordTrace (prefixWord ++ tailWord_226683) baseStart_226683 baseEnd_226683 := by
    simpa [prefixWord, tailWord_226683, baseEnd_226683] using wordTrace_append hprefix tailTrace_226683
  have hstable : (prefixWord ++ tailWord_226683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226683).length < 2 ^ (prefixWord ++ tailWord_226683).sum := by decide
  have hdescent : baseEnd_226683 < baseStart_226683 := by decide
  rcases family_descends (prefixWord ++ tailWord_226683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226778 : List Nat := [3, 1, 1, 2, 3, 3, 6]
def baseStart_226778 : Nat := 118140960795 + 226778 * 2 ^ 59
def prefixEnd_226778 : Nat := 4983230072969 + 3 ^ 40 * 226778 * 2
def baseEnd_226778 : Nat := 23001701899342017527323

theorem tailTrace_226778 : CollatzResearch.WordTrace tailWord_226778 prefixEnd_226778 23001701899342017527323 := by
  unfold tailWord_226778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067818293107377861002247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5514182114953007629339325 2067818293107377861002247)
  ·
    refine ⟨3101727439661066791503371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067818293107377861002247 3101727439661066791503371)
    ·
      refine ⟨4652591159491600187255057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101727439661066791503371 4652591159491600187255057)
      ·
        refine ⟨3489443369618700140441293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4652591159491600187255057 3489443369618700140441293)
        ·
          refine ⟨1308541263607012552665485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3489443369618700140441293 1308541263607012552665485)
          ·
            refine ⟨490702973852629707249557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1308541263607012552665485 490702973852629707249557)
            ·
              refine ⟨23001701899342017527323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 490702973852629707249557 23001701899342017527323)
              ·
                rfl

theorem cell19_226778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_226778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226778 prefixEnd_226778 := by exact prefixLift 226778
  have htrace : WordTrace (prefixWord ++ tailWord_226778) baseStart_226778 baseEnd_226778 := by
    simpa [prefixWord, tailWord_226778, baseEnd_226778] using wordTrace_append hprefix tailTrace_226778
  have hstable : (prefixWord ++ tailWord_226778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226778).length < 2 ^ (prefixWord ++ tailWord_226778).sum := by decide
  have hdescent : baseEnd_226778 < baseStart_226778 := by decide
  rcases family_descends (prefixWord ++ tailWord_226778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226829 : List Nat := [1, 7, 1, 1, 2, 2, 5]
def baseStart_226829 : Nat := 118140960795 + 226829 * 2 ^ 59
def prefixEnd_226829 : Nat := 4983230072969 + 3 ^ 40 * 226829 * 2
def baseEnd_226829 : Nat := 23006874741491015149499

theorem tailTrace_226829 : CollatzResearch.WordTrace tailWord_226829 prefixEnd_226829 23006874741491015149499 := by
  unfold tailWord_226829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273133295244747154115541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5515422196829831436077027 8273133295244747154115541)
  ·
    refine ⟨193901561607298761424583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8273133295244747154115541 193901561607298761424583)
    ·
      refine ⟨290852342410948142136875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193901561607298761424583 290852342410948142136875)
      ·
        refine ⟨436278513616422213205313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290852342410948142136875 436278513616422213205313)
        ·
          refine ⟨327208885212316659903985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436278513616422213205313 327208885212316659903985)
          ·
            refine ⟨245406663909237494927989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327208885212316659903985 245406663909237494927989)
            ·
              refine ⟨23006874741491015149499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245406663909237494927989 23006874741491015149499)
              ·
                rfl

theorem cell19_226829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_226829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226829 prefixEnd_226829 := by exact prefixLift 226829
  have htrace : WordTrace (prefixWord ++ tailWord_226829) baseStart_226829 baseEnd_226829 := by
    simpa [prefixWord, tailWord_226829, baseEnd_226829] using wordTrace_append hprefix tailTrace_226829
  have hstable : (prefixWord ++ tailWord_226829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226829).length < 2 ^ (prefixWord ++ tailWord_226829).sum := by decide
  have hdescent : baseEnd_226829 < baseStart_226829 := by decide
  rcases family_descends (prefixWord ++ tailWord_226829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226835 : List Nat := [1, 1, 1, 2, 1, 8, 5]
def baseStart_226835 : Nat := 118140960795 + 226835 * 2 ^ 59
def prefixEnd_226835 : Nat := 4983230072969 + 3 ^ 40 * 226835 * 2
def baseEnd_226835 : Nat := 23007483311155603105049

theorem tailTrace_226835 : CollatzResearch.WordTrace tailWord_226835 prefixEnd_226835 23007483311155603105049 := by
  unfold tailWord_226835
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273352133223010178833959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5515568088815340119222639 8273352133223010178833959)
  ·
    refine ⟨12410028199834515268250939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8273352133223010178833959 12410028199834515268250939)
    ·
      refine ⟨18615042299751772902376409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12410028199834515268250939 18615042299751772902376409)
      ·
        refine ⟨13961281724813829676782307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18615042299751772902376409 13961281724813829676782307)
        ·
          refine ⟨20941922587220744515173461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961281724813829676782307 20941922587220744515173461)
          ·
            refine ⟨245413155318993099787189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 20941922587220744515173461 245413155318993099787189)
            ·
              refine ⟨23007483311155603105049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245413155318993099787189 23007483311155603105049)
              ·
                rfl

theorem cell19_226835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_226835 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226835 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226835 prefixEnd_226835 := by exact prefixLift 226835
  have htrace : WordTrace (prefixWord ++ tailWord_226835) baseStart_226835 baseEnd_226835 := by
    simpa [prefixWord, tailWord_226835, baseEnd_226835] using wordTrace_append hprefix tailTrace_226835
  have hstable : (prefixWord ++ tailWord_226835).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226835).length < 2 ^ (prefixWord ++ tailWord_226835).sum := by decide
  have hdescent : baseEnd_226835 < baseStart_226835 := by decide
  rcases family_descends (prefixWord ++ tailWord_226835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226846 : List Nat := [4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_226846 : Nat := 118140960795 + 226846 * 2 ^ 59
def prefixEnd_226846 : Nat := 4983230072969 + 3 ^ 40 * 226846 * 2
def baseEnd_226846 : Nat := 69025797066622043070673

theorem tailTrace_226846 : CollatzResearch.WordTrace tailWord_226846 prefixEnd_226846 69025797066622043070673 := by
  unfold tailWord_226846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034219167022894882185549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5515835557455439371656261 1034219167022894882185549)
  ·
    refine ⟨387832187633585580819581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1034219167022894882185549 387832187633585580819581)
    ·
      refine ⟨145437070362594592807343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387832187633585580819581 145437070362594592807343)
      ·
        refine ⟨218155605543891889211015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145437070362594592807343 218155605543891889211015)
        ·
          refine ⟨327233408315837833816523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218155605543891889211015 327233408315837833816523)
          ·
            refine ⟨490850112473756750724785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327233408315837833816523 490850112473756750724785)
            ·
              refine ⟨368137584355317563043589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490850112473756750724785 368137584355317563043589)
              ·
                refine ⟨69025797066622043070673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368137584355317563043589 69025797066622043070673)
                ·
                  rfl

theorem cell19_226846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_226846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226846 prefixEnd_226846 := by exact prefixLift 226846
  have htrace : WordTrace (prefixWord ++ tailWord_226846) baseStart_226846 baseEnd_226846 := by
    simpa [prefixWord, tailWord_226846, baseEnd_226846] using wordTrace_append hprefix tailTrace_226846
  have hstable : (prefixWord ++ tailWord_226846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226846).length < 2 ^ (prefixWord ++ tailWord_226846).sum := by decide
  have hdescent : baseEnd_226846 < baseStart_226846 := by decide
  rcases family_descends (prefixWord ++ tailWord_226846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226873 : List Nat := [1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_226873 : Nat := 118140960795 + 226873 * 2 ^ 59
def prefixEnd_226873 : Nat := 4983230072969 + 3 ^ 40 * 226873 * 2
def baseEnd_226873 : Nat := 69034012757093980470599

theorem tailTrace_226873 : CollatzResearch.WordTrace tailWord_226873 prefixEnd_226873 69034012757093980470599 := by
  unfold tailWord_226873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274738107085342668717273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5516492071390228445811515 8274738107085342668717273)
  ·
    refine ⟨6206053580314007001537955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8274738107085342668717273 6206053580314007001537955)
    ·
      refine ⟨9309080370471010502306933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206053580314007001537955 9309080370471010502306933)
      ·
        refine ⟨872726284731657234591275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9309080370471010502306933 872726284731657234591275)
        ·
          refine ⟨1309089427097485851886913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872726284731657234591275 1309089427097485851886913)
          ·
            refine ⟨981817070323114388915185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309089427097485851886913 981817070323114388915185)
            ·
              refine ⟨736362802742335791686389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981817070323114388915185 736362802742335791686389)
              ·
                refine ⟨69034012757093980470599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736362802742335791686389 69034012757093980470599)
                ·
                  rfl

theorem cell19_226873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_226873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226873 prefixEnd_226873 := by exact prefixLift 226873
  have htrace : WordTrace (prefixWord ++ tailWord_226873) baseStart_226873 baseEnd_226873 := by
    simpa [prefixWord, tailWord_226873, baseEnd_226873] using wordTrace_append hprefix tailTrace_226873
  have hstable : (prefixWord ++ tailWord_226873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226873).length < 2 ^ (prefixWord ++ tailWord_226873).sum := by decide
  have hdescent : baseEnd_226873 < baseStart_226873 := by decide
  rcases family_descends (prefixWord ++ tailWord_226873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226926 : List Nat := [4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_226926 : Nat := 118140960795 + 226926 * 2 ^ 59
def prefixEnd_226926 : Nat := 4983230072969 + 3 ^ 40 * 226926 * 2
def baseEnd_226926 : Nat := 69050139853205561292677

theorem tailTrace_226926 : CollatzResearch.WordTrace tailWord_226926 prefixEnd_226926 69050139853205561292677 := by
  unfold tailWord_226926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034583896986666590049579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5517780783928888480264421 1034583896986666590049579)
  ·
    refine ⟨1551875845479999885074369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034583896986666590049579 1551875845479999885074369)
    ·
      refine ⟨1163906884109999913805777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1551875845479999885074369 1163906884109999913805777)
      ·
        refine ⟨872930163082499935354333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1163906884109999913805777 872930163082499935354333)
        ·
          refine ⟨327348811155937475757875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872930163082499935354333 327348811155937475757875)
          ·
            refine ⟨491023216733906213636813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327348811155937475757875 491023216733906213636813)
            ·
              refine ⟨184133706275214830113805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491023216733906213636813 184133706275214830113805)
              ·
                refine ⟨69050139853205561292677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184133706275214830113805 69050139853205561292677)
                ·
                  rfl

theorem cell19_226926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_226926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226926 prefixEnd_226926 := by exact prefixLift 226926
  have htrace : WordTrace (prefixWord ++ tailWord_226926) baseStart_226926 baseEnd_226926 := by
    simpa [prefixWord, tailWord_226926, baseEnd_226926] using wordTrace_append hprefix tailTrace_226926
  have hstable : (prefixWord ++ tailWord_226926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226926).length < 2 ^ (prefixWord ++ tailWord_226926).sum := by decide
  have hdescent : baseEnd_226926 < baseStart_226926 := by decide
  rcases family_descends (prefixWord ++ tailWord_226926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_226928 : List Nat := [2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_226928 : Nat := 118140960795 + 226928 * 2 ^ 59
def prefixEnd_226928 : Nat := 4983230072969 + 3 ^ 40 * 226928 * 2
def baseEnd_226928 : Nat := 69050748422870149248227

theorem tailTrace_226928 : CollatzResearch.WordTrace tailWord_226928 prefixEnd_226928 69050748422870149248227 := by
  unfold tailWord_226928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138372060943043530984719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5517829414590724707979625 4138372060943043530984719)
  ·
    refine ⟨6207558091414565296477079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138372060943043530984719 6207558091414565296477079)
    ·
      refine ⟨9311337137121847944715619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207558091414565296477079 9311337137121847944715619)
      ·
        refine ⟨13967005705682771917073429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311337137121847944715619 13967005705682771917073429)
        ·
          refine ⟨654703392453879933612817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13967005705682771917073429 654703392453879933612817)
          ·
            refine ⟨491027544340409950209613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654703392453879933612817 491027544340409950209613)
            ·
              refine ⟨184135329127653731328605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491027544340409950209613 184135329127653731328605)
              ·
                refine ⟨69050748422870149248227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184135329127653731328605 69050748422870149248227)
                ·
                  rfl

theorem cell19_226928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_226928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_226928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_226928 prefixEnd_226928 := by exact prefixLift 226928
  have htrace : WordTrace (prefixWord ++ tailWord_226928) baseStart_226928 baseEnd_226928 := by
    simpa [prefixWord, tailWord_226928, baseEnd_226928] using wordTrace_append hprefix tailTrace_226928
  have hstable : (prefixWord ++ tailWord_226928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_226928).length < 2 ^ (prefixWord ++ tailWord_226928).sum := by decide
  have hdescent : baseEnd_226928 < baseStart_226928 := by decide
  rcases family_descends (prefixWord ++ tailWord_226928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227006 : List Nat := [4, 2, 1, 1, 2, 2, 7]
def baseStart_227006 : Nat := 118140960795 + 227006 * 2 ^ 59
def prefixEnd_227006 : Nat := 4983230072969 + 3 ^ 40 * 227006 * 2
def baseEnd_227006 : Nat := 23024827546596359838227

theorem tailTrace_227006 : CollatzResearch.WordTrace tailWord_227006 prefixEnd_227006 23024827546596359838227 := by
  unfold tailWord_227006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034948626950438297913609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5519726010402337588872581 1034948626950438297913609)
  ·
    refine ⟨776211470212828723435207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034948626950438297913609 776211470212828723435207)
    ·
      refine ⟨1164317205319243085152811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776211470212828723435207 1164317205319243085152811)
      ·
        refine ⟨1746475807978864627729217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164317205319243085152811 1746475807978864627729217)
        ·
          refine ⟨1309856855984148470796913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746475807978864627729217 1309856855984148470796913)
          ·
            refine ⟨982392641988111353097685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309856855984148470796913 982392641988111353097685)
            ·
              refine ⟨23024827546596359838227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 982392641988111353097685 23024827546596359838227)
              ·
                rfl

theorem cell19_227006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_227006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227006 prefixEnd_227006 := by exact prefixLift 227006
  have htrace : WordTrace (prefixWord ++ tailWord_227006) baseStart_227006 baseEnd_227006 := by
    simpa [prefixWord, tailWord_227006, baseEnd_227006] using wordTrace_append hprefix tailTrace_227006
  have hstable : (prefixWord ++ tailWord_227006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227006).length < 2 ^ (prefixWord ++ tailWord_227006).sum := by decide
  have hdescent : baseEnd_227006 < baseStart_227006 := by decide
  rcases family_descends (prefixWord ++ tailWord_227006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227021 : List Nat := [1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_227021 : Nat := 118140960795 + 227021 * 2 ^ 59
def prefixEnd_227021 : Nat := 4983230072969 + 3 ^ 40 * 227021 * 2
def baseEnd_227021 : Nat := 69079046912273489181307

theorem tailTrace_227021 : CollatzResearch.WordTrace tailWord_227021 prefixEnd_227021 69079046912273489181307 := by
  unfold tailWord_227021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280136110549163945104917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520090740366109296736611 8280136110549163945104917)
  ·
    refine ⟨388131380181992059926793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8280136110549163945104917 388131380181992059926793)
    ·
      refine ⟨291098535136494044945095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388131380181992059926793 291098535136494044945095)
      ·
        refine ⟨436647802704741067417643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291098535136494044945095 436647802704741067417643)
        ·
          refine ⟨654971704057111601126465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436647802704741067417643 654971704057111601126465)
          ·
            refine ⟨491228778042833700844849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 654971704057111601126465 491228778042833700844849)
            ·
              refine ⟨368421583532125275633637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491228778042833700844849 368421583532125275633637)
              ·
                refine ⟨69079046912273489181307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368421583532125275633637 69079046912273489181307)
                ·
                  rfl

theorem cell19_227021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_227021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227021 prefixEnd_227021 := by exact prefixLift 227021
  have htrace : WordTrace (prefixWord ++ tailWord_227021) baseStart_227021 baseEnd_227021 := by
    simpa [prefixWord, tailWord_227021, baseEnd_227021] using wordTrace_append hprefix tailTrace_227021
  have hstable : (prefixWord ++ tailWord_227021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227021).length < 2 ^ (prefixWord ++ tailWord_227021).sum := by decide
  have hdescent : baseEnd_227021 < baseStart_227021 := by decide
  rcases family_descends (prefixWord ++ tailWord_227021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227025 : List Nat := [1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_227025 : Nat := 118140960795 + 227025 * 2 ^ 59
def prefixEnd_227025 : Nat := 4983230072969 + 3 ^ 40 * 227025 * 2
def baseEnd_227025 : Nat := 69080264051602665092407

theorem tailTrace_227025 : CollatzResearch.WordTrace tailWord_227025 prefixEnd_227025 69080264051602665092407 := by
  unfold tailWord_227025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280282002534672628250529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5520188001689781752167019 8280282002534672628250529)
  ·
    refine ⟨6210211501901004471187897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8280282002534672628250529 6210211501901004471187897)
    ·
      refine ⟨4657658626425753353390923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6210211501901004471187897 4657658626425753353390923)
      ·
        refine ⟨6986487939638630030086385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657658626425753353390923 6986487939638630030086385)
        ·
          refine ⟨5239865954728972522564789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6986487939638630030086385 5239865954728972522564789)
          ·
            refine ⟨491237433255841173990449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5239865954728972522564789 491237433255841173990449)
            ·
              refine ⟨368428074941880880492837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491237433255841173990449 368428074941880880492837)
              ·
                refine ⟨69080264051602665092407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368428074941880880492837 69080264051602665092407)
                ·
                  rfl

theorem cell19_227025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_227025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227025 prefixEnd_227025 := by exact prefixLift 227025
  have htrace : WordTrace (prefixWord ++ tailWord_227025) baseStart_227025 baseEnd_227025 := by
    simpa [prefixWord, tailWord_227025, baseEnd_227025] using wordTrace_append hprefix tailTrace_227025
  have hstable : (prefixWord ++ tailWord_227025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227025).length < 2 ^ (prefixWord ++ tailWord_227025).sum := by decide
  have hdescent : baseEnd_227025 < baseStart_227025 := by decide
  rcases family_descends (prefixWord ++ tailWord_227025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227082 : List Nat := [3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_227082 : Nat := 118140960795 + 227082 * 2 ^ 59
def prefixEnd_227082 : Nat := 4983230072969 + 3 ^ 40 * 227082 * 2
def baseEnd_227082 : Nat := 69097608287043421825585

theorem tailTrace_227082 : CollatzResearch.WordTrace tailWord_227082 prefixEnd_227082 69097608287043421825585 := by
  unfold tailWord_227082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070590240832042840768875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5521573975552114242050333 2070590240832042840768875)
  ·
    refine ⟨3105885361248064261153313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070590240832042840768875 3105885361248064261153313)
    ·
      refine ⟨2329414020936048195864985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3105885361248064261153313 2329414020936048195864985)
      ·
        refine ⟨1747060515702036146898739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2329414020936048195864985 1747060515702036146898739)
        ·
          refine ⟨2620590773553054220348109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747060515702036146898739 2620590773553054220348109)
          ·
            refine ⟨982721540082395332630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620590773553054220348109 982721540082395332630541)
            ·
              refine ⟨368520577530898249736453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982721540082395332630541 368520577530898249736453)
              ·
                refine ⟨69097608287043421825585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368520577530898249736453 69097608287043421825585)
                ·
                  rfl

theorem cell19_227082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_227082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227082 prefixEnd_227082 := by exact prefixLift 227082
  have htrace : WordTrace (prefixWord ++ tailWord_227082) baseStart_227082 baseEnd_227082 := by
    simpa [prefixWord, tailWord_227082, baseEnd_227082] using wordTrace_append hprefix tailTrace_227082
  have hstable : (prefixWord ++ tailWord_227082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227082).length < 2 ^ (prefixWord ++ tailWord_227082).sum := by decide
  have hdescent : baseEnd_227082 < baseStart_227082 := by decide
  rcases family_descends (prefixWord ++ tailWord_227082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227118 : List Nat := [4, 1, 3, 2, 2, 1, 6]
def baseStart_227118 : Nat := 118140960795 + 227118 * 2 ^ 59
def prefixEnd_227118 : Nat := 4983230072969 + 3 ^ 40 * 227118 * 2
def baseEnd_227118 : Nat := 23036187513668668341829

theorem tailTrace_227118 : CollatzResearch.WordTrace tailWord_227118 prefixEnd_227118 23036187513668668341829 := by
  unfold tailWord_227118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035459248899718688923251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5522449327465166340924005 1035459248899718688923251)
  ·
    refine ⟨1553188873349578033384877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035459248899718688923251 1553188873349578033384877)
    ·
      refine ⟨582445827506091762519329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1553188873349578033384877 582445827506091762519329)
      ·
        refine ⟨436834370629568821889497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582445827506091762519329 436834370629568821889497)
        ·
          refine ⟨327625777972176616417123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436834370629568821889497 327625777972176616417123)
          ·
            refine ⟨491438666958264924625685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327625777972176616417123 491438666958264924625685)
            ·
              refine ⟨23036187513668668341829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 491438666958264924625685 23036187513668668341829)
              ·
                rfl

theorem cell19_227118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_227118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227118 prefixEnd_227118 := by exact prefixLift 227118
  have htrace : WordTrace (prefixWord ++ tailWord_227118) baseStart_227118 baseEnd_227118 := by
    simpa [prefixWord, tailWord_227118, baseEnd_227118] using wordTrace_append hprefix tailTrace_227118
  have hstable : (prefixWord ++ tailWord_227118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227118).length < 2 ^ (prefixWord ++ tailWord_227118).sum := by decide
  have hdescent : baseEnd_227118 < baseStart_227118 := by decide
  rcases family_descends (prefixWord ++ tailWord_227118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227141 : List Nat := [1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_227141 : Nat := 118140960795 + 227141 * 2 ^ 59
def prefixEnd_227141 : Nat := 4983230072969 + 3 ^ 40 * 227141 * 2
def baseEnd_227141 : Nat := 69115561092148766514313

theorem tailTrace_227141 : CollatzResearch.WordTrace tailWord_227141 prefixEnd_227141 69115561092148766514313 := by
  unfold tailWord_227141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284512870114424439473277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5523008580076282959648851 8284512870114424439473277)
  ·
    refine ⟨3106692326292909164802479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8284512870114424439473277 3106692326292909164802479)
    ·
      refine ⟨4660038489439363747203719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106692326292909164802479 4660038489439363747203719)
      ·
        refine ⟨6990057734159045620805579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660038489439363747203719 6990057734159045620805579)
        ·
          refine ⟨10485086601238568431208369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990057734159045620805579 10485086601238568431208369)
          ·
            refine ⟨7863814950928926323406277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10485086601238568431208369 7863814950928926323406277)
            ·
              refine ⟨1474465303299173685638677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7863814950928926323406277 1474465303299173685638677)
              ·
                refine ⟨69115561092148766514313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1474465303299173685638677 69115561092148766514313)
                ·
                  rfl

theorem cell19_227141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_227141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227141 prefixEnd_227141 := by exact prefixLift 227141
  have htrace : WordTrace (prefixWord ++ tailWord_227141) baseStart_227141 baseEnd_227141 := by
    simpa [prefixWord, tailWord_227141, baseEnd_227141] using wordTrace_append hprefix tailTrace_227141
  have hstable : (prefixWord ++ tailWord_227141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227141).length < 2 ^ (prefixWord ++ tailWord_227141).sum := by decide
  have hdescent : baseEnd_227141 < baseStart_227141 := by decide
  rcases family_descends (prefixWord ++ tailWord_227141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227156 : List Nat := [2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_227156 : Nat := 118140960795 + 227156 * 2 ^ 59
def prefixEnd_227156 : Nat := 4983230072969 + 3 ^ 40 * 227156 * 2
def baseEnd_227156 : Nat := 69120125364633176180939

theorem tailTrace_227156 : CollatzResearch.WordTrace tailWord_227156 prefixEnd_227156 69120125364633176180939 := by
  unfold tailWord_227156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142529982530041000634661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5523373310040054667512881 4142529982530041000634661)
  ·
    refine ⟨776724371724382687618999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4142529982530041000634661 776724371724382687618999)
    ·
      refine ⟨1165086557586574031428499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776724371724382687618999 1165086557586574031428499)
      ·
        refine ⟨1747629836379861047142749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165086557586574031428499 1747629836379861047142749)
        ·
          refine ⟨655361188642447892678531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1747629836379861047142749 655361188642447892678531)
          ·
            refine ⟨983041782963671839017797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655361188642447892678531 983041782963671839017797)
            ·
              refine ⟨184320334305688469815837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 983041782963671839017797 184320334305688469815837)
              ·
                refine ⟨69120125364633176180939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184320334305688469815837 69120125364633176180939)
                ·
                  rfl

theorem cell19_227156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_227156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227156 prefixEnd_227156 := by exact prefixLift 227156
  have htrace : WordTrace (prefixWord ++ tailWord_227156) baseStart_227156 baseEnd_227156 := by
    simpa [prefixWord, tailWord_227156, baseEnd_227156] using wordTrace_append hprefix tailTrace_227156
  have hstable : (prefixWord ++ tailWord_227156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227156).length < 2 ^ (prefixWord ++ tailWord_227156).sum := by decide
  have hdescent : baseEnd_227156 < baseStart_227156 := by decide
  rcases family_descends (prefixWord ++ tailWord_227156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227217 : List Nat := [1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_227217 : Nat := 118140960795 + 227217 * 2 ^ 59
def prefixEnd_227217 : Nat := 4983230072969 + 3 ^ 40 * 227217 * 2
def baseEnd_227217 : Nat := 69138686739403108825217

theorem tailTrace_227217 : CollatzResearch.WordTrace tailWord_227217 prefixEnd_227217 69138686739403108825217 := by
  unfold tailWord_227217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287284817839089419239905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5524856545226059612826603 8287284817839089419239905)
  ·
    refine ⟨6215463613379317064429929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8287284817839089419239905 6215463613379317064429929)
    ·
      refine ⟨4661597710034487798322447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215463613379317064429929 4661597710034487798322447)
      ·
        refine ⟨6992396565051731697483671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661597710034487798322447 6992396565051731697483671)
        ·
          refine ⟨10488594847577597546225507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992396565051731697483671 10488594847577597546225507)
          ·
            refine ⟨15732892271366396319338261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488594847577597546225507 15732892271366396319338261)
            ·
              refine ⟨737479325220299827468981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15732892271366396319338261 737479325220299827468981)
              ·
                refine ⟨69138686739403108825217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737479325220299827468981 69138686739403108825217)
                ·
                  rfl

theorem cell19_227217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_227217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227217 prefixEnd_227217 := by exact prefixLift 227217
  have htrace : WordTrace (prefixWord ++ tailWord_227217) baseStart_227217 baseEnd_227217 := by
    simpa [prefixWord, tailWord_227217, baseEnd_227217] using wordTrace_append hprefix tailTrace_227217
  have hstable : (prefixWord ++ tailWord_227217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227217).length < 2 ^ (prefixWord ++ tailWord_227217).sum := by decide
  have hdescent : baseEnd_227217 < baseStart_227217 := by decide
  rcases family_descends (prefixWord ++ tailWord_227217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227230 : List Nat := [4, 3, 1, 3, 2, 6]
def baseStart_227230 : Nat := 118140960795 + 227230 * 2 ^ 59
def prefixEnd_227230 : Nat := 4983230072969 + 3 ^ 40 * 227230 * 2
def baseEnd_227230 : Nat := 7682515826913658948477

theorem tailTrace_227230 : CollatzResearch.WordTrace tailWord_227230 prefixEnd_227230 7682515826913658948477 := by
  unfold tailWord_227230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035969870848999079932893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5525172644527995092975429 1035969870848999079932893)
  ·
    refine ⟨388488701568374654974835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1035969870848999079932893 388488701568374654974835)
    ·
      refine ⟨582733052352561982462253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388488701568374654974835 582733052352561982462253)
      ·
        refine ⟨218524894632210743423345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582733052352561982462253 218524894632210743423345)
        ·
          refine ⟨163893670974158057567509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218524894632210743423345 163893670974158057567509)
          ·
            refine ⟨7682515826913658948477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163893670974158057567509 7682515826913658948477)
            ·
              rfl

theorem cell19_227230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_227230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227230 prefixEnd_227230 := by exact prefixLift 227230
  have htrace : WordTrace (prefixWord ++ tailWord_227230) baseStart_227230 baseEnd_227230 := by
    simpa [prefixWord, tailWord_227230, baseEnd_227230] using wordTrace_append hprefix tailTrace_227230
  have hstable : (prefixWord ++ tailWord_227230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227230).length < 2 ^ (prefixWord ++ tailWord_227230).sum := by decide
  have hdescent : baseEnd_227230 < baseStart_227230 := by decide
  rcases family_descends (prefixWord ++ tailWord_227230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227234 : List Nat := [3, 3, 1, 2, 3, 7]
def baseStart_227234 : Nat := 118140960795 + 227234 * 2 ^ 59
def prefixEnd_227234 : Nat := 4983230072969 + 3 ^ 40 * 227234 * 2
def baseEnd_227234 : Nat := 7682651064616900716377

theorem tailTrace_227234 : CollatzResearch.WordTrace tailWord_227234 prefixEnd_227234 7682651064616900716377 := by
  unfold tailWord_227234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071976214694375330652189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5525269905851667548405837 2071976214694375330652189)
  ·
    refine ⟨776991080510390748994571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2071976214694375330652189 776991080510390748994571)
    ·
      refine ⟨1165486620765586123491857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776991080510390748994571 1165486620765586123491857)
      ·
        refine ⟨874114965574189592618893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165486620765586123491857 874114965574189592618893)
        ·
          refine ⟨327793112090321097232085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874114965574189592618893 327793112090321097232085)
          ·
            refine ⟨7682651064616900716377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 327793112090321097232085 7682651064616900716377)
            ·
              rfl

theorem cell19_227234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_227234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227234 prefixEnd_227234 := by exact prefixLift 227234
  have htrace : WordTrace (prefixWord ++ tailWord_227234) baseStart_227234 baseEnd_227234 := by
    simpa [prefixWord, tailWord_227234, baseEnd_227234] using wordTrace_append hprefix tailTrace_227234
  have hstable : (prefixWord ++ tailWord_227234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227234).length < 2 ^ (prefixWord ++ tailWord_227234).sum := by decide
  have hdescent : baseEnd_227234 < baseStart_227234 := by decide
  rcases family_descends (prefixWord ++ tailWord_227234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227236 : List Nat := [2, 3, 1, 2, 1, 10]
def baseStart_227236 : Nat := 118140960795 + 227236 * 2 ^ 59
def prefixEnd_227236 : Nat := 4983230072969 + 3 ^ 40 * 227236 * 2
def baseEnd_227236 : Nat := 7682718683468521600327

theorem tailTrace_227236 : CollatzResearch.WordTrace tailWord_227236 prefixEnd_227236 7682718683468521600327 := by
  unfold tailWord_227236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143988902385127832090781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5525318536513503776121041 4143988902385127832090781)
  ·
    refine ⟨1553995838394422937034043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4143988902385127832090781 1553995838394422937034043)
    ·
      refine ⟨2330993757591634405551065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553995838394422937034043 2330993757591634405551065)
      ·
        refine ⟨1748245318193725804163299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330993757591634405551065 1748245318193725804163299)
        ·
          refine ⟨2622367977290588706244949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748245318193725804163299 2622367977290588706244949)
          ·
            refine ⟨7682718683468521600327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2622367977290588706244949 7682718683468521600327)
            ·
              rfl

theorem cell19_227236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_227236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227236 prefixEnd_227236 := by exact prefixLift 227236
  have htrace : WordTrace (prefixWord ++ tailWord_227236) baseStart_227236 baseEnd_227236 := by
    simpa [prefixWord, tailWord_227236, baseEnd_227236] using wordTrace_append hprefix tailTrace_227236
  have hstable : (prefixWord ++ tailWord_227236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227236).length < 2 ^ (prefixWord ++ tailWord_227236).sum := by decide
  have hdescent : baseEnd_227236 < baseStart_227236 := by decide
  rcases family_descends (prefixWord ++ tailWord_227236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227253 : List Nat := [1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_227253 : Nat := 118140960795 + 227253 * 2 ^ 59
def prefixEnd_227253 : Nat := 4983230072969 + 3 ^ 40 * 227253 * 2
def baseEnd_227253 : Nat := 69149640993365692025119

theorem tailTrace_227253 : CollatzResearch.WordTrace tailWord_227253 prefixEnd_227253 69149640993365692025119 := by
  unfold tailWord_227253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288597845708667567550413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5525731897139111711700275 8288597845708667567550413)
  ·
    refine ⟨3108224192140750337831405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8288597845708667567550413 3108224192140750337831405)
    ·
      refine ⟨1165584072052781376686777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3108224192140750337831405 1165584072052781376686777)
      ·
        refine ⟨874188054039586032515083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165584072052781376686777 874188054039586032515083)
        ·
          refine ⟨1311282081059379048772625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874188054039586032515083 1311282081059379048772625)
          ·
            refine ⟨983461560794534286579469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1311282081059379048772625 983461560794534286579469)
            ·
              refine ⟨368798085297950357467301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 983461560794534286579469 368798085297950357467301)
              ·
                refine ⟨69149640993365692025119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368798085297950357467301 69149640993365692025119)
                ·
                  rfl

theorem cell19_227253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_227253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227253 prefixEnd_227253 := by exact prefixLift 227253
  have htrace : WordTrace (prefixWord ++ tailWord_227253) baseStart_227253 baseEnd_227253 := by
    simpa [prefixWord, tailWord_227253, baseEnd_227253] using wordTrace_append hprefix tailTrace_227253
  have hstable : (prefixWord ++ tailWord_227253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227253).length < 2 ^ (prefixWord ++ tailWord_227253).sum := by decide
  have hdescent : baseEnd_227253 < baseStart_227253 := by decide
  rcases family_descends (prefixWord ++ tailWord_227253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227274 : List Nat := [3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_227274 : Nat := 118140960795 + 227274 * 2 ^ 59
def prefixEnd_227274 : Nat := 4983230072969 + 3 ^ 40 * 227274 * 2
def baseEnd_227274 : Nat := 69156030974843865558395

theorem tailTrace_227274 : CollatzResearch.WordTrace tailWord_227274 prefixEnd_227274 69156030974843865558395 := by
  unfold tailWord_227274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072340944658147038516219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5526242519088392102709917 2072340944658147038516219)
  ·
    refine ⟨3108511416987220557774329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072340944658147038516219 3108511416987220557774329)
    ·
      refine ⟨2331383562740415418330747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3108511416987220557774329 2331383562740415418330747)
      ·
        refine ⟨3497075344110623127496121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331383562740415418330747 3497075344110623127496121)
        ·
          refine ⟨2622806508082967345622091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497075344110623127496121 2622806508082967345622091)
          ·
            refine ⟨3934209762124451018433137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622806508082967345622091 3934209762124451018433137)
            ·
              refine ⟨2950657321593338263824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934209762124451018433137 2950657321593338263824853)
              ·
                refine ⟨69156030974843865558395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2950657321593338263824853 69156030974843865558395)
                ·
                  rfl

theorem cell19_227274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_227274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227274 prefixEnd_227274 := by exact prefixLift 227274
  have htrace : WordTrace (prefixWord ++ tailWord_227274) baseStart_227274 baseEnd_227274 := by
    simpa [prefixWord, tailWord_227274, baseEnd_227274] using wordTrace_append hprefix tailTrace_227274
  have hstable : (prefixWord ++ tailWord_227274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227274).length < 2 ^ (prefixWord ++ tailWord_227274).sum := by decide
  have hdescent : baseEnd_227274 < baseStart_227274 := by decide
  rcases family_descends (prefixWord ++ tailWord_227274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227388 : List Nat := [2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_227388 : Nat := 118140960795 + 227388 * 2 ^ 59
def prefixEnd_227388 : Nat := 4983230072969 + 3 ^ 40 * 227388 * 2
def baseEnd_227388 : Nat := 69190719445725379024751

theorem tailTrace_227388 : CollatzResearch.WordTrace tailWord_227388 prefixEnd_227388 69190719445725379024751 := by
  unfold tailWord_227388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146760850109792811857409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5529014466813057082476545 4146760850109792811857409)
  ·
    refine ⟨3110070637582344608893057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4146760850109792811857409 3110070637582344608893057)
    ·
      refine ⟨2332552978186758456669793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3110070637582344608893057 2332552978186758456669793)
      ·
        refine ⟨1749414733640068842502345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2332552978186758456669793 1749414733640068842502345)
        ·
          refine ⟨1312061050230051631876759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749414733640068842502345 1312061050230051631876759)
          ·
            refine ⟨1968091575345077447815139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312061050230051631876759 1968091575345077447815139)
            ·
              refine ⟨2952137363017616171722709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968091575345077447815139 2952137363017616171722709)
              ·
                refine ⟨69190719445725379024751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2952137363017616171722709 69190719445725379024751)
                ·
                  rfl

theorem cell19_227388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_227388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227388 prefixEnd_227388 := by exact prefixLift 227388
  have htrace : WordTrace (prefixWord ++ tailWord_227388) baseStart_227388 baseEnd_227388 := by
    simpa [prefixWord, tailWord_227388, baseEnd_227388] using wordTrace_append hprefix tailTrace_227388
  have hstable : (prefixWord ++ tailWord_227388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227388).length < 2 ^ (prefixWord ++ tailWord_227388).sum := by decide
  have hdescent : baseEnd_227388 < baseStart_227388 := by decide
  rcases family_descends (prefixWord ++ tailWord_227388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227424 : List Nat := [2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_227424 : Nat := 118140960795 + 227424 * 2 ^ 59
def prefixEnd_227424 : Nat := 4983230072969 + 3 ^ 40 * 227424 * 2
def baseEnd_227424 : Nat := 69201673699687962224653

theorem tailTrace_227424 : CollatzResearch.WordTrace tailWord_227424 prefixEnd_227424 69201673699687962224653 := by
  unfold tailWord_227424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147417364044581886012663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5529889818726109181350217 4147417364044581886012663)
  ·
    refine ⟨6221126046066872829018995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4147417364044581886012663 6221126046066872829018995)
    ·
      refine ⟨9331689069100309243528493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221126046066872829018995 9331689069100309243528493)
      ·
        refine ⟨3499383400912615966323185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9331689069100309243528493 3499383400912615966323185)
        ·
          refine ⟨2624537550684461974742389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3499383400912615966323185 2624537550684461974742389)
          ·
            refine ⟨246050395376668310132099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2624537550684461974742389 246050395376668310132099)
            ·
              refine ⟨369075593065002465198149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246050395376668310132099 369075593065002465198149)
              ·
                refine ⟨69201673699687962224653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369075593065002465198149 69201673699687962224653)
                ·
                  rfl

theorem cell19_227424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_227424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227424 prefixEnd_227424 := by exact prefixLift 227424
  have htrace : WordTrace (prefixWord ++ tailWord_227424) baseStart_227424 baseEnd_227424 := by
    simpa [prefixWord, tailWord_227424, baseEnd_227424] using wordTrace_append hprefix tailTrace_227424
  have hstable : (prefixWord ++ tailWord_227424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227424).length < 2 ^ (prefixWord ++ tailWord_227424).sum := by decide
  have hdescent : baseEnd_227424 < baseStart_227424 := by decide
  rcases family_descends (prefixWord ++ tailWord_227424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227498 : List Nat := [3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_227498 : Nat := 118140960795 + 227498 * 2 ^ 59
def prefixEnd_227498 : Nat := 4983230072969 + 3 ^ 40 * 227498 * 2
def baseEnd_227498 : Nat := 69224190777277716580007

theorem tailTrace_227498 : CollatzResearch.WordTrace tailWord_227498 prefixEnd_227498 69224190777277716580007 := by
  unfold tailWord_227498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074383432455268602554787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5531689153214049606812765 2074383432455268602554787)
  ·
    refine ⟨3111575148682902903832181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074383432455268602554787 3111575148682902903832181)
    ·
      refine ⟨291710170189022147234267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3111575148682902903832181 291710170189022147234267)
      ·
        refine ⟨437565255283533220851401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291710170189022147234267 437565255283533220851401)
        ·
          refine ⟨328173941462649915638551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437565255283533220851401 328173941462649915638551)
          ·
            refine ⟨492260912193974873457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328173941462649915638551 492260912193974873457827)
            ·
              refine ⟨738391368290962310186741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492260912193974873457827 738391368290962310186741)
              ·
                refine ⟨69224190777277716580007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 738391368290962310186741 69224190777277716580007)
                ·
                  rfl

theorem cell19_227498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_227498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227498 prefixEnd_227498 := by exact prefixLift 227498
  have htrace : WordTrace (prefixWord ++ tailWord_227498) baseStart_227498 baseEnd_227498 := by
    simpa [prefixWord, tailWord_227498, baseEnd_227498] using wordTrace_append hprefix tailTrace_227498
  have hstable : (prefixWord ++ tailWord_227498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227498).length < 2 ^ (prefixWord ++ tailWord_227498).sum := by decide
  have hdescent : baseEnd_227498 < baseStart_227498 := by decide
  rcases family_descends (prefixWord ++ tailWord_227498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227538 : List Nat := [3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_227538 : Nat := 118140960795 + 227538 * 2 ^ 59
def prefixEnd_227538 : Nat := 4983230072969 + 3 ^ 40 * 227538 * 2
def baseEnd_227538 : Nat := 69236362170569475691009

theorem tailTrace_227538 : CollatzResearch.WordTrace tailWord_227538 prefixEnd_227538 69236362170569475691009 := by
  unfold tailWord_227538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074748162419040310418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5532661766450774161116845 2074748162419040310418817)
  ·
    refine ⟨1556061121814280232814113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2074748162419040310418817 1556061121814280232814113)
    ·
      refine ⟨1167045841360710174610585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556061121814280232814113 1167045841360710174610585)
      ·
        refine ⟨875284381020532630957939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167045841360710174610585 875284381020532630957939)
        ·
          refine ⟨1312926571530798946436909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875284381020532630957939 1312926571530798946436909)
          ·
            refine ⟨492347464324049604913841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312926571530798946436909 492347464324049604913841)
            ·
              refine ⟨369260598243037203685381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492347464324049604913841 369260598243037203685381)
              ·
                refine ⟨69236362170569475691009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369260598243037203685381 69236362170569475691009)
                ·
                  rfl

theorem cell19_227538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_227538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227538 prefixEnd_227538 := by exact prefixLift 227538
  have htrace : WordTrace (prefixWord ++ tailWord_227538) baseStart_227538 baseEnd_227538 := by
    simpa [prefixWord, tailWord_227538, baseEnd_227538] using wordTrace_append hprefix tailTrace_227538
  have hstable : (prefixWord ++ tailWord_227538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227538).length < 2 ^ (prefixWord ++ tailWord_227538).sum := by decide
  have hdescent : baseEnd_227538 < baseStart_227538 := by decide
  rcases family_descends (prefixWord ++ tailWord_227538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227591 : List Nat := [1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_227591 : Nat := 118140960795 + 227591 * 2 ^ 59
def prefixEnd_227591 : Nat := 4983230072969 + 3 ^ 40 * 227591 * 2
def baseEnd_227591 : Nat := 69252489266681056513087

theorem tailTrace_227591 : CollatzResearch.WordTrace tailWord_227591 prefixEnd_227591 69252489266681056513087 := by
  unfold tailWord_227591
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300925718484151293354627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5533950478989434195569751 8300925718484151293354627)
  ·
    refine ⟨12451388577726226940031941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300925718484151293354627 12451388577726226940031941)
    ·
      refine ⟨2334635358323667551255989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12451388577726226940031941 2334635358323667551255989)
      ·
        refine ⟨218872064842843832930249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2334635358323667551255989 218872064842843832930249)
        ·
          refine ⟨164154048632132874697687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218872064842843832930249 164154048632132874697687)
          ·
            refine ⟨246231072948199312046531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164154048632132874697687 246231072948199312046531)
            ·
              refine ⟨369346609422298968069797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246231072948199312046531 369346609422298968069797)
              ·
                refine ⟨69252489266681056513087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369346609422298968069797 69252489266681056513087)
                ·
                  rfl

theorem cell19_227591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_227591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227591 prefixEnd_227591 := by exact prefixLift 227591
  have htrace : WordTrace (prefixWord ++ tailWord_227591) baseStart_227591 baseEnd_227591 := by
    simpa [prefixWord, tailWord_227591, baseEnd_227591] using wordTrace_append hprefix tailTrace_227591
  have hstable : (prefixWord ++ tailWord_227591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227591).length < 2 ^ (prefixWord ++ tailWord_227591).sum := by decide
  have hdescent : baseEnd_227591 < baseStart_227591 := by decide
  rcases family_descends (prefixWord ++ tailWord_227591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227669 : List Nat := [1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_227669 : Nat := 118140960795 + 227669 * 2 ^ 59
def prefixEnd_227669 : Nat := 4983230072969 + 3 ^ 40 * 227669 * 2
def baseEnd_227669 : Nat := 69276223483599986779541

theorem tailTrace_227669 : CollatzResearch.WordTrace tailWord_227669 prefixEnd_227669 69276223483599986779541 := by
  unfold tailWord_227669
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303770612201570614694061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5535847074801047076462707 8303770612201570614694061)
  ·
    refine ⟨3113913979575588980510273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8303770612201570614694061 3113913979575588980510273)
    ·
      refine ⟨2335435484681691735382705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3113913979575588980510273 2335435484681691735382705)
      ·
        refine ⟨1751576613511268801537029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335435484681691735382705 1751576613511268801537029)
        ·
          refine ⟨328420615033362900288193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1751576613511268801537029 328420615033362900288193)
          ·
            refine ⟨246315461275022175216145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328420615033362900288193 246315461275022175216145)
            ·
              refine ⟨184736595956266631412109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246315461275022175216145 184736595956266631412109)
              ·
                refine ⟨69276223483599986779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184736595956266631412109 69276223483599986779541)
                ·
                  rfl

theorem cell19_227669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_227669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227669 prefixEnd_227669 := by exact prefixLift 227669
  have htrace : WordTrace (prefixWord ++ tailWord_227669) baseStart_227669 baseEnd_227669 := by
    simpa [prefixWord, tailWord_227669, baseEnd_227669] using wordTrace_append hprefix tailTrace_227669
  have hstable : (prefixWord ++ tailWord_227669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227669).length < 2 ^ (prefixWord ++ tailWord_227669).sum := by decide
  have hdescent : baseEnd_227669 < baseStart_227669 := by decide
  rcases family_descends (prefixWord ++ tailWord_227669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227690 : List Nat := [3, 1, 3, 3, 1, 3, 5]
def baseStart_227690 : Nat := 118140960795 + 227690 * 2 ^ 59
def prefixEnd_227690 : Nat := 4983230072969 + 3 ^ 40 * 227690 * 2
def baseEnd_227690 : Nat := 23094204488359386770939

theorem tailTrace_227690 : CollatzResearch.WordTrace tailWord_227690 prefixEnd_227690 23094204488359386770939 := by
  unfold tailWord_227690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076134136281372800302131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5536357696750327467472349 2076134136281372800302131)
  ·
    refine ⟨3114201204422059200453197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2076134136281372800302131 3114201204422059200453197)
    ·
      refine ⟨1167825451658272200169949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3114201204422059200453197 1167825451658272200169949)
      ·
        refine ⟨437934544371852075063731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1167825451658272200169949 437934544371852075063731)
        ·
          refine ⟨656901816557778112595597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437934544371852075063731 656901816557778112595597)
          ·
            refine ⟨246338181209166792223349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656901816557778112595597 246338181209166792223349)
            ·
              refine ⟨23094204488359386770939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246338181209166792223349 23094204488359386770939)
              ·
                rfl

theorem cell19_227690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_227690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227690 prefixEnd_227690 := by exact prefixLift 227690
  have htrace : WordTrace (prefixWord ++ tailWord_227690) baseStart_227690 baseEnd_227690 := by
    simpa [prefixWord, tailWord_227690, baseEnd_227690] using wordTrace_append hprefix tailTrace_227690
  have hstable : (prefixWord ++ tailWord_227690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227690).length < 2 ^ (prefixWord ++ tailWord_227690).sum := by decide
  have hdescent : baseEnd_227690 < baseStart_227690 := by decide
  rcases family_descends (prefixWord ++ tailWord_227690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227808 : List Nat := [2, 1, 1, 3, 1, 1, 10]
def baseStart_227808 : Nat := 118140960795 + 227808 * 2 ^ 59
def prefixEnd_227808 : Nat := 4983230072969 + 3 ^ 40 * 227808 * 2
def baseEnd_227808 : Nat := 23106173025096283230091

theorem tailTrace_227808 : CollatzResearch.WordTrace tailWord_227808 prefixEnd_227808 23106173025096283230091 := by
  unfold tailWord_227808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154420179348998677002039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5539226905798664902669385 4154420179348998677002039)
  ·
    refine ⟨6231630269023498015503059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154420179348998677002039 6231630269023498015503059)
    ·
      refine ⟨9347445403535247023254589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231630269023498015503059 9347445403535247023254589)
      ·
        refine ⟨3505292026325717633720471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9347445403535247023254589 3505292026325717633720471)
        ·
          refine ⟨5257938039488576450580707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505292026325717633720471 5257938039488576450580707)
          ·
            refine ⟨7886907059232864675871061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257938039488576450580707 7886907059232864675871061)
            ·
              refine ⟨23106173025096283230091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7886907059232864675871061 23106173025096283230091)
              ·
                rfl

theorem cell19_227808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_227808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227808 prefixEnd_227808 := by exact prefixLift 227808
  have htrace : WordTrace (prefixWord ++ tailWord_227808) baseStart_227808 baseEnd_227808 := by
    simpa [prefixWord, tailWord_227808, baseEnd_227808] using wordTrace_append hprefix tailTrace_227808
  have hstable : (prefixWord ++ tailWord_227808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227808).length < 2 ^ (prefixWord ++ tailWord_227808).sum := by decide
  have hdescent : baseEnd_227808 < baseStart_227808 := by decide
  rcases family_descends (prefixWord ++ tailWord_227808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227827 : List Nat := [1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_227827 : Nat := 118140960795 + 227827 * 2 ^ 59
def prefixEnd_227827 : Nat := 4983230072969 + 3 ^ 40 * 227827 * 2
def baseEnd_227827 : Nat := 69324300487102435267999

theorem tailTrace_227827 : CollatzResearch.WordTrace tailWord_227827 prefixEnd_227827 69324300487102435267999 := by
  unfold tailWord_227827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309533345629163598945735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5539688897086109065963823 8309533345629163598945735)
  ·
    refine ⟨12464300018443745398418603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309533345629163598945735 12464300018443745398418603)
    ·
      refine ⟨18696450027665618097627905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464300018443745398418603 18696450027665618097627905)
      ·
        refine ⟨14022337520749213573220929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18696450027665618097627905 14022337520749213573220929)
        ·
          refine ⟨10516753140561910179915697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14022337520749213573220929 10516753140561910179915697)
          ·
            refine ⟨7887564855421432634936773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10516753140561910179915697 7887564855421432634936773)
            ·
              refine ⟨1478918410391518619050645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7887564855421432634936773 1478918410391518619050645)
              ·
                refine ⟨69324300487102435267999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1478918410391518619050645 69324300487102435267999)
                ·
                  rfl

theorem cell19_227827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_227827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227827 prefixEnd_227827 := by exact prefixLift 227827
  have htrace : WordTrace (prefixWord ++ tailWord_227827) baseStart_227827 baseEnd_227827 := by
    simpa [prefixWord, tailWord_227827, baseEnd_227827] using wordTrace_append hprefix tailTrace_227827
  have hstable : (prefixWord ++ tailWord_227827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227827).length < 2 ^ (prefixWord ++ tailWord_227827).sum := by decide
  have hdescent : baseEnd_227827 < baseStart_227827 := by decide
  rcases family_descends (prefixWord ++ tailWord_227827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227880 : List Nat := [2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_227880 : Nat := 118140960795 + 227880 * 2 ^ 59
def prefixEnd_227880 : Nat := 4983230072969 + 3 ^ 40 * 227880 * 2
def baseEnd_227880 : Nat := 69340427583214016090077

theorem tailTrace_227880 : CollatzResearch.WordTrace tailWord_227880 prefixEnd_227880 69340427583214016090077 := by
  unfold tailWord_227880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155733207218576825312547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5540977609624769100416729 4155733207218576825312547)
  ·
    refine ⟨6233599810827865237968821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155733207218576825312547 6233599810827865237968821)
    ·
      refine ⟨584399982265112366059577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6233599810827865237968821 584399982265112366059577)
      ·
        refine ⟨438299986698834274544683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584399982265112366059577 438299986698834274544683)
        ·
          refine ⟨657449980048251411817025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438299986698834274544683 657449980048251411817025)
          ·
            refine ⟨493087485036188558862769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657449980048251411817025 493087485036188558862769)
            ·
              refine ⟨369815613777141419147077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493087485036188558862769 369815613777141419147077)
              ·
                refine ⟨69340427583214016090077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369815613777141419147077 69340427583214016090077)
                ·
                  rfl

theorem cell19_227880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_227880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227880 prefixEnd_227880 := by exact prefixLift 227880
  have htrace : WordTrace (prefixWord ++ tailWord_227880) baseStart_227880 baseEnd_227880 := by
    simpa [prefixWord, tailWord_227880, baseEnd_227880] using wordTrace_append hprefix tailTrace_227880
  have hstable : (prefixWord ++ tailWord_227880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227880).length < 2 ^ (prefixWord ++ tailWord_227880).sum := by decide
  have hdescent : baseEnd_227880 < baseStart_227880 := by decide
  rcases family_descends (prefixWord ++ tailWord_227880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227882 : List Nat := [3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_227882 : Nat := 118140960795 + 227882 * 2 ^ 59
def prefixEnd_227882 : Nat := 4983230072969 + 3 ^ 40 * 227882 * 2
def baseEnd_227882 : Nat := 69341036152878604045627

theorem tailTrace_227882 : CollatzResearch.WordTrace tailWord_227882 prefixEnd_227882 69341036152878604045627 := by
  unfold tailWord_227882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077884840107476998049475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5541026240286605328131933 2077884840107476998049475)
  ·
    refine ⟨3116827260161215497074213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077884840107476998049475 3116827260161215497074213)
    ·
      refine ⟨584405111280227905701415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3116827260161215497074213 584405111280227905701415)
      ·
        refine ⟨876607666920341858552123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584405111280227905701415 876607666920341858552123)
        ·
          refine ⟨1314911500380512787828185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876607666920341858552123 1314911500380512787828185)
          ·
            refine ⟨986183625285384590871139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314911500380512787828185 986183625285384590871139)
            ·
              refine ⟨1479275437928076886306709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986183625285384590871139 1479275437928076886306709)
              ·
                refine ⟨69341036152878604045627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1479275437928076886306709 69341036152878604045627)
                ·
                  rfl

theorem cell19_227882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_227882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227882 prefixEnd_227882 := by exact prefixLift 227882
  have htrace : WordTrace (prefixWord ++ tailWord_227882) baseStart_227882 baseEnd_227882 := by
    simpa [prefixWord, tailWord_227882, baseEnd_227882] using wordTrace_append hprefix tailTrace_227882
  have hstable : (prefixWord ++ tailWord_227882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227882).length < 2 ^ (prefixWord ++ tailWord_227882).sum := by decide
  have hdescent : baseEnd_227882 < baseStart_227882 := by decide
  rcases family_descends (prefixWord ++ tailWord_227882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227901 : List Nat := [1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_227901 : Nat := 118140960795 + 227901 * 2 ^ 59
def prefixEnd_227901 : Nat := 4983230072969 + 3 ^ 40 * 227901 * 2
def baseEnd_227901 : Nat := 69346817564692189623353

theorem tailTrace_227901 : CollatzResearch.WordTrace tailWord_227901 prefixEnd_227901 69346817564692189623353 := by
  unfold tailWord_227901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312232347361074237139557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5541488231574049491426371 8312232347361074237139557)
  ·
    refine ⟨1558543565130201419463667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8312232347361074237139557 1558543565130201419463667)
    ·
      refine ⟨2337815347695302129195501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558543565130201419463667 2337815347695302129195501)
      ·
        refine ⟨876680755385738298448313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2337815347695302129195501 876680755385738298448313)
        ·
          refine ⟨657510566539303723836235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876680755385738298448313 657510566539303723836235)
          ·
            refine ⟨986265849808955585754353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657510566539303723836235 986265849808955585754353)
            ·
              refine ⟨739699387356716689315765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986265849808955585754353 739699387356716689315765)
              ·
                refine ⟨69346817564692189623353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 739699387356716689315765 69346817564692189623353)
                ·
                  rfl

theorem cell19_227901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_227901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227901 prefixEnd_227901 := by exact prefixLift 227901
  have htrace : WordTrace (prefixWord ++ tailWord_227901) baseStart_227901 baseEnd_227901 := by
    simpa [prefixWord, tailWord_227901, baseEnd_227901] using wordTrace_append hprefix tailTrace_227901
  have hstable : (prefixWord ++ tailWord_227901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227901).length < 2 ^ (prefixWord ++ tailWord_227901).sum := by decide
  have hdescent : baseEnd_227901 < baseStart_227901 := by decide
  rcases family_descends (prefixWord ++ tailWord_227901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_227903 : List Nat := [1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_227903 : Nat := 118140960795 + 227903 * 2 ^ 59
def prefixEnd_227903 : Nat := 4983230072969 + 3 ^ 40 * 227903 * 2
def baseEnd_227903 : Nat := 69347426134356777578903

theorem tailTrace_227903 : CollatzResearch.WordTrace tailWord_227903 prefixEnd_227903 69347426134356777578903 := by
  unfold tailWord_227903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312305293353828578712363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5541536862235885719141575 8312305293353828578712363)
  ·
    refine ⟨12468457940030742868068545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312305293353828578712363 12468457940030742868068545)
    ·
      refine ⟨9351343455023057151051409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12468457940030742868068545 9351343455023057151051409)
      ·
        refine ⟨7013507591267292863288557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9351343455023057151051409 7013507591267292863288557)
        ·
          refine ⟨2630065346725234823733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7013507591267292863288557 2630065346725234823733209)
          ·
            refine ⟨1972549010043926117799907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630065346725234823733209 1972549010043926117799907)
            ·
              refine ⟨2958823515065889176699861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972549010043926117799907 2958823515065889176699861)
              ·
                refine ⟨69347426134356777578903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2958823515065889176699861 69347426134356777578903)
                ·
                  rfl

theorem cell19_227903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_227903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_227903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_227903 prefixEnd_227903 := by exact prefixLift 227903
  have htrace : WordTrace (prefixWord ++ tailWord_227903) baseStart_227903 baseEnd_227903 := by
    simpa [prefixWord, tailWord_227903, baseEnd_227903] using wordTrace_append hprefix tailTrace_227903
  have hstable : (prefixWord ++ tailWord_227903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_227903).length < 2 ^ (prefixWord ++ tailWord_227903).sum := by decide
  have hdescent : baseEnd_227903 < baseStart_227903 := by decide
  rcases family_descends (prefixWord ++ tailWord_227903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228013 : List Nat := [1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_228013 : Nat := 118140960795 + 228013 * 2 ^ 59
def prefixEnd_228013 : Nat := 4983230072969 + 3 ^ 40 * 228013 * 2
def baseEnd_228013 : Nat := 69380897465909115134159

theorem tailTrace_228013 : CollatzResearch.WordTrace tailWord_228013 prefixEnd_228013 69380897465909115134159 := by
  unfold tailWord_228013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316317322955317365216693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5544211548636878243477795 8316317322955317365216693)
  ·
    refine ⟨779654749027061002989065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8316317322955317365216693 779654749027061002989065)
    ·
      refine ⟨584741061770295752241799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 779654749027061002989065 584741061770295752241799)
      ·
        refine ⟨877111592655443628362699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584741061770295752241799 877111592655443628362699)
        ·
          refine ⟨1315667388983165442544049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877111592655443628362699 1315667388983165442544049)
          ·
            refine ⟨986750541737374081908037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315667388983165442544049 986750541737374081908037)
            ·
              refine ⟨185015726575757640357757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 986750541737374081908037 185015726575757640357757)
              ·
                refine ⟨69380897465909115134159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185015726575757640357757 69380897465909115134159)
                ·
                  rfl

theorem cell19_228013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_228013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228013 prefixEnd_228013 := by exact prefixLift 228013
  have htrace : WordTrace (prefixWord ++ tailWord_228013) baseStart_228013 baseEnd_228013 := by
    simpa [prefixWord, tailWord_228013, baseEnd_228013] using wordTrace_append hprefix tailTrace_228013
  have hstable : (prefixWord ++ tailWord_228013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228013).length < 2 ^ (prefixWord ++ tailWord_228013).sum := by decide
  have hdescent : baseEnd_228013 < baseStart_228013 := by decide
  rcases family_descends (prefixWord ++ tailWord_228013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228015 : List Nat := [1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_228015 : Nat := 118140960795 + 228015 * 2 ^ 59
def prefixEnd_228015 : Nat := 4983230072969 + 3 ^ 40 * 228015 * 2
def baseEnd_228015 : Nat := 69381506035573703089709

theorem tailTrace_228015 : CollatzResearch.WordTrace tailWord_228015 prefixEnd_228015 69381506035573703089709 := by
  unfold tailWord_228015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316390268948071706789499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5544260179298714471192999 8316390268948071706789499)
  ·
    refine ⟨12474585403422107560184249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316390268948071706789499 12474585403422107560184249)
    ·
      refine ⟨9355939052566580670138187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12474585403422107560184249 9355939052566580670138187)
      ·
        refine ⟨14033908578849871005207281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9355939052566580670138187 14033908578849871005207281)
        ·
          refine ⟨10525431434137403253905461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14033908578849871005207281 10525431434137403253905461)
          ·
            refine ⟨986759196950381555053637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10525431434137403253905461 986759196950381555053637)
            ·
              refine ⟨185017349428196541572557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 986759196950381555053637 185017349428196541572557)
              ·
                refine ⟨69381506035573703089709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185017349428196541572557 69381506035573703089709)
                ·
                  rfl

theorem cell19_228015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_228015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228015 prefixEnd_228015 := by exact prefixLift 228015
  have htrace : WordTrace (prefixWord ++ tailWord_228015) baseStart_228015 baseEnd_228015 := by
    simpa [prefixWord, tailWord_228015, baseEnd_228015] using wordTrace_append hprefix tailTrace_228015
  have hstable : (prefixWord ++ tailWord_228015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228015).length < 2 ^ (prefixWord ++ tailWord_228015).sum := by decide
  have hdescent : baseEnd_228015 < baseStart_228015 := by decide
  rcases family_descends (prefixWord ++ tailWord_228015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228055 : List Nat := [1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_228055 : Nat := 118140960795 + 228055 * 2 ^ 59
def prefixEnd_228055 : Nat := 4983230072969 + 3 ^ 40 * 228055 * 2
def baseEnd_228055 : Nat := 69393677428865462200711

theorem tailTrace_228055 : CollatzResearch.WordTrace tailWord_228055 prefixEnd_228055 69393677428865462200711 := by
  unfold tailWord_228055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317849188803158538245619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5545232792535439025497079 8317849188803158538245619)
  ·
    refine ⟨12476773783204737807368429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317849188803158538245619 12476773783204737807368429)
    ·
      refine ⟨4678790168701776677763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12476773783204737807368429 4678790168701776677763161)
      ·
        refine ⟨3509092626526332508322371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4678790168701776677763161 3509092626526332508322371)
        ·
          refine ⟨5263638939789498762483557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509092626526332508322371 5263638939789498762483557)
          ·
            refine ⟨986932301210531017965667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5263638939789498762483557 986932301210531017965667)
            ·
              refine ⟨1480398451815796526948501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986932301210531017965667 1480398451815796526948501)
              ·
                refine ⟨69393677428865462200711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1480398451815796526948501 69393677428865462200711)
                ·
                  rfl

theorem cell19_228055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_228055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228055 prefixEnd_228055 := by exact prefixLift 228055
  have htrace : WordTrace (prefixWord ++ tailWord_228055) baseStart_228055 baseEnd_228055 := by
    simpa [prefixWord, tailWord_228055, baseEnd_228055] using wordTrace_append hprefix tailTrace_228055
  have hstable : (prefixWord ++ tailWord_228055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228055).length < 2 ^ (prefixWord ++ tailWord_228055).sum := by decide
  have hdescent : baseEnd_228055 < baseStart_228055 := by decide
  rcases family_descends (prefixWord ++ tailWord_228055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228125 : List Nat := [1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_228125 : Nat := 118140960795 + 228125 * 2 ^ 59
def prefixEnd_228125 : Nat := 4983230072969 + 3 ^ 40 * 228125 * 2
def baseEnd_228125 : Nat := 69414977367126040644965

theorem tailTrace_228125 : CollatzResearch.WordTrace tailWord_228125 prefixEnd_228125 69414977367126040644965 := by
  unfold tailWord_228125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320402298549560493293829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5546934865699706995529219 8320402298549560493293829)
  ·
    refine ⟨1560075430978042592492593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8320402298549560493293829 1560075430978042592492593)
    ·
      refine ⟨1170056573233531944369445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1560075430978042592492593 1170056573233531944369445)
      ·
        refine ⟨219385607481287239569271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1170056573233531944369445 219385607481287239569271)
        ·
          refine ⟨329078411221930859353907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219385607481287239569271 329078411221930859353907)
          ·
            refine ⟨493617616832896289030861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329078411221930859353907 493617616832896289030861)
            ·
              refine ⟨185106606312336108386573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493617616832896289030861 185106606312336108386573)
              ·
                refine ⟨69414977367126040644965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185106606312336108386573 69414977367126040644965)
                ·
                  rfl

theorem cell19_228125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_228125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228125 prefixEnd_228125 := by exact prefixLift 228125
  have htrace : WordTrace (prefixWord ++ tailWord_228125) baseStart_228125 baseEnd_228125 := by
    simpa [prefixWord, tailWord_228125, baseEnd_228125] using wordTrace_append hprefix tailTrace_228125
  have hstable : (prefixWord ++ tailWord_228125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228125).length < 2 ^ (prefixWord ++ tailWord_228125).sum := by decide
  have hdescent : baseEnd_228125 < baseStart_228125 := by decide
  rcases family_descends (prefixWord ++ tailWord_228125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228129 : List Nat := [1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_228129 : Nat := 118140960795 + 228129 * 2 ^ 59
def prefixEnd_228129 : Nat := 4983230072969 + 3 ^ 40 * 228129 * 2
def baseEnd_228129 : Nat := 69416194506455216556065

theorem tailTrace_228129 : CollatzResearch.WordTrace tailWord_228129 prefixEnd_228129 69416194506455216556065 := by
  unfold tailWord_228129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320548190535069176439441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5547032127023379450959627 8320548190535069176439441)
  ·
    refine ⟨6240411142901301882329581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8320548190535069176439441 6240411142901301882329581)
    ·
      refine ⟨2340154178587988205873593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6240411142901301882329581 2340154178587988205873593)
      ·
        refine ⟨1755115633940991154405195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2340154178587988205873593 1755115633940991154405195)
        ·
          refine ⟨2632673450911486731607793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755115633940991154405195 2632673450911486731607793)
          ·
            refine ⟨1974505088183615048705845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632673450911486731607793 1974505088183615048705845)
            ·
              refine ⟨185109852017213910816173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1974505088183615048705845 185109852017213910816173)
              ·
                refine ⟨69416194506455216556065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185109852017213910816173 69416194506455216556065)
                ·
                  rfl

theorem cell19_228129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_228129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228129 prefixEnd_228129 := by exact prefixLift 228129
  have htrace : WordTrace (prefixWord ++ tailWord_228129) baseStart_228129 baseEnd_228129 := by
    simpa [prefixWord, tailWord_228129, baseEnd_228129] using wordTrace_append hprefix tailTrace_228129
  have hstable : (prefixWord ++ tailWord_228129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228129).length < 2 ^ (prefixWord ++ tailWord_228129).sum := by decide
  have hdescent : baseEnd_228129 < baseStart_228129 := by decide
  rcases family_descends (prefixWord ++ tailWord_228129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228186 : List Nat := [3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_228186 : Nat := 118140960795 + 228186 * 2 ^ 59
def prefixEnd_228186 : Nat := 4983230072969 + 3 ^ 40 * 228186 * 2
def baseEnd_228186 : Nat := 69433538741895973289243

theorem tailTrace_228186 : CollatzResearch.WordTrace tailWord_228186 prefixEnd_228186 69433538741895973289243 := by
  unfold tailWord_228186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080656787832141977816103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5548418100885711940842941 2080656787832141977816103)
  ·
    refine ⟨3120985181748212966724155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080656787832141977816103 3120985181748212966724155)
    ·
      refine ⟨4681477772622319450086233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120985181748212966724155 4681477772622319450086233)
      ·
        refine ⟨3511108329466739587564675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4681477772622319450086233 3511108329466739587564675)
        ·
          refine ⟨5266662494200109381347013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511108329466739587564675 5266662494200109381347013)
          ·
            refine ⟨987499217662520509002565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5266662494200109381347013 987499217662520509002565)
            ·
              refine ⟨185156103311722595437981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 987499217662520509002565 185156103311722595437981)
              ·
                refine ⟨69433538741895973289243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185156103311722595437981 69433538741895973289243)
                ·
                  rfl

theorem cell19_228186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_228186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228186 prefixEnd_228186 := by exact prefixLift 228186
  have htrace : WordTrace (prefixWord ++ tailWord_228186) baseStart_228186 baseEnd_228186 := by
    simpa [prefixWord, tailWord_228186, baseEnd_228186] using wordTrace_append hprefix tailTrace_228186
  have hstable : (prefixWord ++ tailWord_228186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228186).length < 2 ^ (prefixWord ++ tailWord_228186).sum := by decide
  have hdescent : baseEnd_228186 < baseStart_228186 := by decide
  rcases family_descends (prefixWord ++ tailWord_228186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228245 : List Nat := [1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_228245 : Nat := 118140960795 + 228245 * 2 ^ 59
def prefixEnd_228245 : Nat := 4983230072969 + 3 ^ 40 * 228245 * 2
def baseEnd_228245 : Nat := 69451491547001317977971

theorem tailTrace_228245 : CollatzResearch.WordTrace tailWord_228245 prefixEnd_228245 69451491547001317977971 := by
  unfold tailWord_228245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8324779058114820987662189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5549852705409880658441459 8324779058114820987662189)
  ·
    refine ⟨3121792146793057870373321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8324779058114820987662189 3121792146793057870373321)
    ·
      refine ⟨2341344110094793402779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3121792146793057870373321 2341344110094793402779991)
      ·
        refine ⟨3512016165142190104169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341344110094793402779991 3512016165142190104169987)
        ·
          refine ⟨5268024247713285156254981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512016165142190104169987 5268024247713285156254981)
          ·
            refine ⟨987754546446240966797809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5268024247713285156254981 987754546446240966797809)
            ·
              refine ⟨740815909834680725098357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987754546446240966797809 740815909834680725098357)
              ·
                refine ⟨69451491547001317977971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740815909834680725098357 69451491547001317977971)
                ·
                  rfl

theorem cell19_228245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_228245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228245 prefixEnd_228245 := by exact prefixLift 228245
  have htrace : WordTrace (prefixWord ++ tailWord_228245) baseStart_228245 baseEnd_228245 := by
    simpa [prefixWord, tailWord_228245, baseEnd_228245] using wordTrace_append hprefix tailTrace_228245
  have hstable : (prefixWord ++ tailWord_228245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228245).length < 2 ^ (prefixWord ++ tailWord_228245).sum := by decide
  have hdescent : baseEnd_228245 < baseStart_228245 := by decide
  rcases family_descends (prefixWord ++ tailWord_228245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228264 : List Nat := [2, 1, 6, 10]
def baseStart_228264 : Nat := 118140960795 + 228264 * 2 ^ 59
def prefixEnd_228264 : Nat := 4983230072969 + 3 ^ 40 * 228264 * 2
def baseEnd_228264 : Nat := 857497197022406216737

theorem tailTrace_228264 : CollatzResearch.WordTrace tailWord_228264 prefixEnd_228264 857497197022406216737 := by
  unfold tailWord_228264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162736022522993616301923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5550314696697324821735897 4162736022522993616301923)
  ·
    refine ⟨6244104033784490424452885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162736022522993616301923 6244104033784490424452885)
    ·
      refine ⟨292692376583647988646229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6244104033784490424452885 292692376583647988646229)
      ·
        refine ⟨857497197022406216737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 292692376583647988646229 857497197022406216737)
        ·
          rfl

theorem cell19_228264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 10].length) (baseStart_228264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228264 prefixEnd_228264 := by exact prefixLift 228264
  have htrace : WordTrace (prefixWord ++ tailWord_228264) baseStart_228264 baseEnd_228264 := by
    simpa [prefixWord, tailWord_228264, baseEnd_228264] using wordTrace_append hprefix tailTrace_228264
  have hstable : (prefixWord ++ tailWord_228264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228264).length < 2 ^ (prefixWord ++ tailWord_228264).sum := by decide
  have hdescent : baseEnd_228264 < baseStart_228264 := by decide
  rcases family_descends (prefixWord ++ tailWord_228264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228281 : List Nat := [1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_228281 : Nat := 118140960795 + 228281 * 2 ^ 59
def prefixEnd_228281 : Nat := 4983230072969 + 3 ^ 40 * 228281 * 2
def baseEnd_228281 : Nat := 69462445800963901177873

theorem tailTrace_228281 : CollatzResearch.WordTrace tailWord_228281 prefixEnd_228281 69462445800963901177873 := by
  unfold tailWord_228281
  simp only [CollatzResearch.WordTrace]
  refine ⟨8326092085984399135972697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5550728057322932757315131 8326092085984399135972697)
  ·
    refine ⟨6244569064488299351979523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8326092085984399135972697 6244569064488299351979523)
    ·
      refine ⟨9366853596732449027969285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6244569064488299351979523 9366853596732449027969285)
      ·
        refine ⟨1756285049387334192744241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9366853596732449027969285 1756285049387334192744241)
        ·
          refine ⟨1317213787040500644558181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756285049387334192744241 1317213787040500644558181)
          ·
            refine ⟨246977585070093870854659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1317213787040500644558181 246977585070093870854659)
            ·
              refine ⟨370466377605140806281989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246977585070093870854659 370466377605140806281989)
              ·
                refine ⟨69462445800963901177873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370466377605140806281989 69462445800963901177873)
                ·
                  rfl

theorem cell19_228281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_228281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228281 prefixEnd_228281 := by exact prefixLift 228281
  have htrace : WordTrace (prefixWord ++ tailWord_228281) baseStart_228281 baseEnd_228281 := by
    simpa [prefixWord, tailWord_228281, baseEnd_228281] using wordTrace_append hprefix tailTrace_228281
  have hstable : (prefixWord ++ tailWord_228281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228281).length < 2 ^ (prefixWord ++ tailWord_228281).sum := by decide
  have hdescent : baseEnd_228281 < baseStart_228281 := by decide
  rcases family_descends (prefixWord ++ tailWord_228281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228300 : List Nat := [2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_228300 : Nat := 118140960795 + 228300 * 2 ^ 59
def prefixEnd_228300 : Nat := 4983230072969 + 3 ^ 40 * 228300 * 2
def baseEnd_228300 : Nat := 69468227212777486755599

theorem tailTrace_228300 : CollatzResearch.WordTrace tailWord_228300 prefixEnd_228300 69468227212777486755599 := by
  unfold tailWord_228300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163392536457782690457177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5551190048610376920609569 4163392536457782690457177)
  ·
    refine ⟨3122544402343337017842883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4163392536457782690457177 3122544402343337017842883)
    ·
      refine ⟨4683816603515005526764325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122544402343337017842883 4683816603515005526764325)
      ·
        refine ⟨878215613159063536268311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4683816603515005526764325 878215613159063536268311)
        ·
          refine ⟨1317323419738595304402467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878215613159063536268311 1317323419738595304402467)
          ·
            refine ⟨1975985129607892956603701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317323419738595304402467 1975985129607892956603701)
            ·
              refine ⟨185248605900739964681597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1975985129607892956603701 185248605900739964681597)
              ·
                refine ⟨69468227212777486755599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185248605900739964681597 69468227212777486755599)
                ·
                  rfl

theorem cell19_228300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_228300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228300 prefixEnd_228300 := by exact prefixLift 228300
  have htrace : WordTrace (prefixWord ++ tailWord_228300) baseStart_228300 baseEnd_228300 := by
    simpa [prefixWord, tailWord_228300, baseEnd_228300] using wordTrace_append hprefix tailTrace_228300
  have hstable : (prefixWord ++ tailWord_228300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228300).length < 2 ^ (prefixWord ++ tailWord_228300).sum := by decide
  have hdescent : baseEnd_228300 < baseStart_228300 := by decide
  rcases family_descends (prefixWord ++ tailWord_228300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228359 : List Nat := [1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_228359 : Nat := 118140960795 + 228359 * 2 ^ 59
def prefixEnd_228359 : Nat := 4983230072969 + 3 ^ 40 * 228359 * 2
def baseEnd_228359 : Nat := 69486180017882831444327

theorem tailTrace_228359 : CollatzResearch.WordTrace tailWord_228359 prefixEnd_228359 69486180017882831444327 := by
  unfold tailWord_228359
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328936979701818457312131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5552624653134545638208087 8328936979701818457312131)
  ·
    refine ⟨12493405469552727685968197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328936979701818457312131 12493405469552727685968197)
    ·
      refine ⟨2342513525541136441119037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12493405469552727685968197 2342513525541136441119037)
      ·
        refine ⟨878442572077926165419639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2342513525541136441119037 878442572077926165419639)
        ·
          refine ⟨1317663858116889248129459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878442572077926165419639 1317663858116889248129459)
          ·
            refine ⟨1976495787175333872194189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317663858116889248129459 1976495787175333872194189)
            ·
              refine ⟨741185920190750202072821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976495787175333872194189 741185920190750202072821)
              ·
                refine ⟨69486180017882831444327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741185920190750202072821 69486180017882831444327)
                ·
                  rfl

theorem cell19_228359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_228359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228359 prefixEnd_228359 := by exact prefixLift 228359
  have htrace : WordTrace (prefixWord ++ tailWord_228359) baseStart_228359 baseEnd_228359 := by
    simpa [prefixWord, tailWord_228359, baseEnd_228359] using wordTrace_append hprefix tailTrace_228359
  have hstable : (prefixWord ++ tailWord_228359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228359).length < 2 ^ (prefixWord ++ tailWord_228359).sum := by decide
  have hdescent : baseEnd_228359 < baseStart_228359 := by decide
  rcases family_descends (prefixWord ++ tailWord_228359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228370 : List Nat := [3, 2, 5, 1, 2, 1, 5]
def baseStart_228370 : Nat := 118140960795 + 228370 * 2 ^ 59
def prefixEnd_228370 : Nat := 4983230072969 + 3 ^ 40 * 228370 * 2
def baseEnd_228370 : Nat := 23163175717012688399951

theorem tailTrace_228370 : CollatzResearch.WordTrace tailWord_228370 prefixEnd_228370 23163175717012688399951 := by
  unfold tailWord_228370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082334545665491833990641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5552892121774644890641709 2082334545665491833990641)
  ·
    refine ⟨1561750909249118875492981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2082334545665491833990641 1561750909249118875492981)
    ·
      refine ⟨146414147742104894577467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1561750909249118875492981 146414147742104894577467)
      ·
        refine ⟨219621221613157341866201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146414147742104894577467 219621221613157341866201)
        ·
          refine ⟨164715916209868006399651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219621221613157341866201 164715916209868006399651)
          ·
            refine ⟨247073874314802009599477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164715916209868006399651 247073874314802009599477)
            ·
              refine ⟨23163175717012688399951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247073874314802009599477 23163175717012688399951)
              ·
                rfl

theorem cell19_228370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_228370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228370 prefixEnd_228370 := by exact prefixLift 228370
  have htrace : WordTrace (prefixWord ++ tailWord_228370) baseStart_228370 baseEnd_228370 := by
    simpa [prefixWord, tailWord_228370, baseEnd_228370] using wordTrace_append hprefix tailTrace_228370
  have hstable : (prefixWord ++ tailWord_228370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228370).length < 2 ^ (prefixWord ++ tailWord_228370).sum := by decide
  have hdescent : baseEnd_228370 < baseStart_228370 := by decide
  rcases family_descends (prefixWord ++ tailWord_228370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228414 : List Nat := [4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_228414 : Nat := 118140960795 + 228414 * 2 ^ 59
def prefixEnd_228414 : Nat := 4983230072969 + 3 ^ 40 * 228414 * 2
def baseEnd_228414 : Nat := 69502915683659000221955

theorem tailTrace_228414 : CollatzResearch.WordTrace tailWord_228414 prefixEnd_228414 69502915683659000221955 := by
  unfold tailWord_228414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041367874312820356320537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5553961996335041900376197 1041367874312820356320537)
  ·
    refine ⟨781025905734615267240403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041367874312820356320537 781025905734615267240403)
    ·
      refine ⟨1171538858601922900860605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781025905734615267240403 1171538858601922900860605)
      ·
        refine ⟨439327071975721087822727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1171538858601922900860605 439327071975721087822727)
        ·
          refine ⟨658990607963581631734091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439327071975721087822727 658990607963581631734091)
          ·
            refine ⟨988485911945372447601137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658990607963581631734091 988485911945372447601137)
            ·
              refine ⟨741364433959029335700853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988485911945372447601137 741364433959029335700853)
              ·
                refine ⟨69502915683659000221955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741364433959029335700853 69502915683659000221955)
                ·
                  rfl

theorem cell19_228414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_228414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228414 prefixEnd_228414 := by exact prefixLift 228414
  have htrace : WordTrace (prefixWord ++ tailWord_228414) baseStart_228414 baseEnd_228414 := by
    simpa [prefixWord, tailWord_228414, baseEnd_228414] using wordTrace_append hprefix tailTrace_228414
  have hstable : (prefixWord ++ tailWord_228414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228414).length < 2 ^ (prefixWord ++ tailWord_228414).sum := by decide
  have hdescent : baseEnd_228414 < baseStart_228414 := by decide
  rcases family_descends (prefixWord ++ tailWord_228414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228450 : List Nat := [3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_228450 : Nat := 118140960795 + 228450 * 2 ^ 59
def prefixEnd_228450 : Nat := 4983230072969 + 3 ^ 40 * 228450 * 2
def baseEnd_228450 : Nat := 69513869937621583421857

theorem tailTrace_228450 : CollatzResearch.WordTrace tailWord_228450 prefixEnd_228450 69513869937621583421857 := by
  unfold tailWord_228450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083064005593035249718701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5554837348248093999249869 2083064005593035249718701)
  ·
    refine ⟨781149002097388218644513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2083064005593035249718701 781149002097388218644513)
    ·
      refine ⟨585861751573041163983385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781149002097388218644513 585861751573041163983385)
      ·
        refine ⟨439396313679780872987539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585861751573041163983385 439396313679780872987539)
        ·
          refine ⟨659094470519671309481309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439396313679780872987539 659094470519671309481309)
          ·
            refine ⟨247160426444876741055491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 659094470519671309481309 247160426444876741055491)
            ·
              refine ⟨370740639667315111583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247160426444876741055491 370740639667315111583237)
              ·
                refine ⟨69513869937621583421857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370740639667315111583237 69513869937621583421857)
                ·
                  rfl

theorem cell19_228450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_228450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228450 prefixEnd_228450 := by exact prefixLift 228450
  have htrace : WordTrace (prefixWord ++ tailWord_228450) baseStart_228450 baseEnd_228450 := by
    simpa [prefixWord, tailWord_228450, baseEnd_228450] using wordTrace_append hprefix tailTrace_228450
  have hstable : (prefixWord ++ tailWord_228450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228450).length < 2 ^ (prefixWord ++ tailWord_228450).sum := by decide
  have hdescent : baseEnd_228450 < baseStart_228450 := by decide
  rcases family_descends (prefixWord ++ tailWord_228450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228475 : List Nat := [1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_228475 : Nat := 118140960795 + 228475 * 2 ^ 59
def prefixEnd_228475 : Nat := 4983230072969 + 3 ^ 40 * 228475 * 2
def baseEnd_228475 : Nat := 69521477058428932866233

theorem tailTrace_228475 : CollatzResearch.WordTrace tailWord_228475 prefixEnd_228475 69521477058428932866233 := by
  unfold tailWord_228475
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333167847281570268534879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5555445231521046845689919 8333167847281570268534879)
  ·
    refine ⟨12499751770922355402802319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333167847281570268534879 12499751770922355402802319)
    ·
      refine ⟨18749627656383533104203479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12499751770922355402802319 18749627656383533104203479)
      ·
        refine ⟨28124441484575299656305219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18749627656383533104203479 28124441484575299656305219)
        ·
          refine ⟨42186662226862949484457829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28124441484575299656305219 42186662226862949484457829)
          ·
            refine ⟨7909999167536803028335843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42186662226862949484457829 7909999167536803028335843)
            ·
              refine ⟨11864998751305204542503765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909999167536803028335843 11864998751305204542503765)
              ·
                refine ⟨69521477058428932866233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11864998751305204542503765 69521477058428932866233)
                ·
                  rfl

theorem cell19_228475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_228475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228475 prefixEnd_228475 := by exact prefixLift 228475
  have htrace : WordTrace (prefixWord ++ tailWord_228475) baseStart_228475 baseEnd_228475 := by
    simpa [prefixWord, tailWord_228475, baseEnd_228475] using wordTrace_append hprefix tailTrace_228475
  have hstable : (prefixWord ++ tailWord_228475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228475).length < 2 ^ (prefixWord ++ tailWord_228475).sum := by decide
  have hdescent : baseEnd_228475 < baseStart_228475 := by decide
  rcases family_descends (prefixWord ++ tailWord_228475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228530 : List Nat := [3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_228530 : Nat := 118140960795 + 228530 * 2 ^ 59
def prefixEnd_228530 : Nat := 4983230072969 + 3 ^ 40 * 228530 * 2
def baseEnd_228530 : Nat := 69538212724205101643861

theorem tailTrace_228530 : CollatzResearch.WordTrace tailWord_228530 prefixEnd_228530 69538212724205101643861 := by
  unfold tailWord_228530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083793465520578665446761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5556782574721543107858029 2083793465520578665446761)
  ·
    refine ⟨1562845099140433999085071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2083793465520578665446761 1562845099140433999085071)
    ·
      refine ⟨2344267648710650998627607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562845099140433999085071 2344267648710650998627607)
      ·
        refine ⟨3516401473065976497941411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344267648710650998627607 3516401473065976497941411)
        ·
          refine ⟨5274602209598964746912117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516401473065976497941411 5274602209598964746912117)
          ·
            refine ⟨494493957149902945023011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5274602209598964746912117 494493957149902945023011)
            ·
              refine ⟨741740935724854417534517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494493957149902945023011 741740935724854417534517)
              ·
                refine ⟨69538212724205101643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741740935724854417534517 69538212724205101643861)
                ·
                  rfl

theorem cell19_228530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_228530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228530 prefixEnd_228530 := by exact prefixLift 228530
  have htrace : WordTrace (prefixWord ++ tailWord_228530) baseStart_228530 baseEnd_228530 := by
    simpa [prefixWord, tailWord_228530, baseEnd_228530] using wordTrace_append hprefix tailTrace_228530
  have hstable : (prefixWord ++ tailWord_228530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228530).length < 2 ^ (prefixWord ++ tailWord_228530).sum := by decide
  have hdescent : baseEnd_228530 < baseStart_228530 := by decide
  rcases family_descends (prefixWord ++ tailWord_228530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228564 : List Nat := [2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_228564 : Nat := 118140960795 + 228564 * 2 ^ 59
def prefixEnd_228564 : Nat := 4983230072969 + 3 ^ 40 * 228564 * 2
def baseEnd_228564 : Nat := 69548558408503096888213

theorem tailTrace_228564 : CollatzResearch.WordTrace tailWord_228564 prefixEnd_228564 69548558408503096888213 := by
  unfold tailWord_228564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168206971979569234262373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5557609295972758979016497 4168206971979569234262373)
  ·
    refine ⟨781538807246169231424195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4168206971979569234262373 781538807246169231424195)
    ·
      refine ⟨1172308210869253847136293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 781538807246169231424195 1172308210869253847136293)
      ·
        refine ⟨219807789537985096338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1172308210869253847136293 219807789537985096338055)
        ·
          refine ⟨329711684306977644507083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219807789537985096338055 329711684306977644507083)
          ·
            refine ⟨494567526460466466760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329711684306977644507083 494567526460466466760625)
            ·
              refine ⟨370925644845349850070469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494567526460466466760625 370925644845349850070469)
              ·
                refine ⟨69548558408503096888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 370925644845349850070469 69548558408503096888213)
                ·
                  rfl

theorem cell19_228564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_228564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228564 prefixEnd_228564 := by exact prefixLift 228564
  have htrace : WordTrace (prefixWord ++ tailWord_228564) baseStart_228564 baseEnd_228564 := by
    simpa [prefixWord, tailWord_228564, baseEnd_228564] using wordTrace_append hprefix tailTrace_228564
  have hstable : (prefixWord ++ tailWord_228564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228564).length < 2 ^ (prefixWord ++ tailWord_228564).sum := by decide
  have hdescent : baseEnd_228564 < baseStart_228564 := by decide
  rcases family_descends (prefixWord ++ tailWord_228564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228606 : List Nat := [4, 2, 2, 1, 1, 9]
def baseStart_228606 : Nat := 118140960795 + 228606 * 2 ^ 59
def prefixEnd_228606 : Nat := 4983230072969 + 3 ^ 40 * 228606 * 2
def baseEnd_228606 : Nat := 7729037596828827106085

theorem tailTrace_228606 : CollatzResearch.WordTrace tailWord_228606 prefixEnd_228606 7729037596828827106085 := by
  unfold tailWord_228606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042243226225872455194209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5558630539871319761035781 1042243226225872455194209)
  ·
    refine ⟨781682419669404341395657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042243226225872455194209 781682419669404341395657)
    ·
      refine ⟨586261814752053256046743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781682419669404341395657 586261814752053256046743)
      ·
        refine ⟨879392722128079884070115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586261814752053256046743 879392722128079884070115)
        ·
          refine ⟨1319089083192119826105173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879392722128079884070115 1319089083192119826105173)
          ·
            refine ⟨7729037596828827106085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1319089083192119826105173 7729037596828827106085)
            ·
              rfl

theorem cell19_228606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_228606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228606 prefixEnd_228606 := by exact prefixLift 228606
  have htrace : WordTrace (prefixWord ++ tailWord_228606) baseStart_228606 baseEnd_228606 := by
    simpa [prefixWord, tailWord_228606, baseEnd_228606] using wordTrace_append hprefix tailTrace_228606
  have hstable : (prefixWord ++ tailWord_228606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228606).length < 2 ^ (prefixWord ++ tailWord_228606).sum := by decide
  have hdescent : baseEnd_228606 < baseStart_228606 := by decide
  rcases family_descends (prefixWord ++ tailWord_228606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228638 : List Nat := [4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_228638 : Nat := 118140960795 + 228638 * 2 ^ 59
def prefixEnd_228638 : Nat := 4983230072969 + 3 ^ 40 * 228638 * 2
def baseEnd_228638 : Nat := 69571075486092851243567

theorem tailTrace_228638 : CollatzResearch.WordTrace tailWord_228638 prefixEnd_228638 69571075486092851243567 := by
  unfold tailWord_228638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042389118211381138339821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5559408630460699404479045 1042389118211381138339821)
  ·
    refine ⟨390895919329267926877433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1042389118211381138339821 390895919329267926877433)
    ·
      refine ⟨293171939496950945158075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 390895919329267926877433 293171939496950945158075)
      ·
        refine ⟨439757909245426417737113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293171939496950945158075 439757909245426417737113)
        ·
          refine ⟨329818431934069813302835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439757909245426417737113 329818431934069813302835)
          ·
            refine ⟨494727647901104719954253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329818431934069813302835 494727647901104719954253)
            ·
              refine ⟨185522867962914269982845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494727647901104719954253 185522867962914269982845)
              ·
                refine ⟨69571075486092851243567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185522867962914269982845 69571075486092851243567)
                ·
                  rfl

theorem cell19_228638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_228638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228638 prefixEnd_228638 := by exact prefixLift 228638
  have htrace : WordTrace (prefixWord ++ tailWord_228638) baseStart_228638 baseEnd_228638 := by
    simpa [prefixWord, tailWord_228638, baseEnd_228638] using wordTrace_append hprefix tailTrace_228638
  have hstable : (prefixWord ++ tailWord_228638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228638).length < 2 ^ (prefixWord ++ tailWord_228638).sum := by decide
  have hdescent : baseEnd_228638 < baseStart_228638 := by decide
  rcases family_descends (prefixWord ++ tailWord_228638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228737 : List Nat := [1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_228737 : Nat := 118140960795 + 228737 * 2 ^ 59
def prefixEnd_228737 : Nat := 4983230072969 + 3 ^ 40 * 228737 * 2
def baseEnd_228737 : Nat := 69601199684489955043297

theorem tailTrace_228737 : CollatzResearch.WordTrace tailWord_228737 prefixEnd_228737 69601199684489955043297 := by
  unfold tailWord_228737
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342723772332389014572465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561815848221592676381643 8342723772332389014572465)
  ·
    refine ⟨6257042829249291760929349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8342723772332389014572465 6257042829249291760929349)
    ·
      refine ⟨1173195530484242205174253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6257042829249291760929349 1173195530484242205174253)
      ·
        refine ⟨439948323931590826940345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1173195530484242205174253 439948323931590826940345)
        ·
          refine ⟨329961242948693120205259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439948323931590826940345 329961242948693120205259)
          ·
            refine ⟨494941864423039680307889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329961242948693120205259 494941864423039680307889)
            ·
              refine ⟨371206398317279760230917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494941864423039680307889 371206398317279760230917)
              ·
                refine ⟨69601199684489955043297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371206398317279760230917 69601199684489955043297)
                ·
                  rfl

theorem cell19_228737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_228737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228737 prefixEnd_228737 := by exact prefixLift 228737
  have htrace : WordTrace (prefixWord ++ tailWord_228737) baseStart_228737 baseEnd_228737 := by
    simpa [prefixWord, tailWord_228737, baseEnd_228737] using wordTrace_append hprefix tailTrace_228737
  have hstable : (prefixWord ++ tailWord_228737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228737).length < 2 ^ (prefixWord ++ tailWord_228737).sum := by decide
  have hdescent : baseEnd_228737 < baseStart_228737 := by decide
  rcases family_descends (prefixWord ++ tailWord_228737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228739 : List Nat := [1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_228739 : Nat := 118140960795 + 228739 * 2 ^ 59
def prefixEnd_228739 : Nat := 4983230072969 + 3 ^ 40 * 228739 * 2
def baseEnd_228739 : Nat := 69601808254154542998847

theorem tailTrace_228739 : CollatzResearch.WordTrace tailWord_228739 prefixEnd_228739 69601808254154542998847 := by
  unfold tailWord_228739
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342796718325143356145271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561864478883428904096847 8342796718325143356145271)
  ·
    refine ⟨12514195077487715034217907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342796718325143356145271 12514195077487715034217907)
    ·
      refine ⟨18771292616231572551326861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12514195077487715034217907 18771292616231572551326861)
      ·
        refine ⟨7039234731086839706747573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18771292616231572551326861 7039234731086839706747573)
        ·
          refine ⟨659928256039391222507585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7039234731086839706747573 659928256039391222507585)
          ·
            refine ⟨494946192029543416880689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659928256039391222507585 494946192029543416880689)
            ·
              refine ⟨371209644022157562660517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494946192029543416880689 371209644022157562660517)
              ·
                refine ⟨69601808254154542998847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371209644022157562660517 69601808254154542998847)
                ·
                  rfl

theorem cell19_228739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_228739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228739 prefixEnd_228739 := by exact prefixLift 228739
  have htrace : WordTrace (prefixWord ++ tailWord_228739) baseStart_228739 baseEnd_228739 := by
    simpa [prefixWord, tailWord_228739, baseEnd_228739] using wordTrace_append hprefix tailTrace_228739
  have hstable : (prefixWord ++ tailWord_228739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228739).length < 2 ^ (prefixWord ++ tailWord_228739).sum := by decide
  have hdescent : baseEnd_228739 < baseStart_228739 := by decide
  rcases family_descends (prefixWord ++ tailWord_228739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228741 : List Nat := [1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_228741 : Nat := 118140960795 + 228741 * 2 ^ 59
def prefixEnd_228741 : Nat := 4983230072969 + 3 ^ 40 * 228741 * 2
def baseEnd_228741 : Nat := 69602416823819130954397

theorem tailTrace_228741 : CollatzResearch.WordTrace tailWord_228741 prefixEnd_228741 69602416823819130954397 := by
  unfold tailWord_228741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342869664317897697718077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5561913109545265131812051 8342869664317897697718077)
  ·
    refine ⟨3128576124119211636644279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8342869664317897697718077 3128576124119211636644279)
    ·
      refine ⟨4692864186178817454966419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128576124119211636644279 4692864186178817454966419)
      ·
        refine ⟨7039296279268226182449629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692864186178817454966419 7039296279268226182449629)
        ·
          refine ⟨2639736104725584818418611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7039296279268226182449629 2639736104725584818418611)
          ·
            refine ⟨3959604157088377227627917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639736104725584818418611 3959604157088377227627917)
            ·
              refine ⟨1484851558908141460360469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959604157088377227627917 1484851558908141460360469)
              ·
                refine ⟨69602416823819130954397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484851558908141460360469 69602416823819130954397)
                ·
                  rfl

theorem cell19_228741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_228741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228741 prefixEnd_228741 := by exact prefixLift 228741
  have htrace : WordTrace (prefixWord ++ tailWord_228741) baseStart_228741 baseEnd_228741 := by
    simpa [prefixWord, tailWord_228741, baseEnd_228741] using wordTrace_append hprefix tailTrace_228741
  have hstable : (prefixWord ++ tailWord_228741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228741).length < 2 ^ (prefixWord ++ tailWord_228741).sum := by decide
  have hdescent : baseEnd_228741 < baseStart_228741 := by decide
  rcases family_descends (prefixWord ++ tailWord_228741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228868 : List Nat := [2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_228868 : Nat := 118140960795 + 228868 * 2 ^ 59
def prefixEnd_228868 : Nat := 4983230072969 + 3 ^ 40 * 228868 * 2
def baseEnd_228868 : Nat := 69641060997520466131829

theorem tailTrace_228868 : CollatzResearch.WordTrace tailWord_228868 prefixEnd_228868 69641060997520466131829 := by
  unfold tailWord_228868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173750867428899193795629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5565001156571865591727505 4173750867428899193795629)
  ·
    refine ⟨1565156575285837197673361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4173750867428899193795629 1565156575285837197673361)
    ·
      refine ⟨1173867431464377898255021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565156575285837197673361 1173867431464377898255021)
      ·
        refine ⟨440200286799141711845633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1173867431464377898255021 440200286799141711845633)
        ·
          refine ⟨330150215099356283884225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440200286799141711845633 330150215099356283884225)
          ·
            refine ⟨247612661324517212913169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330150215099356283884225 247612661324517212913169)
            ·
              refine ⟨185709495993387909684877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247612661324517212913169 185709495993387909684877)
              ·
                refine ⟨69641060997520466131829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185709495993387909684877 69641060997520466131829)
                ·
                  rfl

theorem cell19_228868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_228868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228868 prefixEnd_228868 := by exact prefixLift 228868
  have htrace : WordTrace (prefixWord ++ tailWord_228868) baseStart_228868 baseEnd_228868 := by
    simpa [prefixWord, tailWord_228868, baseEnd_228868] using wordTrace_append hprefix tailTrace_228868
  have hstable : (prefixWord ++ tailWord_228868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228868).length < 2 ^ (prefixWord ++ tailWord_228868).sum := by decide
  have hdescent : baseEnd_228868 < baseStart_228868 := by decide
  rcases family_descends (prefixWord ++ tailWord_228868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228872 : List Nat := [2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_228872 : Nat := 118140960795 + 228872 * 2 ^ 59
def prefixEnd_228872 : Nat := 4983230072969 + 3 ^ 40 * 228872 * 2
def baseEnd_228872 : Nat := 69642278136849642042929

theorem tailTrace_228872 : CollatzResearch.WordTrace tailWord_228872 prefixEnd_228872 69642278136849642042929 := by
  unfold tailWord_228872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173823813421653535368435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5565098417895538047157913 4173823813421653535368435)
  ·
    refine ⟨6260735720132480303052653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173823813421653535368435 6260735720132480303052653)
    ·
      refine ⟨2347775895049680113644745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6260735720132480303052653 2347775895049680113644745)
      ·
        refine ⟨1760831921287260085233559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2347775895049680113644745 1760831921287260085233559)
        ·
          refine ⟨2641247881930890127850339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760831921287260085233559 2641247881930890127850339)
          ·
            refine ⟨3961871822896335191775509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641247881930890127850339 3961871822896335191775509)
            ·
              refine ⟨185712741698265712114477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3961871822896335191775509 185712741698265712114477)
              ·
                refine ⟨69642278136849642042929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185712741698265712114477 69642278136849642042929)
                ·
                  rfl

theorem cell19_228872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_228872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228872 prefixEnd_228872 := by exact prefixLift 228872
  have htrace : WordTrace (prefixWord ++ tailWord_228872) baseStart_228872 baseEnd_228872 := by
    simpa [prefixWord, tailWord_228872, baseEnd_228872] using wordTrace_append hprefix tailTrace_228872
  have hstable : (prefixWord ++ tailWord_228872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228872).length < 2 ^ (prefixWord ++ tailWord_228872).sum := by decide
  have hdescent : baseEnd_228872 < baseStart_228872 := by decide
  rcases family_descends (prefixWord ++ tailWord_228872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228910 : List Nat := [4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_228910 : Nat := 118140960795 + 228910 * 2 ^ 59
def prefixEnd_228910 : Nat := 4983230072969 + 3 ^ 40 * 228910 * 2
def baseEnd_228910 : Nat := 69653840960476813198381

theorem tailTrace_228910 : CollatzResearch.WordTrace tailWord_228910 prefixEnd_228910 69653840960476813198381 := by
  unfold tailWord_228910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043629200088204945077523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5566022400470426373746789 1043629200088204945077523)
  ·
    refine ⟨1565443800132307417616285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043629200088204945077523 1565443800132307417616285)
    ·
      refine ⟨587041425049615281606107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1565443800132307417616285 587041425049615281606107)
      ·
        refine ⟨880562137574422922409161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587041425049615281606107 880562137574422922409161)
        ·
          refine ⟨660421603180817191806871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880562137574422922409161 660421603180817191806871)
          ·
            refine ⟨990632404771225787710307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660421603180817191806871 990632404771225787710307)
            ·
              refine ⟨1485948607156838681565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990632404771225787710307 1485948607156838681565461)
              ·
                refine ⟨69653840960476813198381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1485948607156838681565461 69653840960476813198381)
                ·
                  rfl

theorem cell19_228910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_228910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228910 prefixEnd_228910 := by exact prefixLift 228910
  have htrace : WordTrace (prefixWord ++ tailWord_228910) baseStart_228910 baseEnd_228910 := by
    simpa [prefixWord, tailWord_228910, baseEnd_228910] using wordTrace_append hprefix tailTrace_228910
  have hstable : (prefixWord ++ tailWord_228910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228910).length < 2 ^ (prefixWord ++ tailWord_228910).sum := by decide
  have hdescent : baseEnd_228910 < baseStart_228910 := by decide
  rcases family_descends (prefixWord ++ tailWord_228910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_228969 : List Nat := [1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_228969 : Nat := 118140960795 + 228969 * 2 ^ 59
def prefixEnd_228969 : Nat := 4983230072969 + 3 ^ 40 * 228969 * 2
def baseEnd_228969 : Nat := 69671793765582157887109

theorem tailTrace_228969 : CollatzResearch.WordTrace tailWord_228969 prefixEnd_228969 69671793765582157887109 := by
  unfold tailWord_228969
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351185507491892637017961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5567457004994595091345307 8351185507491892637017961)
  ·
    refine ⟨6263389130618919477763471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8351185507491892637017961 6263389130618919477763471)
    ·
      refine ⟨9395083695928379216645207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263389130618919477763471 9395083695928379216645207)
      ·
        refine ⟨14092625543892568824967811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395083695928379216645207 14092625543892568824967811)
        ·
          refine ⟨21138938315838853237451717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092625543892568824967811 21138938315838853237451717)
          ·
            refine ⟨3963550934219784982022197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21138938315838853237451717 3963550934219784982022197)
            ·
              refine ⟨371582900083104842064581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3963550934219784982022197 371582900083104842064581)
              ·
                refine ⟨69671793765582157887109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371582900083104842064581 69671793765582157887109)
                ·
                  rfl

theorem cell19_228969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_228969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_228969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_228969 prefixEnd_228969 := by exact prefixLift 228969
  have htrace : WordTrace (prefixWord ++ tailWord_228969) baseStart_228969 baseEnd_228969 := by
    simpa [prefixWord, tailWord_228969, baseEnd_228969] using wordTrace_append hprefix tailTrace_228969
  have hstable : (prefixWord ++ tailWord_228969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_228969).length < 2 ^ (prefixWord ++ tailWord_228969).sum := by decide
  have hdescent : baseEnd_228969 < baseStart_228969 := by decide
  rcases family_descends (prefixWord ++ tailWord_228969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229102 : List Nat := [4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_229102 : Nat := 118140960795 + 229102 * 2 ^ 59
def prefixEnd_229102 : Nat := 4983230072969 + 3 ^ 40 * 229102 * 2
def baseEnd_229102 : Nat := 69712263648277256931191

theorem tailTrace_229102 : CollatzResearch.WordTrace tailWord_229102 prefixEnd_229102 69712263648277256931191 := by
  unfold tailWord_229102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044504552001257043951195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5570690944006704234406373 1044504552001257043951195)
  ·
    refine ⟨1566756828001885565926793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044504552001257043951195 1566756828001885565926793)
    ·
      refine ⟨1175067621001414174445095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1566756828001885565926793 1175067621001414174445095)
      ·
        refine ⟨1762601431502121261667643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175067621001414174445095 1762601431502121261667643)
        ·
          refine ⟨2643902147253181892501465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762601431502121261667643 2643902147253181892501465)
          ·
            refine ⟨1982926610439886419376099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643902147253181892501465 1982926610439886419376099)
            ·
              refine ⟨2974389915659829629064149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982926610439886419376099 2974389915659829629064149)
              ·
                refine ⟨69712263648277256931191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2974389915659829629064149 69712263648277256931191)
                ·
                  rfl

theorem cell19_229102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_229102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229102 prefixEnd_229102 := by exact prefixLift 229102
  have htrace : WordTrace (prefixWord ++ tailWord_229102) baseStart_229102 baseEnd_229102 := by
    simpa [prefixWord, tailWord_229102, baseEnd_229102] using wordTrace_append hprefix tailTrace_229102
  have hstable : (prefixWord ++ tailWord_229102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229102).length < 2 ^ (prefixWord ++ tailWord_229102).sum := by decide
  have hdescent : baseEnd_229102 < baseStart_229102 := by decide
  rcases family_descends (prefixWord ++ tailWord_229102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229157 : List Nat := [1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_229157 : Nat := 118140960795 + 229157 * 2 ^ 59
def prefixEnd_229157 : Nat := 4983230072969 + 3 ^ 40 * 229157 * 2
def baseEnd_229157 : Nat := 69728999314053425708819

theorem tailTrace_229157 : CollatzResearch.WordTrace tailWord_229157 prefixEnd_229157 69728999314053425708819 := by
  unfold tailWord_229157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358042430810800744861725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5572028287207200496574483 8358042430810800744861725)
  ·
    refine ⟨3134265911554050279323147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8358042430810800744861725 3134265911554050279323147)
    ·
      refine ⟨4701398867331075418984721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134265911554050279323147 4701398867331075418984721)
      ·
        refine ⟨3526049150498306564238541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701398867331075418984721 3526049150498306564238541)
        ·
          refine ⟨1322268431436864961589453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3526049150498306564238541 1322268431436864961589453)
          ·
            refine ⟨495850661788824360596045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1322268431436864961589453 495850661788824360596045)
            ·
              refine ⟨185943998170809135223517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495850661788824360596045 185943998170809135223517)
              ·
                refine ⟨69728999314053425708819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185943998170809135223517 69728999314053425708819)
                ·
                  rfl

theorem cell19_229157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_229157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229157 prefixEnd_229157 := by exact prefixLift 229157
  have htrace : WordTrace (prefixWord ++ tailWord_229157) baseStart_229157 baseEnd_229157 := by
    simpa [prefixWord, tailWord_229157, baseEnd_229157] using wordTrace_append hprefix tailTrace_229157
  have hstable : (prefixWord ++ tailWord_229157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229157).length < 2 ^ (prefixWord ++ tailWord_229157).sum := by decide
  have hdescent : baseEnd_229157 < baseStart_229157 := by decide
  rcases family_descends (prefixWord ++ tailWord_229157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229178 : List Nat := [3, 1, 1, 1, 5, 2, 6]
def baseStart_229178 : Nat := 118140960795 + 229178 * 2 ^ 59
def prefixEnd_229178 : Nat := 4983230072969 + 3 ^ 40 * 229178 * 2
def baseEnd_229178 : Nat := 23245129765177199747365

theorem tailTrace_229178 : CollatzResearch.WordTrace tailWord_229178 prefixEnd_229178 23245129765177199747365 := by
  unfold tailWord_229178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089702090933680332844047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5572538909156480887584125 2089702090933680332844047)
  ·
    refine ⟨3134553136400520499266071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089702090933680332844047 3134553136400520499266071)
    ·
      refine ⟨4701829704600780748899107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134553136400520499266071 4701829704600780748899107)
      ·
        refine ⟨7052744556901171123348661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701829704600780748899107 7052744556901171123348661)
        ·
          refine ⟨661194802209484792813937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7052744556901171123348661 661194802209484792813937)
          ·
            refine ⟨495896101657113594610453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661194802209484792813937 495896101657113594610453)
            ·
              refine ⟨23245129765177199747365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 495896101657113594610453 23245129765177199747365)
              ·
                rfl

theorem cell19_229178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_229178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229178 prefixEnd_229178 := by exact prefixLift 229178
  have htrace : WordTrace (prefixWord ++ tailWord_229178) baseStart_229178 baseEnd_229178 := by
    simpa [prefixWord, tailWord_229178, baseEnd_229178] using wordTrace_append hprefix tailTrace_229178
  have hstable : (prefixWord ++ tailWord_229178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229178).length < 2 ^ (prefixWord ++ tailWord_229178).sum := by decide
  have hdescent : baseEnd_229178 < baseStart_229178 := by decide
  rcases family_descends (prefixWord ++ tailWord_229178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229216 : List Nat := [2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_229216 : Nat := 118140960795 + 229216 * 2 ^ 59
def prefixEnd_229216 : Nat := 4983230072969 + 3 ^ 40 * 229216 * 2
def baseEnd_229216 : Nat := 69746952119158770397547

theorem tailTrace_229216 : CollatzResearch.WordTrace tailWord_229216 prefixEnd_229216 69746952119158770397547 := by
  unfold tailWord_229216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180097168798526910629751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5573462891731369214173001 4180097168798526910629751)
  ·
    refine ⟨6270145753197790365944627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180097168798526910629751 6270145753197790365944627)
    ·
      refine ⟨9405218629796685548916941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270145753197790365944627 9405218629796685548916941)
      ·
        refine ⟨3526956986173757080843853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9405218629796685548916941 3526956986173757080843853)
        ·
          refine ⟨1322608869815158905316445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3526956986173757080843853 1322608869815158905316445)
          ·
            refine ⟨495978326180684589493667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1322608869815158905316445 495978326180684589493667)
            ·
              refine ⟨743967489271026884240501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495978326180684589493667 743967489271026884240501)
              ·
                refine ⟨69746952119158770397547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 743967489271026884240501 69746952119158770397547)
                ·
                  rfl

theorem cell19_229216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_229216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229216 prefixEnd_229216 := by exact prefixLift 229216
  have htrace : WordTrace (prefixWord ++ tailWord_229216) baseStart_229216 baseEnd_229216 := by
    simpa [prefixWord, tailWord_229216, baseEnd_229216] using wordTrace_append hprefix tailTrace_229216
  have hstable : (prefixWord ++ tailWord_229216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229216).length < 2 ^ (prefixWord ++ tailWord_229216).sum := by decide
  have hdescent : baseEnd_229216 < baseStart_229216 := by decide
  rcases family_descends (prefixWord ++ tailWord_229216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229288 : List Nat := [2, 1, 6, 2, 2, 6]
def baseStart_229288 : Nat := 118140960795 + 229288 * 2 ^ 59
def prefixEnd_229288 : Nat := 4983230072969 + 3 ^ 40 * 229288 * 2
def baseEnd_229288 : Nat := 7752095625231548533039

theorem tailTrace_229288 : CollatzResearch.WordTrace tailWord_229288 prefixEnd_229288 7752095625231548533039 := by
  unfold tailWord_229288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181410196668105058940259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5575213595557473411920345 4181410196668105058940259)
  ·
    refine ⟨6272115295002157588410389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181410196668105058940259 6272115295002157588410389)
    ·
      refine ⟨294005404453226136956737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6272115295002157588410389 294005404453226136956737)
      ·
        refine ⟨220504053339919602717553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294005404453226136956737 220504053339919602717553)
        ·
          refine ⟨165378040004939702038165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220504053339919602717553 165378040004939702038165)
          ·
            refine ⟨7752095625231548533039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165378040004939702038165 7752095625231548533039)
            ·
              rfl

theorem cell19_229288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_229288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229288 prefixEnd_229288 := by exact prefixLift 229288
  have htrace : WordTrace (prefixWord ++ tailWord_229288) baseStart_229288 baseEnd_229288 := by
    simpa [prefixWord, tailWord_229288, baseEnd_229288] using wordTrace_append hprefix tailTrace_229288
  have hstable : (prefixWord ++ tailWord_229288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229288).length < 2 ^ (prefixWord ++ tailWord_229288).sum := by decide
  have hdescent : baseEnd_229288 < baseStart_229288 := by decide
  rcases family_descends (prefixWord ++ tailWord_229288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229309 : List Nat := [1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_229309 : Nat := 118140960795 + 229309 * 2 ^ 59
def prefixEnd_229309 : Nat := 4983230072969 + 3 ^ 40 * 229309 * 2
def baseEnd_229309 : Nat := 69775250608562110330627

theorem tailTrace_229309 : CollatzResearch.WordTrace tailWord_229309 prefixEnd_229309 69775250608562110330627 := by
  unfold tailWord_229309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363586326260130704394981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5575724217506753802929987 8363586326260130704394981)
  ·
    refine ⟨1568172436173774507074059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8363586326260130704394981 1568172436173774507074059)
    ·
      refine ⟨2352258654260661760611089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568172436173774507074059 2352258654260661760611089)
      ·
        refine ⟨1764193990695496320458317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352258654260661760611089 1764193990695496320458317)
        ·
          refine ⟨661572746510811120171869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1764193990695496320458317 661572746510811120171869)
          ·
            refine ⟨248089779941554170064451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661572746510811120171869 248089779941554170064451)
            ·
              refine ⟨372134669912331255096677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248089779941554170064451 372134669912331255096677)
              ·
                refine ⟨69775250608562110330627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372134669912331255096677 69775250608562110330627)
                ·
                  rfl

theorem cell19_229309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_229309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229309 prefixEnd_229309 := by exact prefixLift 229309
  have htrace : WordTrace (prefixWord ++ tailWord_229309) baseStart_229309 baseEnd_229309 := by
    simpa [prefixWord, tailWord_229309, baseEnd_229309] using wordTrace_append hprefix tailTrace_229309
  have hstable : (prefixWord ++ tailWord_229309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229309).length < 2 ^ (prefixWord ++ tailWord_229309).sum := by decide
  have hdescent : baseEnd_229309 < baseStart_229309 := by decide
  rcases family_descends (prefixWord ++ tailWord_229309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229425 : List Nat := [1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_229425 : Nat := 118140960795 + 229425 * 2 ^ 59
def prefixEnd_229425 : Nat := 4983230072969 + 3 ^ 40 * 229425 * 2
def baseEnd_229425 : Nat := 69810547649108211752533

theorem tailTrace_229425 : CollatzResearch.WordTrace tailWord_229425 prefixEnd_229425 69810547649108211752533 := by
  unfold tailWord_229425
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367817193839882515617729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5578544795893255010411819 8367817193839882515617729)
  ·
    refine ⟨6275862895379911886713297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8367817193839882515617729 6275862895379911886713297)
    ·
      refine ⟨4706897171534933915034973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6275862895379911886713297 4706897171534933915034973)
      ·
        refine ⟨1765086439325600218138115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4706897171534933915034973 1765086439325600218138115)
        ·
          refine ⟨2647629658988400327207173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765086439325600218138115 2647629658988400327207173)
          ·
            refine ⟨496430561060325061351345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2647629658988400327207173 496430561060325061351345)
            ·
              refine ⟨372322920795243796013509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496430561060325061351345 372322920795243796013509)
              ·
                refine ⟨69810547649108211752533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372322920795243796013509 69810547649108211752533)
                ·
                  rfl

theorem cell19_229425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_229425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229425 prefixEnd_229425 := by exact prefixLift 229425
  have htrace : WordTrace (prefixWord ++ tailWord_229425) baseStart_229425 baseEnd_229425 := by
    simpa [prefixWord, tailWord_229425, baseEnd_229425] using wordTrace_append hprefix tailTrace_229425
  have hstable : (prefixWord ++ tailWord_229425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229425).length < 2 ^ (prefixWord ++ tailWord_229425).sum := by decide
  have hdescent : baseEnd_229425 < baseStart_229425 := by decide
  rcases family_descends (prefixWord ++ tailWord_229425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229427 : List Nat := [1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_229427 : Nat := 118140960795 + 229427 * 2 ^ 59
def prefixEnd_229427 : Nat := 4983230072969 + 3 ^ 40 * 229427 * 2
def baseEnd_229427 : Nat := 69811156218772799708083

theorem tailTrace_229427 : CollatzResearch.WordTrace tailWord_229427 prefixEnd_229427 69811156218772799708083 := by
  unfold tailWord_229427
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367890139832636857190535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5578593426555091238127023 8367890139832636857190535)
  ·
    refine ⟨12551835209748955285785803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8367890139832636857190535 12551835209748955285785803)
    ·
      refine ⟨18827752814623432928678705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12551835209748955285785803 18827752814623432928678705)
      ·
        refine ⟨14120814610967574696509029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18827752814623432928678705 14120814610967574696509029)
        ·
          refine ⟨2647652739556420255595443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14120814610967574696509029 2647652739556420255595443)
          ·
            refine ⟨3971479109334630383393165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647652739556420255595443 3971479109334630383393165)
            ·
              refine ⟨1489304666000486393772437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3971479109334630383393165 1489304666000486393772437)
              ·
                refine ⟨69811156218772799708083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1489304666000486393772437 69811156218772799708083)
                ·
                  rfl

theorem cell19_229427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_229427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229427 prefixEnd_229427 := by exact prefixLift 229427
  have htrace : WordTrace (prefixWord ++ tailWord_229427) baseStart_229427 baseEnd_229427 := by
    simpa [prefixWord, tailWord_229427, baseEnd_229427] using wordTrace_append hprefix tailTrace_229427
  have hstable : (prefixWord ++ tailWord_229427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229427).length < 2 ^ (prefixWord ++ tailWord_229427).sum := by decide
  have hdescent : baseEnd_229427 < baseStart_229427 := by decide
  rcases family_descends (prefixWord ++ tailWord_229427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229541 : List Nat := [1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_229541 : Nat := 118140960795 + 229541 * 2 ^ 59
def prefixEnd_229541 : Nat := 4983230072969 + 3 ^ 40 * 229541 * 2
def baseEnd_229541 : Nat := 69845844689654313174439

theorem tailTrace_229541 : CollatzResearch.WordTrace tailWord_229541 prefixEnd_229541 69845844689654313174439 := by
  unfold tailWord_229541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372048061419634326840477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5581365374279756217893651 8372048061419634326840477)
  ·
    refine ⟨3139518023032362872565179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8372048061419634326840477 3139518023032362872565179)
    ·
      refine ⟨4709277034548544308847769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139518023032362872565179 4709277034548544308847769)
      ·
        refine ⟨3531957775911408231635827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709277034548544308847769 3531957775911408231635827)
        ·
          refine ⟨5297936663867112347453741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531957775911408231635827 5297936663867112347453741)
          ·
            refine ⟨1986726248950167130295153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5297936663867112347453741 1986726248950167130295153)
            ·
              refine ⟨1490044686712625347721365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986726248950167130295153 1490044686712625347721365)
              ·
                refine ⟨69845844689654313174439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1490044686712625347721365 69845844689654313174439)
                ·
                  rfl

theorem cell19_229541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_229541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229541 prefixEnd_229541 := by exact prefixLift 229541
  have htrace : WordTrace (prefixWord ++ tailWord_229541) baseStart_229541 baseEnd_229541 := by
    simpa [prefixWord, tailWord_229541, baseEnd_229541] using wordTrace_append hprefix tailTrace_229541
  have hstable : (prefixWord ++ tailWord_229541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229541).length < 2 ^ (prefixWord ++ tailWord_229541).sum := by decide
  have hdescent : baseEnd_229541 < baseStart_229541 := by decide
  rcases family_descends (prefixWord ++ tailWord_229541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229550 : List Nat := [4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_229550 : Nat := 118140960795 + 229550 * 2 ^ 59
def prefixEnd_229550 : Nat := 4983230072969 + 3 ^ 40 * 229550 * 2
def baseEnd_229550 : Nat := 69848583253144958974415

theorem tailTrace_229550 : CollatzResearch.WordTrace tailWord_229550 prefixEnd_229550 69848583253144958974415 := by
  unfold tailWord_229550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046547039798378607989763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5581584212258019242612069 1046547039798378607989763)
  ·
    refine ⟨1569820559697567911984645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046547039798378607989763 1569820559697567911984645)
    ·
      refine ⟨294341354943293983497121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1569820559697567911984645 294341354943293983497121)
      ·
        refine ⟨220756016207470487622841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294341354943293983497121 220756016207470487622841)
        ·
          refine ⟨165567012155602865717131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220756016207470487622841 165567012155602865717131)
          ·
            refine ⟨248350518233404298575697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165567012155602865717131 248350518233404298575697)
            ·
              refine ⟨186262888675053223931773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248350518233404298575697 186262888675053223931773)
              ·
                refine ⟨69848583253144958974415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186262888675053223931773 69848583253144958974415)
                ·
                  rfl

theorem cell19_229550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_229550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229550 prefixEnd_229550 := by exact prefixLift 229550
  have htrace : WordTrace (prefixWord ++ tailWord_229550) baseStart_229550 baseEnd_229550 := by
    simpa [prefixWord, tailWord_229550, baseEnd_229550] using wordTrace_append hprefix tailTrace_229550
  have hstable : (prefixWord ++ tailWord_229550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229550).length < 2 ^ (prefixWord ++ tailWord_229550).sum := by decide
  have hdescent : baseEnd_229550 < baseStart_229550 := by decide
  rcases family_descends (prefixWord ++ tailWord_229550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229560 : List Nat := [2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_229560 : Nat := 118140960795 + 229560 * 2 ^ 59
def prefixEnd_229560 : Nat := 4983230072969 + 3 ^ 40 * 229560 * 2
def baseEnd_229560 : Nat := 69851626101467898752165

theorem tailTrace_229560 : CollatzResearch.WordTrace tailWord_229560 prefixEnd_229560 69851626101467898752165 := by
  unfold tailWord_229560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186370524175400285891067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5581827365567200381188089 4186370524175400285891067)
  ·
    refine ⟨6279555786263100428836601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4186370524175400285891067 6279555786263100428836601)
    ·
      refine ⟨4709666839697325321627451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6279555786263100428836601 4709666839697325321627451)
      ·
        refine ⟨7064500259545987982441177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709666839697325321627451 7064500259545987982441177)
        ·
          refine ⟨5298375194659490986830883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7064500259545987982441177 5298375194659490986830883)
          ·
            refine ⟨7947562791989236480246325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298375194659490986830883 7947562791989236480246325)
            ·
              refine ⟨745084011748990920023093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7947562791989236480246325 745084011748990920023093)
              ·
                refine ⟨69851626101467898752165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745084011748990920023093 69851626101467898752165)
                ·
                  rfl

theorem cell19_229560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_229560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229560 prefixEnd_229560 := by exact prefixLift 229560
  have htrace : WordTrace (prefixWord ++ tailWord_229560) baseStart_229560 baseEnd_229560 := by
    simpa [prefixWord, tailWord_229560, baseEnd_229560] using wordTrace_append hprefix tailTrace_229560
  have hstable : (prefixWord ++ tailWord_229560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229560).length < 2 ^ (prefixWord ++ tailWord_229560).sum := by decide
  have hdescent : baseEnd_229560 < baseStart_229560 := by decide
  rcases family_descends (prefixWord ++ tailWord_229560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229617 : List Nat := [1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_229617 : Nat := 118140960795 + 229617 * 2 ^ 59
def prefixEnd_229617 : Nat := 4983230072969 + 3 ^ 40 * 229617 * 2
def baseEnd_229617 : Nat := 69868970336908655485343

theorem tailTrace_229617 : CollatzResearch.WordTrace tailWord_229617 prefixEnd_229617 69868970336908655485343 := by
  unfold tailWord_229617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374820009144299306607105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5583213339429532871071403 8374820009144299306607105)
  ·
    refine ⟨6281115006858224479955329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8374820009144299306607105 6281115006858224479955329)
    ·
      refine ⟨4710836255143668359966497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6281115006858224479955329 4710836255143668359966497)
      ·
        refine ⟨3533127191357751269974873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4710836255143668359966497 3533127191357751269974873)
        ·
          refine ⟨2649845393518313452481155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533127191357751269974873 2649845393518313452481155)
          ·
            refine ⟨3974768090277470178721733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649845393518313452481155 3974768090277470178721733)
            ·
              refine ⟨745269016927025658510325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3974768090277470178721733 745269016927025658510325)
              ·
                refine ⟨69868970336908655485343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745269016927025658510325 69868970336908655485343)
                ·
                  rfl

theorem cell19_229617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_229617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229617 prefixEnd_229617 := by exact prefixLift 229617
  have htrace : WordTrace (prefixWord ++ tailWord_229617) baseStart_229617 baseEnd_229617 := by
    simpa [prefixWord, tailWord_229617, baseEnd_229617] using wordTrace_append hprefix tailTrace_229617
  have hstable : (prefixWord ++ tailWord_229617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229617).length < 2 ^ (prefixWord ++ tailWord_229617).sum := by decide
  have hdescent : baseEnd_229617 < baseStart_229617 := by decide
  rcases family_descends (prefixWord ++ tailWord_229617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229634 : List Nat := [3, 4, 1, 1, 2, 8]
def baseStart_229634 : Nat := 118140960795 + 229634 * 2 ^ 59
def prefixEnd_229634 : Nat := 4983230072969 + 3 ^ 40 * 229634 * 2
def baseEnd_229634 : Nat := 7763793686561961456391

theorem tailTrace_229634 : CollatzResearch.WordTrace tailWord_229634 prefixEnd_229634 7763793686561961456391 := by
  unfold tailWord_229634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093860012520677802493989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5583626700055140806650637 2093860012520677802493989)
  ·
    refine ⟨392598752347627087967623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2093860012520677802493989 392598752347627087967623)
    ·
      refine ⟨588898128521440631951435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392598752347627087967623 588898128521440631951435)
      ·
        refine ⟨883347192782160947927153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588898128521440631951435 883347192782160947927153)
        ·
          refine ⟨662510394586620710945365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883347192782160947927153 662510394586620710945365)
          ·
            refine ⟨7763793686561961456391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 662510394586620710945365 7763793686561961456391)
            ·
              rfl

theorem cell19_229634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_229634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229634 prefixEnd_229634 := by exact prefixLift 229634
  have htrace : WordTrace (prefixWord ++ tailWord_229634) baseStart_229634 baseEnd_229634 := by
    simpa [prefixWord, tailWord_229634, baseEnd_229634] using wordTrace_append hprefix tailTrace_229634
  have hstable : (prefixWord ++ tailWord_229634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229634).length < 2 ^ (prefixWord ++ tailWord_229634).sum := by decide
  have hdescent : baseEnd_229634 < baseStart_229634 := by decide
  rcases family_descends (prefixWord ++ tailWord_229634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229636 : List Nat := [2, 3, 2, 2, 10]
def baseStart_229636 : Nat := 118140960795 + 229636 * 2 ^ 59
def prefixEnd_229636 : Nat := 4983230072969 + 3 ^ 40 * 229636 * 2
def baseEnd_229636 : Nat := 2587953768471194113447

theorem tailTrace_229636 : CollatzResearch.WordTrace tailWord_229636 prefixEnd_229636 2587953768471194113447 := by
  unfold tailWord_229636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187756498037732775774381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5583675330716977034365841 4187756498037732775774381)
  ·
    refine ⟨1570408686764149790915393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4187756498037732775774381 1570408686764149790915393)
    ·
      refine ⟨1177806515073112343186545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570408686764149790915393 1177806515073112343186545)
      ·
        refine ⟨883354886304834257389909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177806515073112343186545 883354886304834257389909)
        ·
          refine ⟨2587953768471194113447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 883354886304834257389909 2587953768471194113447)
          ·
            rfl

theorem cell19_229636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_229636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229636 prefixEnd_229636 := by exact prefixLift 229636
  have htrace : WordTrace (prefixWord ++ tailWord_229636) baseStart_229636 baseEnd_229636 := by
    simpa [prefixWord, tailWord_229636, baseEnd_229636] using wordTrace_append hprefix tailTrace_229636
  have hstable : (prefixWord ++ tailWord_229636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229636).length < 2 ^ (prefixWord ++ tailWord_229636).sum := by decide
  have hdescent : baseEnd_229636 < baseStart_229636 := by decide
  rcases family_descends (prefixWord ++ tailWord_229636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229731 : List Nat := [1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_229731 : Nat := 118140960795 + 229731 * 2 ^ 59
def prefixEnd_229731 : Nat := 4983230072969 + 3 ^ 40 * 229731 * 2
def baseEnd_229731 : Nat := 69903658807790168951699

theorem tailTrace_229731 : CollatzResearch.WordTrace tailWord_229731 prefixEnd_229731 69903658807790168951699 := by
  unfold tailWord_229731
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378977930731296776257047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5585985287154197850838031 8378977930731296776257047)
  ·
    refine ⟨12568466896096945164385571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8378977930731296776257047 12568466896096945164385571)
    ·
      refine ⟨18852700344145417746578357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12568466896096945164385571 18852700344145417746578357)
      ·
        refine ⟨1767440657263632913741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18852700344145417746578357 1767440657263632913741721)
        ·
          refine ⟨1325580492947724685306291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767440657263632913741721 1325580492947724685306291)
          ·
            refine ⟨1988370739421587027959437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325580492947724685306291 1988370739421587027959437)
            ·
              refine ⟨745639027283095135484789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1988370739421587027959437 745639027283095135484789)
              ·
                refine ⟨69903658807790168951699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 745639027283095135484789 69903658807790168951699)
                ·
                  rfl

theorem cell19_229731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_229731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229731 prefixEnd_229731 := by exact prefixLift 229731
  have htrace : WordTrace (prefixWord ++ tailWord_229731) baseStart_229731 baseEnd_229731 := by
    simpa [prefixWord, tailWord_229731, baseEnd_229731] using wordTrace_append hprefix tailTrace_229731
  have hstable : (prefixWord ++ tailWord_229731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229731).length < 2 ^ (prefixWord ++ tailWord_229731).sum := by decide
  have hdescent : baseEnd_229731 < baseStart_229731 := by decide
  rcases family_descends (prefixWord ++ tailWord_229731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229769 : List Nat := [1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_229769 : Nat := 118140960795 + 229769 * 2 ^ 59
def prefixEnd_229769 : Nat := 4983230072969 + 3 ^ 40 * 229769 * 2
def baseEnd_229769 : Nat := 69915221631417340107151

theorem tailTrace_229769 : CollatzResearch.WordTrace tailWord_229769 prefixEnd_229769 69915221631417340107151 := by
  unfold tailWord_229769
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380363904593629266140361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5586909269729086177426907 8380363904593629266140361)
  ·
    refine ⟨6285272928445221949605271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8380363904593629266140361 6285272928445221949605271)
    ·
      refine ⟨9427909392667832924407907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285272928445221949605271 9427909392667832924407907)
      ·
        refine ⟨14141864089001749386611861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427909392667832924407907 14141864089001749386611861)
        ·
          refine ⟨662899879171957002497431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14141864089001749386611861 662899879171957002497431)
          ·
            refine ⟨994349818757935503746147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662899879171957002497431 994349818757935503746147)
            ·
              refine ⟨1491524728136903255619221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994349818757935503746147 1491524728136903255619221)
              ·
                refine ⟨69915221631417340107151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1491524728136903255619221 69915221631417340107151)
                ·
                  rfl

theorem cell19_229769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_229769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229769 prefixEnd_229769 := by exact prefixLift 229769
  have htrace : WordTrace (prefixWord ++ tailWord_229769) baseStart_229769 baseEnd_229769 := by
    simpa [prefixWord, tailWord_229769, baseEnd_229769] using wordTrace_append hprefix tailTrace_229769
  have hstable : (prefixWord ++ tailWord_229769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229769).length < 2 ^ (prefixWord ++ tailWord_229769).sum := by decide
  have hdescent : baseEnd_229769 < baseStart_229769 := by decide
  rcases family_descends (prefixWord ++ tailWord_229769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229805 : List Nat := [1, 5, 2, 2, 2, 7]
def baseStart_229805 : Nat := 118140960795 + 229805 * 2 ^ 59
def prefixEnd_229805 : Nat := 4983230072969 + 3 ^ 40 * 229805 * 2
def baseEnd_229805 : Nat := 7769575098375547034117

theorem tailTrace_229805 : CollatzResearch.WordTrace tailWord_229805 prefixEnd_229805 7769575098375547034117 := by
  unfold tailWord_229805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381676932463207414450869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5587784621642138276300579 8381676932463207414450869)
  ·
    refine ⟨785782212418425695104769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8381676932463207414450869 785782212418425695104769)
    ·
      refine ⟨589336659313819271328577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 785782212418425695104769 589336659313819271328577)
      ·
        refine ⟨442002494485364453496433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589336659313819271328577 442002494485364453496433)
        ·
          refine ⟨331501870864023340122325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442002494485364453496433 331501870864023340122325)
          ·
            refine ⟨7769575098375547034117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 331501870864023340122325 7769575098375547034117)
            ·
              rfl

theorem cell19_229805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_229805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229805 prefixEnd_229805 := by exact prefixLift 229805
  have htrace : WordTrace (prefixWord ++ tailWord_229805) baseStart_229805 baseEnd_229805 := by
    simpa [prefixWord, tailWord_229805, baseEnd_229805] using wordTrace_append hprefix tailTrace_229805
  have hstable : (prefixWord ++ tailWord_229805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229805).length < 2 ^ (prefixWord ++ tailWord_229805).sum := by decide
  have hdescent : baseEnd_229805 < baseStart_229805 := by decide
  rcases family_descends (prefixWord ++ tailWord_229805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229864 : List Nat := [2, 1, 4, 1, 1, 4, 6]
def baseStart_229864 : Nat := 118140960795 + 229864 * 2 ^ 59
def prefixEnd_229864 : Nat := 4983230072969 + 3 ^ 40 * 229864 * 2
def baseEnd_229864 : Nat := 23314709563495089331927

theorem tailTrace_229864 : CollatzResearch.WordTrace tailWord_229864 prefixEnd_229864 23314709563495089331927 := by
  unfold tailWord_229864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191914419624730245424323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5589219226166306993899097 4191914419624730245424323)
  ·
    refine ⟨6287871629437095368136485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4191914419624730245424323 6287871629437095368136485)
    ·
      refine ⟨1178975930519455381525591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6287871629437095368136485 1178975930519455381525591)
      ·
        refine ⟨1768463895779183072288387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178975930519455381525591 1768463895779183072288387)
        ·
          refine ⟨2652695843668774608432581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768463895779183072288387 2652695843668774608432581)
          ·
            refine ⟨497380470687895239081109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2652695843668774608432581 497380470687895239081109)
            ·
              refine ⟨23314709563495089331927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 497380470687895239081109 23314709563495089331927)
              ·
                rfl

theorem cell19_229864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_229864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229864 prefixEnd_229864 := by exact prefixLift 229864
  have htrace : WordTrace (prefixWord ++ tailWord_229864) baseStart_229864 baseEnd_229864 := by
    simpa [prefixWord, tailWord_229864, baseEnd_229864] using wordTrace_append hprefix tailTrace_229864
  have hstable : (prefixWord ++ tailWord_229864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229864).length < 2 ^ (prefixWord ++ tailWord_229864).sum := by decide
  have hdescent : baseEnd_229864 < baseStart_229864 := by decide
  rcases family_descends (prefixWord ++ tailWord_229864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229894 : List Nat := [6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_229894 : Nat := 118140960795 + 229894 * 2 ^ 59
def prefixEnd_229894 : Nat := 4983230072969 + 3 ^ 40 * 229894 * 2
def baseEnd_229894 : Nat := 69953257235454087329033

theorem tailTrace_229894 : CollatzResearch.WordTrace tailWord_229894 prefixEnd_229894 69953257235454087329033 := by
  unfold tailWord_229894
  simp only [CollatzResearch.WordTrace]
  refine ⟨262028844660649237951273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5589948686093850409627157 262028844660649237951273)
  ·
    refine ⟨196521633495486928463455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262028844660649237951273 196521633495486928463455)
    ·
      refine ⟨294782450243230392695183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196521633495486928463455 294782450243230392695183)
      ·
        refine ⟨442173675364845589042775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294782450243230392695183 442173675364845589042775)
        ·
          refine ⟨663260513047268383564163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442173675364845589042775 663260513047268383564163)
          ·
            refine ⟨994890769570902575346245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663260513047268383564163 994890769570902575346245)
            ·
              refine ⟨186542019294544232877421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 994890769570902575346245 186542019294544232877421)
              ·
                refine ⟨69953257235454087329033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186542019294544232877421 69953257235454087329033)
                ·
                  rfl

theorem cell19_229894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_229894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229894 prefixEnd_229894 := by exact prefixLift 229894
  have htrace : WordTrace (prefixWord ++ tailWord_229894) baseStart_229894 baseEnd_229894 := by
    simpa [prefixWord, tailWord_229894, baseEnd_229894] using wordTrace_append hprefix tailTrace_229894
  have hstable : (prefixWord ++ tailWord_229894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229894).length < 2 ^ (prefixWord ++ tailWord_229894).sum := by decide
  have hdescent : baseEnd_229894 < baseStart_229894 := by decide
  rcases family_descends (prefixWord ++ tailWord_229894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229900 : List Nat := [2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_229900 : Nat := 118140960795 + 229900 * 2 ^ 59
def prefixEnd_229900 : Nat := 4983230072969 + 3 ^ 40 * 229900 * 2
def baseEnd_229900 : Nat := 69955082944447851195683

theorem tailTrace_229900 : CollatzResearch.WordTrace tailWord_229900 prefixEnd_229900 69955082944447851195683 := by
  unfold tailWord_229900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192570933559519319579577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5590094578079359092772769 4192570933559519319579577)
  ·
    refine ⟨3144428200169639489684683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4192570933559519319579577 3144428200169639489684683)
    ·
      refine ⟨4716642300254459234527025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144428200169639489684683 4716642300254459234527025)
      ·
        refine ⟨3537481725190844425895269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716642300254459234527025 3537481725190844425895269)
        ·
          refine ⟨663277823473283329855363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3537481725190844425895269 663277823473283329855363)
          ·
            refine ⟨994916735209924994783045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663277823473283329855363 994916735209924994783045)
            ·
              refine ⟨186546887851860936521821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 994916735209924994783045 186546887851860936521821)
              ·
                refine ⟨69955082944447851195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186546887851860936521821 69955082944447851195683)
                ·
                  rfl

theorem cell19_229900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_229900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229900 prefixEnd_229900 := by exact prefixLift 229900
  have htrace : WordTrace (prefixWord ++ tailWord_229900) baseStart_229900 baseEnd_229900 := by
    simpa [prefixWord, tailWord_229900, baseEnd_229900] using wordTrace_append hprefix tailTrace_229900
  have hstable : (prefixWord ++ tailWord_229900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229900).length < 2 ^ (prefixWord ++ tailWord_229900).sum := by decide
  have hdescent : baseEnd_229900 < baseStart_229900 := by decide
  rcases family_descends (prefixWord ++ tailWord_229900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229959 : List Nat := [1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_229959 : Nat := 118140960795 + 229959 * 2 ^ 59
def prefixEnd_229959 : Nat := 4983230072969 + 3 ^ 40 * 229959 * 2
def baseEnd_229959 : Nat := 69973035749553195884411

theorem tailTrace_229959 : CollatzResearch.WordTrace tailWord_229959 prefixEnd_229959 69973035749553195884411 := by
  unfold tailWord_229959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387293773905291715556931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5591529182603527810371287 8387293773905291715556931)
  ·
    refine ⟨12580940660857937573335397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387293773905291715556931 12580940660857937573335397)
    ·
      refine ⟨2358926373910863295000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12580940660857937573335397 2358926373910863295000387)
      ·
        refine ⟨3538389560866294942500581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358926373910863295000387 3538389560866294942500581)
        ·
          refine ⟨663448042662430301718859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3538389560866294942500581 663448042662430301718859)
          ·
            refine ⟨995172063993645452578289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663448042662430301718859 995172063993645452578289)
            ·
              refine ⟨746379047995234089433717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995172063993645452578289 746379047995234089433717)
              ·
                refine ⟨69973035749553195884411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746379047995234089433717 69973035749553195884411)
                ·
                  rfl

theorem cell19_229959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_229959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_229959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_229959 prefixEnd_229959 := by exact prefixLift 229959
  have htrace : WordTrace (prefixWord ++ tailWord_229959) baseStart_229959 baseEnd_229959 := by
    simpa [prefixWord, tailWord_229959, baseEnd_229959] using wordTrace_append hprefix tailTrace_229959
  have hstable : (prefixWord ++ tailWord_229959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229959).length < 2 ^ (prefixWord ++ tailWord_229959).sum := by decide
  have hdescent : baseEnd_229959 < baseStart_229959 := by decide
  rcases family_descends (prefixWord ++ tailWord_229959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230069 : List Nat := [1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_230069 : Nat := 118140960795 + 230069 * 2 ^ 59
def prefixEnd_230069 : Nat := 4983230072969 + 3 ^ 40 * 230069 * 2
def baseEnd_230069 : Nat := 70006507081105533439667

theorem tailTrace_230069 : CollatzResearch.WordTrace tailWord_230069 prefixEnd_230069 70006507081105533439667 := by
  unfold tailWord_230069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391305803506780502061261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5594203869004520334707507 8391305803506780502061261)
  ·
    refine ⟨3146739676315042688272973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8391305803506780502061261 3146739676315042688272973)
    ·
      refine ⟨1180027378618141008102365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3146739676315042688272973 1180027378618141008102365)
      ·
        refine ⟨442510266981802878038387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1180027378618141008102365 442510266981802878038387)
        ·
          refine ⟨663765400472704317057581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442510266981802878038387 663765400472704317057581)
          ·
            refine ⟨248912025177264118896593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663765400472704317057581 248912025177264118896593)
            ·
              refine ⟨186684018882948089172445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248912025177264118896593 186684018882948089172445)
              ·
                refine ⟨70006507081105533439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186684018882948089172445 70006507081105533439667)
                ·
                  rfl

theorem cell19_230069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_230069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230069 prefixEnd_230069 := by exact prefixLift 230069
  have htrace : WordTrace (prefixWord ++ tailWord_230069) baseStart_230069 baseEnd_230069 := by
    simpa [prefixWord, tailWord_230069, baseEnd_230069] using wordTrace_append hprefix tailTrace_230069
  have hstable : (prefixWord ++ tailWord_230069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230069).length < 2 ^ (prefixWord ++ tailWord_230069).sum := by decide
  have hdescent : baseEnd_230069 < baseStart_230069 := by decide
  rcases family_descends (prefixWord ++ tailWord_230069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230086 : List Nat := [6, 1, 2, 1, 2, 2, 5]
def baseStart_230086 : Nat := 118140960795 + 230086 * 2 ^ 59
def prefixEnd_230086 : Nat := 4983230072969 + 3 ^ 40 * 230086 * 2
def baseEnd_230086 : Nat := 23337226641084843687281

theorem tailTrace_230086 : CollatzResearch.WordTrace tailWord_230086 prefixEnd_230086 23337226641084843687281 := by
  unfold tailWord_230086
  simp only [CollatzResearch.WordTrace]
  refine ⟨262247682638912262669691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5594617229630128270286741 262247682638912262669691)
  ·
    refine ⟨393371523958368394004537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262247682638912262669691 393371523958368394004537)
    ·
      refine ⟨295028642968776295503403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393371523958368394004537 295028642968776295503403)
      ·
        refine ⟨442542964453164443255105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295028642968776295503403 442542964453164443255105)
        ·
          refine ⟨331907223339873332441329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442542964453164443255105 331907223339873332441329)
          ·
            refine ⟨248930417504904999330997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331907223339873332441329 248930417504904999330997)
            ·
              refine ⟨23337226641084843687281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248930417504904999330997 23337226641084843687281)
              ·
                rfl

theorem cell19_230086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_230086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230086 prefixEnd_230086 := by exact prefixLift 230086
  have htrace : WordTrace (prefixWord ++ tailWord_230086) baseStart_230086 baseEnd_230086 := by
    simpa [prefixWord, tailWord_230086, baseEnd_230086] using wordTrace_append hprefix tailTrace_230086
  have hstable : (prefixWord ++ tailWord_230086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230086).length < 2 ^ (prefixWord ++ tailWord_230086).sum := by decide
  have hdescent : baseEnd_230086 < baseStart_230086 := by decide
  rcases family_descends (prefixWord ++ tailWord_230086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230092 : List Nat := [2, 2, 1, 5, 1, 1, 7]
def baseStart_230092 : Nat := 118140960795 + 230092 * 2 ^ 59
def prefixEnd_230092 : Nat := 4983230072969 + 3 ^ 40 * 230092 * 2
def baseEnd_230092 : Nat := 23337835210749431642831

theorem tailTrace_230092 : CollatzResearch.WordTrace tailWord_230092 prefixEnd_230092 23337835210749431642831 := by
  unfold tailWord_230092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196072341211727715074265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5594763121615636953432353 4196072341211727715074265)
  ·
    refine ⟨3147054255908795786305699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4196072341211727715074265 3147054255908795786305699)
    ·
      refine ⟨4720581383863193679458549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147054255908795786305699 4720581383863193679458549)
      ·
        refine ⟨442554504737174407449239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4720581383863193679458549 442554504737174407449239)
        ·
          refine ⟨663831757105761611173859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442554504737174407449239 663831757105761611173859)
          ·
            refine ⟨995747635658642416760789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663831757105761611173859 995747635658642416760789)
            ·
              refine ⟨23337835210749431642831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 995747635658642416760789 23337835210749431642831)
              ·
                rfl

theorem cell19_230092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_230092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230092 prefixEnd_230092 := by exact prefixLift 230092
  have htrace : WordTrace (prefixWord ++ tailWord_230092) baseStart_230092 baseEnd_230092 := by
    simpa [prefixWord, tailWord_230092, baseEnd_230092] using wordTrace_append hprefix tailTrace_230092
  have hstable : (prefixWord ++ tailWord_230092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230092).length < 2 ^ (prefixWord ++ tailWord_230092).sum := by decide
  have hdescent : baseEnd_230092 < baseStart_230092 := by decide
  rcases family_descends (prefixWord ++ tailWord_230092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230111 : List Nat := [1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_230111 : Nat := 118140960795 + 230111 * 2 ^ 59
def prefixEnd_230111 : Nat := 4983230072969 + 3 ^ 40 * 230111 * 2
def baseEnd_230111 : Nat := 70019287044061880506219

theorem tailTrace_230111 : CollatzResearch.WordTrace tailWord_230111 prefixEnd_230111 70019287044061880506219 := by
  unfold tailWord_230111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392837669354621675090187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595225112903081116726791 8392837669354621675090187)
  ·
    refine ⟨12589256504031932512635281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392837669354621675090187 12589256504031932512635281)
    ·
      refine ⟨9441942378023949384476461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12589256504031932512635281 9441942378023949384476461)
      ·
        refine ⟨3540728391758981019178673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9441942378023949384476461 3540728391758981019178673)
        ·
          refine ⟨2655546293819235764384005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540728391758981019178673 2655546293819235764384005)
          ·
            refine ⟨497914930091106705822001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2655546293819235764384005 497914930091106705822001)
            ·
              refine ⟨373436197568330029366501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497914930091106705822001 373436197568330029366501)
              ·
                refine ⟨70019287044061880506219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373436197568330029366501 70019287044061880506219)
                ·
                  rfl

theorem cell19_230111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_230111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230111 prefixEnd_230111 := by exact prefixLift 230111
  have htrace : WordTrace (prefixWord ++ tailWord_230111) baseStart_230111 baseEnd_230111 := by
    simpa [prefixWord, tailWord_230111, baseEnd_230111] using wordTrace_append hprefix tailTrace_230111
  have hstable : (prefixWord ++ tailWord_230111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230111).length < 2 ^ (prefixWord ++ tailWord_230111).sum := by decide
  have hdescent : baseEnd_230111 < baseStart_230111 := by decide
  rcases family_descends (prefixWord ++ tailWord_230111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230130 : List Nat := [3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_230130 : Nat := 118140960795 + 230130 * 2 ^ 59
def prefixEnd_230130 : Nat := 4983230072969 + 3 ^ 40 * 230130 * 2
def baseEnd_230130 : Nat := 70025068455875466083945

theorem tailTrace_230130 : CollatzResearch.WordTrace tailWord_230130 prefixEnd_230130 70025068455875466083945 := by
  unfold tailWord_230130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098382664071446980007961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5595687104190525280021229 2098382664071446980007961)
  ·
    refine ⟨1573786998053585235005971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098382664071446980007961 1573786998053585235005971)
    ·
      refine ⟨2360680497080377852508957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573786998053585235005971 2360680497080377852508957)
      ·
        refine ⟨885255186405141694690859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2360680497080377852508957 885255186405141694690859)
        ·
          refine ⟨1327882779607712542036289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885255186405141694690859 1327882779607712542036289)
          ·
            refine ⟨995912084705784406527217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327882779607712542036289 995912084705784406527217)
            ·
              refine ⟨746934063529338304895413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995912084705784406527217 746934063529338304895413)
              ·
                refine ⟨70025068455875466083945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746934063529338304895413 70025068455875466083945)
                ·
                  rfl

theorem cell19_230130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_230130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230130 prefixEnd_230130 := by exact prefixLift 230130
  have htrace : WordTrace (prefixWord ++ tailWord_230130) baseStart_230130 baseEnd_230130 := by
    simpa [prefixWord, tailWord_230130, baseEnd_230130] using wordTrace_append hprefix tailTrace_230130
  have hstable : (prefixWord ++ tailWord_230130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230130).length < 2 ^ (prefixWord ++ tailWord_230130).sum := by decide
  have hdescent : baseEnd_230130 < baseStart_230130 := by decide
  rcases family_descends (prefixWord ++ tailWord_230130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230162 : List Nat := [3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_230162 : Nat := 118140960795 + 230162 * 2 ^ 59
def prefixEnd_230162 : Nat := 4983230072969 + 3 ^ 40 * 230162 * 2
def baseEnd_230162 : Nat := 70034805570508873372747

theorem tailTrace_230162 : CollatzResearch.WordTrace tailWord_230162 prefixEnd_230162 70034805570508873372747 := by
  unfold tailWord_230162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098674448042464346299185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5596465194779904923464493 2098674448042464346299185)
  ·
    refine ⟨1574005836031848259724389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098674448042464346299185 1574005836031848259724389)
    ·
      refine ⟨295126094255971548698323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1574005836031848259724389 295126094255971548698323)
      ·
        refine ⟨442689141383957323047485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295126094255971548698323 442689141383957323047485)
        ·
          refine ⟨166008428018983996142807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442689141383957323047485 166008428018983996142807)
          ·
            refine ⟨249012642028475994214211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166008428018983996142807 249012642028475994214211)
            ·
              refine ⟨373518963042713991321317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249012642028475994214211 373518963042713991321317)
              ·
                refine ⟨70034805570508873372747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373518963042713991321317 70034805570508873372747)
                ·
                  rfl

theorem cell19_230162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_230162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230162 prefixEnd_230162 := by exact prefixLift 230162
  have htrace : WordTrace (prefixWord ++ tailWord_230162) baseStart_230162 baseEnd_230162 := by
    simpa [prefixWord, tailWord_230162, baseEnd_230162] using wordTrace_append hprefix tailTrace_230162
  have hstable : (prefixWord ++ tailWord_230162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230162).length < 2 ^ (prefixWord ++ tailWord_230162).sum := by decide
  have hdescent : baseEnd_230162 < baseStart_230162 := by decide
  rcases family_descends (prefixWord ++ tailWord_230162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230242 : List Nat := [3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_230242 : Nat := 118140960795 + 230242 * 2 ^ 59
def prefixEnd_230242 : Nat := 4983230072969 + 3 ^ 40 * 230242 * 2
def baseEnd_230242 : Nat := 70059148357092391594751

theorem tailTrace_230242 : CollatzResearch.WordTrace tailWord_230242 prefixEnd_230242 70059148357092391594751 := by
  unfold tailWord_230242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099403907970007762027245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5598410421253354032072653 2099403907970007762027245)
  ·
    refine ⟨787276465488752910760217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2099403907970007762027245 787276465488752910760217)
    ·
      refine ⟨590457349116564683070163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787276465488752910760217 590457349116564683070163)
      ·
        refine ⟨885686023674847024605245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590457349116564683070163 885686023674847024605245)
        ·
          refine ⟨332132258878067634226967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885686023674847024605245 332132258878067634226967)
          ·
            refine ⟨498198388317101451340451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332132258878067634226967 498198388317101451340451)
            ·
              refine ⟨747297582475652177010677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498198388317101451340451 747297582475652177010677)
              ·
                refine ⟨70059148357092391594751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747297582475652177010677 70059148357092391594751)
                ·
                  rfl

theorem cell19_230242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_230242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230242 prefixEnd_230242 := by exact prefixLift 230242
  have htrace : WordTrace (prefixWord ++ tailWord_230242) baseStart_230242 baseEnd_230242 := by
    simpa [prefixWord, tailWord_230242, baseEnd_230242] using wordTrace_append hprefix tailTrace_230242
  have hstable : (prefixWord ++ tailWord_230242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230242).length < 2 ^ (prefixWord ++ tailWord_230242).sum := by decide
  have hdescent : baseEnd_230242 < baseStart_230242 := by decide
  rcases family_descends (prefixWord ++ tailWord_230242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230244 : List Nat := [2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_230244 : Nat := 118140960795 + 230244 * 2 ^ 59
def prefixEnd_230244 : Nat := 4983230072969 + 3 ^ 40 * 230244 * 2
def baseEnd_230244 : Nat := 70059756926756979550301

theorem tailTrace_230244 : CollatzResearch.WordTrace tailWord_230244 prefixEnd_230244 70059756926756979550301 := by
  unfold tailWord_230244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198844288936392694840893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5598459051915190259787857 4198844288936392694840893)
  ·
    refine ⟨1574566608351147260565335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4198844288936392694840893 1574566608351147260565335)
    ·
      refine ⟨2361849912526720890848003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574566608351147260565335 2361849912526720890848003)
      ·
        refine ⟨3542774868790081336272005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361849912526720890848003 3542774868790081336272005)
        ·
          refine ⟨664270287898140250551001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3542774868790081336272005 664270287898140250551001)
          ·
            refine ⟨498202715923605187913251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664270287898140250551001 498202715923605187913251)
            ·
              refine ⟨747304073885407781869877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498202715923605187913251 747304073885407781869877)
              ·
                refine ⟨70059756926756979550301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747304073885407781869877 70059756926756979550301)
                ·
                  rfl

theorem cell19_230244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_230244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230244 prefixEnd_230244 := by exact prefixLift 230244
  have htrace : WordTrace (prefixWord ++ tailWord_230244) baseStart_230244 baseEnd_230244 := by
    simpa [prefixWord, tailWord_230244, baseEnd_230244] using wordTrace_append hprefix tailTrace_230244
  have hstable : (prefixWord ++ tailWord_230244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230244).length < 2 ^ (prefixWord ++ tailWord_230244).sum := by decide
  have hdescent : baseEnd_230244 < baseStart_230244 := by decide
  rcases family_descends (prefixWord ++ tailWord_230244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230265 : List Nat := [1, 2, 1, 3, 2, 3, 7]
def baseStart_230265 : Nat := 118140960795 + 230265 * 2 ^ 59
def prefixEnd_230265 : Nat := 4983230072969 + 3 ^ 40 * 230265 * 2
def baseEnd_230265 : Nat := 23355382302745051027859

theorem tailTrace_230265 : CollatzResearch.WordTrace tailWord_230265 prefixEnd_230265 23355382302745051027859 := by
  unfold tailWord_230265
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398454510796705976196249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598969673864470650797499 8398454510796705976196249)
  ·
    refine ⟨6298840883097529482147187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8398454510796705976196249 6298840883097529482147187)
    ·
      refine ⟨9448261324646294223220781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298840883097529482147187 9448261324646294223220781)
      ·
        refine ⟨3543097996742360333707793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9448261324646294223220781 3543097996742360333707793)
        ·
          refine ⟨2657323497556770250280845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543097996742360333707793 2657323497556770250280845)
          ·
            refine ⟨996496311583788843855317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657323497556770250280845 996496311583788843855317)
            ·
              refine ⟨23355382302745051027859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 996496311583788843855317 23355382302745051027859)
              ·
                rfl

theorem cell19_230265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_230265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230265 prefixEnd_230265 := by exact prefixLift 230265
  have htrace : WordTrace (prefixWord ++ tailWord_230265) baseStart_230265 baseEnd_230265 := by
    simpa [prefixWord, tailWord_230265, baseEnd_230265] using wordTrace_append hprefix tailTrace_230265
  have hstable : (prefixWord ++ tailWord_230265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230265).length < 2 ^ (prefixWord ++ tailWord_230265).sum := by decide
  have hdescent : baseEnd_230265 < baseStart_230265 := by decide
  rcases family_descends (prefixWord ++ tailWord_230265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230282 : List Nat := [3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_230282 : Nat := 118140960795 + 230282 * 2 ^ 59
def prefixEnd_230282 : Nat := 4983230072969 + 3 ^ 40 * 230282 * 2
def baseEnd_230282 : Nat := 70071319750384150705753

theorem tailTrace_230282 : CollatzResearch.WordTrace tailWord_230282 prefixEnd_230282 70071319750384150705753 := by
  unfold tailWord_230282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099768637933779469891275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5599383034490078586376733 2099768637933779469891275)
  ·
    refine ⟨3149652956900669204836913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2099768637933779469891275 3149652956900669204836913)
    ·
      refine ⟨2362239717675501903627685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149652956900669204836913 2362239717675501903627685)
      ·
        refine ⟨442919947064156606930191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2362239717675501903627685 442919947064156606930191)
        ·
          refine ⟨664379920596234910395287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442919947064156606930191 664379920596234910395287)
          ·
            refine ⟨996569880894352365592931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664379920596234910395287 996569880894352365592931)
            ·
              refine ⟨1494854821341528548389397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996569880894352365592931 1494854821341528548389397)
              ·
                refine ⟨70071319750384150705753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1494854821341528548389397 70071319750384150705753)
                ·
                  rfl

theorem cell19_230282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_230282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230282 prefixEnd_230282 := by exact prefixLift 230282
  have htrace : WordTrace (prefixWord ++ tailWord_230282) baseStart_230282 baseEnd_230282 := by
    simpa [prefixWord, tailWord_230282, baseEnd_230282] using wordTrace_append hprefix tailTrace_230282
  have hstable : (prefixWord ++ tailWord_230282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230282).length < 2 ^ (prefixWord ++ tailWord_230282).sum := by decide
  have hdescent : baseEnd_230282 < baseStart_230282 := by decide
  rcases family_descends (prefixWord ++ tailWord_230282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230284 : List Nat := [2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_230284 : Nat := 118140960795 + 230284 * 2 ^ 59
def prefixEnd_230284 : Nat := 4983230072969 + 3 ^ 40 * 230284 * 2
def baseEnd_230284 : Nat := 70071928320048738661303

theorem tailTrace_230284 : CollatzResearch.WordTrace tailWord_230284 prefixEnd_230284 70071928320048738661303 := by
  unfold tailWord_230284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199573748863936110568953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5599431665151914814091937 4199573748863936110568953)
  ·
    refine ⟨3149680311647952082926715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4199573748863936110568953 3149680311647952082926715)
    ·
      refine ⟨4724520467471928124390073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149680311647952082926715 4724520467471928124390073)
      ·
        refine ⟨3543390350603946093292555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724520467471928124390073 3543390350603946093292555)
        ·
          refine ⟨5315085525905919139938833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543390350603946093292555 5315085525905919139938833)
          ·
            refine ⟨3986314144429439354954125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5315085525905919139938833 3986314144429439354954125)
            ·
              refine ⟨1494867804161039758107797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986314144429439354954125 1494867804161039758107797)
              ·
                refine ⟨70071928320048738661303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1494867804161039758107797 70071928320048738661303)
                ·
                  rfl

theorem cell19_230284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_230284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230284 prefixEnd_230284 := by exact prefixLift 230284
  have htrace : WordTrace (prefixWord ++ tailWord_230284) baseStart_230284 baseEnd_230284 := by
    simpa [prefixWord, tailWord_230284, baseEnd_230284] using wordTrace_append hprefix tailTrace_230284
  have hstable : (prefixWord ++ tailWord_230284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230284).length < 2 ^ (prefixWord ++ tailWord_230284).sum := by decide
  have hdescent : baseEnd_230284 < baseStart_230284 := by decide
  rcases family_descends (prefixWord ++ tailWord_230284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230356 : List Nat := [2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_230356 : Nat := 118140960795 + 230356 * 2 ^ 59
def prefixEnd_230356 : Nat := 4983230072969 + 3 ^ 40 * 230356 * 2
def baseEnd_230356 : Nat := 70093836827973905061107

theorem tailTrace_230356 : CollatzResearch.WordTrace tailWord_230356 prefixEnd_230356 70093836827973905061107 := by
  unfold tailWord_230356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200886776733514258879461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5601182368978019011839281 4200886776733514258879461)
  ·
    refine ⟨787666270637533923539899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4200886776733514258879461 787666270637533923539899)
    ·
      refine ⟨1181499405956300885309849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787666270637533923539899 1181499405956300885309849)
      ·
        refine ⟨886124554467225663982387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181499405956300885309849 886124554467225663982387)
        ·
          refine ⟨1329186831700838495973581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886124554467225663982387 1329186831700838495973581)
          ·
            refine ⟨498445061887814435990093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1329186831700838495973581 498445061887814435990093)
            ·
              refine ⟨186916898207930413496285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498445061887814435990093 186916898207930413496285)
              ·
                refine ⟨70093836827973905061107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186916898207930413496285 70093836827973905061107)
                ·
                  rfl

theorem cell19_230356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_230356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230356 prefixEnd_230356 := by exact prefixLift 230356
  have htrace : WordTrace (prefixWord ++ tailWord_230356) baseStart_230356 baseEnd_230356 := by
    simpa [prefixWord, tailWord_230356, baseEnd_230356] using wordTrace_append hprefix tailTrace_230356
  have hstable : (prefixWord ++ tailWord_230356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230356).length < 2 ^ (prefixWord ++ tailWord_230356).sum := by decide
  have hdescent : baseEnd_230356 < baseStart_230356 := by decide
  rcases family_descends (prefixWord ++ tailWord_230356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230432 : List Nat := [2, 1, 1, 7, 1, 2, 5]
def baseStart_230432 : Nat := 118140960795 + 230432 * 2 ^ 59
def prefixEnd_230432 : Nat := 4983230072969 + 3 ^ 40 * 230432 * 2
def baseEnd_230432 : Nat := 23372320825076082457337

theorem tailTrace_230432 : CollatzResearch.WordTrace tailWord_230432 prefixEnd_230432 23372320825076082457337 := by
  unfold tailWord_230432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202272750595846748762775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5603030334127795665017033 4202272750595846748762775)
  ·
    refine ⟨6303409125893770123144163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202272750595846748762775 6303409125893770123144163)
    ·
      refine ⟨9455113688840655184716245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303409125893770123144163 9455113688840655184716245)
      ·
        refine ⟨221604227082202855891787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9455113688840655184716245 221604227082202855891787)
        ·
          refine ⟨332406340623304283837681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221604227082202855891787 332406340623304283837681)
          ·
            refine ⟨249304755467478212878261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332406340623304283837681 249304755467478212878261)
            ·
              refine ⟨23372320825076082457337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249304755467478212878261 23372320825076082457337)
              ·
                rfl

theorem cell19_230432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_230432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230432 prefixEnd_230432 := by exact prefixLift 230432
  have htrace : WordTrace (prefixWord ++ tailWord_230432) baseStart_230432 baseEnd_230432 := by
    simpa [prefixWord, tailWord_230432, baseEnd_230432] using wordTrace_append hprefix tailTrace_230432
  have hstable : (prefixWord ++ tailWord_230432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230432).length < 2 ^ (prefixWord ++ tailWord_230432).sum := by decide
  have hdescent : baseEnd_230432 < baseStart_230432 := by decide
  rcases family_descends (prefixWord ++ tailWord_230432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230434 : List Nat := [3, 3, 1, 1, 1, 5, 5]
def baseStart_230434 : Nat := 118140960795 + 230434 * 2 ^ 59
def prefixEnd_230434 : Nat := 4983230072969 + 3 ^ 40 * 230434 * 2
def baseEnd_230434 : Nat := 23372523681630945109187

theorem tailTrace_230434 : CollatzResearch.WordTrace tailWord_230434 prefixEnd_230434 23372523681630945109187 := by
  unfold tailWord_230434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101154611796111959774589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5603078964789631892732237 2101154611796111959774589)
  ·
    refine ⟨787932979423541984915471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2101154611796111959774589 787932979423541984915471)
    ·
      refine ⟨1181899469135312977373207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787932979423541984915471 1181899469135312977373207)
      ·
        refine ⟨1772849203702969466059811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181899469135312977373207 1772849203702969466059811)
        ·
          refine ⟨2659273805554454199089717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772849203702969466059811 2659273805554454199089717)
          ·
            refine ⟨249306919270730081164661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2659273805554454199089717 249306919270730081164661)
            ·
              refine ⟨23372523681630945109187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249306919270730081164661 23372523681630945109187)
              ·
                rfl

theorem cell19_230434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_230434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230434 prefixEnd_230434 := by exact prefixLift 230434
  have htrace : WordTrace (prefixWord ++ tailWord_230434) baseStart_230434 baseEnd_230434 := by
    simpa [prefixWord, tailWord_230434, baseEnd_230434] using wordTrace_append hprefix tailTrace_230434
  have hstable : (prefixWord ++ tailWord_230434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230434).length < 2 ^ (prefixWord ++ tailWord_230434).sum := by decide
  have hdescent : baseEnd_230434 < baseStart_230434 := by decide
  rcases family_descends (prefixWord ++ tailWord_230434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230470 : List Nat := [6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_230470 : Nat := 118140960795 + 230470 * 2 ^ 59
def prefixEnd_230470 : Nat := 4983230072969 + 3 ^ 40 * 230470 * 2
def baseEnd_230470 : Nat := 70128525298855418527463

theorem tailTrace_230470 : CollatzResearch.WordTrace tailWord_230470 prefixEnd_230470 70128525298855418527463 := by
  unfold tailWord_230470
  simp only [CollatzResearch.WordTrace]
  refine ⟨262685358595438312106527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5603954316702683991605909 262685358595438312106527)
  ·
    refine ⟨394028037893157468159791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262685358595438312106527 394028037893157468159791)
    ·
      refine ⟨591042056839736202239687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394028037893157468159791 591042056839736202239687)
      ·
        refine ⟨886563085259604303359531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591042056839736202239687 886563085259604303359531)
        ·
          refine ⟨1329844627889406455039297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886563085259604303359531 1329844627889406455039297)
          ·
            refine ⟨997383470917054841279473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329844627889406455039297 997383470917054841279473)
            ·
              refine ⟨748037603187791130959605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997383470917054841279473 748037603187791130959605)
              ·
                refine ⟨70128525298855418527463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748037603187791130959605 70128525298855418527463)
                ·
                  rfl

theorem cell19_230470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_230470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230470 prefixEnd_230470 := by exact prefixLift 230470
  have htrace : WordTrace (prefixWord ++ tailWord_230470) baseStart_230470 baseEnd_230470 := by
    simpa [prefixWord, tailWord_230470, baseEnd_230470] using wordTrace_append hprefix tailTrace_230470
  have hstable : (prefixWord ++ tailWord_230470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230470).length < 2 ^ (prefixWord ++ tailWord_230470).sum := by decide
  have hdescent : baseEnd_230470 < baseStart_230470 := by decide
  rcases family_descends (prefixWord ++ tailWord_230470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230474 : List Nat := [3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_230474 : Nat := 118140960795 + 230474 * 2 ^ 59
def prefixEnd_230474 : Nat := 4983230072969 + 3 ^ 40 * 230474 * 2
def baseEnd_230474 : Nat := 70129742438184594438563

theorem tailTrace_230474 : CollatzResearch.WordTrace tailWord_230474 prefixEnd_230474 70129742438184594438563 := by
  unfold tailWord_230474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101519341759883667638619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5604051578026356447036317 2101519341759883667638619)
  ·
    refine ⟨3152279012639825501457929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101519341759883667638619 3152279012639825501457929)
    ·
      refine ⟨2364209259479869126093447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3152279012639825501457929 2364209259479869126093447)
      ·
        refine ⟨3546313889219803689140171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364209259479869126093447 3546313889219803689140171)
        ·
          refine ⟨5319470833829705533710257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546313889219803689140171 5319470833829705533710257)
          ·
            refine ⟨3989603125372279150282693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5319470833829705533710257 3989603125372279150282693)
            ·
              refine ⟨748050586007302340678005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3989603125372279150282693 748050586007302340678005)
              ·
                refine ⟨70129742438184594438563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748050586007302340678005 70129742438184594438563)
                ·
                  rfl

theorem cell19_230474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_230474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230474 prefixEnd_230474 := by exact prefixLift 230474
  have htrace : WordTrace (prefixWord ++ tailWord_230474) baseStart_230474 baseEnd_230474 := by
    simpa [prefixWord, tailWord_230474, baseEnd_230474] using wordTrace_append hprefix tailTrace_230474
  have hstable : (prefixWord ++ tailWord_230474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230474).length < 2 ^ (prefixWord ++ tailWord_230474).sum := by decide
  have hdescent : baseEnd_230474 < baseStart_230474 := by decide
  rcases family_descends (prefixWord ++ tailWord_230474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230510 : List Nat := [4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_230510 : Nat := 118140960795 + 230510 * 2 ^ 59
def prefixEnd_230510 : Nat := 4983230072969 + 3 ^ 40 * 230510 * 2
def baseEnd_230510 : Nat := 70140696692147177638465

theorem tailTrace_230510 : CollatzResearch.WordTrace tailWord_230510 prefixEnd_230510 70140696692147177638465 := by
  unfold tailWord_230510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050923799363639102358123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5604926929939408545909989 1050923799363639102358123)
  ·
    refine ⟨1576385699045458653537185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050923799363639102358123 1576385699045458653537185)
    ·
      refine ⟨1182289274284093990152889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576385699045458653537185 1182289274284093990152889)
      ·
        refine ⟨886716955713070492614667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182289274284093990152889 886716955713070492614667)
        ·
          refine ⟨1330075433569605738922001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886716955713070492614667 1330075433569605738922001)
          ·
            refine ⟨997556575177204304191501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330075433569605738922001 997556575177204304191501)
            ·
              refine ⟨374083715691451614071813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997556575177204304191501 374083715691451614071813)
              ·
                refine ⟨70140696692147177638465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374083715691451614071813 70140696692147177638465)
                ·
                  rfl

theorem cell19_230510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_230510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230510 prefixEnd_230510 := by exact prefixLift 230510
  have htrace : WordTrace (prefixWord ++ tailWord_230510) baseStart_230510 baseEnd_230510 := by
    simpa [prefixWord, tailWord_230510, baseEnd_230510] using wordTrace_append hprefix tailTrace_230510
  have hstable : (prefixWord ++ tailWord_230510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230510).length < 2 ^ (prefixWord ++ tailWord_230510).sum := by decide
  have hdescent : baseEnd_230510 < baseStart_230510 := by decide
  rcases family_descends (prefixWord ++ tailWord_230510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230582 : List Nat := [5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_230582 : Nat := 118140960795 + 230582 * 2 ^ 59
def prefixEnd_230582 : Nat := 4983230072969 + 3 ^ 40 * 230582 * 2
def baseEnd_230582 : Nat := 70162605200072344038269

theorem tailTrace_230582 : CollatzResearch.WordTrace tailWord_230582 prefixEnd_230582 70162605200072344038269 := by
  unfold tailWord_230582
  simp only [CollatzResearch.WordTrace]
  refine ⟨525626028165516819717875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5606677633765512743657333 525626028165516819717875)
  ·
    refine ⟨788439042248275229576813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525626028165516819717875 788439042248275229576813)
    ·
      refine ⟨295664640843103211091305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 788439042248275229576813 295664640843103211091305)
      ·
        refine ⟨221748480632327408318479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295664640843103211091305 221748480632327408318479)
        ·
          refine ⟨332622720948491112477719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221748480632327408318479 332622720948491112477719)
          ·
            refine ⟨498934081422736668716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332622720948491112477719 498934081422736668716579)
            ·
              refine ⟨748401122134105003074869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498934081422736668716579 748401122134105003074869)
              ·
                refine ⟨70162605200072344038269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748401122134105003074869 70162605200072344038269)
                ·
                  rfl

theorem cell19_230582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_230582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230582 prefixEnd_230582 := by exact prefixLift 230582
  have htrace : WordTrace (prefixWord ++ tailWord_230582) baseStart_230582 baseEnd_230582 := by
    simpa [prefixWord, tailWord_230582, baseEnd_230582] using wordTrace_append hprefix tailTrace_230582
  have hstable : (prefixWord ++ tailWord_230582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230582).length < 2 ^ (prefixWord ++ tailWord_230582).sum := by decide
  have hdescent : baseEnd_230582 < baseStart_230582 := by decide
  rcases family_descends (prefixWord ++ tailWord_230582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230662 : List Nat := [6, 2, 11]
def baseStart_230662 : Nat := 118140960795 + 230662 * 2 ^ 59
def prefixEnd_230662 : Nat := 4983230072969 + 3 ^ 40 * 230662 * 2
def baseEnd_230662 : Nat := 288835176899818363211

theorem tailTrace_230662 : CollatzResearch.WordTrace tailWord_230662 prefixEnd_230662 288835176899818363211 := by
  unfold tailWord_230662
  simp only [CollatzResearch.WordTrace]
  refine ⟨262904196573701336824945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5608622860238961852265493 262904196573701336824945)
  ·
    refine ⟨197178147430276002618709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262904196573701336824945 197178147430276002618709)
    ·
      refine ⟨288835176899818363211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 197178147430276002618709 288835176899818363211)
      ·
        rfl

theorem cell19_230662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 11].length) (baseStart_230662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230662 prefixEnd_230662 := by exact prefixLift 230662
  have htrace : WordTrace (prefixWord ++ tailWord_230662) baseStart_230662 baseEnd_230662 := by
    simpa [prefixWord, tailWord_230662, baseEnd_230662] using wordTrace_append hprefix tailTrace_230662
  have hstable : (prefixWord ++ tailWord_230662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230662).length < 2 ^ (prefixWord ++ tailWord_230662).sum := by decide
  have hdescent : baseEnd_230662 < baseStart_230662 := by decide
  rcases family_descends (prefixWord ++ tailWord_230662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230664 : List Nat := [2, 1, 3, 2, 4, 7]
def baseStart_230664 : Nat := 118140960795 + 230664 * 2 ^ 59
def prefixEnd_230664 : Nat := 4983230072969 + 3 ^ 40 * 230664 * 2
def baseEnd_230664 : Nat := 7798617395146716690647

theorem tailTrace_230664 : CollatzResearch.WordTrace tailWord_230664 prefixEnd_230664 7798617395146716690647 := by
  unfold tailWord_230664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206503618175598559985523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5608671490900798079980697 4206503618175598559985523)
  ·
    refine ⟨6309755427263397839978285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206503618175598559985523 6309755427263397839978285)
    ·
      refine ⟨2366158285223774189991857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6309755427263397839978285 2366158285223774189991857)
      ·
        refine ⟨1774618713917830642493893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366158285223774189991857 1774618713917830642493893)
        ·
          refine ⟨332741008859593245467605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1774618713917830642493893 332741008859593245467605)
          ·
            refine ⟨7798617395146716690647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 332741008859593245467605 7798617395146716690647)
            ·
              rfl

theorem cell19_230664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_230664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230664 prefixEnd_230664 := by exact prefixLift 230664
  have htrace : WordTrace (prefixWord ++ tailWord_230664) baseStart_230664 baseEnd_230664 := by
    simpa [prefixWord, tailWord_230664, baseEnd_230664] using wordTrace_append hprefix tailTrace_230664
  have hstable : (prefixWord ++ tailWord_230664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230664).length < 2 ^ (prefixWord ++ tailWord_230664).sum := by decide
  have hdescent : baseEnd_230664 < baseStart_230664 := by decide
  rcases family_descends (prefixWord ++ tailWord_230664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230698 : List Nat := [3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_230698 : Nat := 118140960795 + 230698 * 2 ^ 59
def prefixEnd_230698 : Nat := 4983230072969 + 3 ^ 40 * 230698 * 2
def baseEnd_230698 : Nat := 70197902240618445460175

theorem tailTrace_230698 : CollatzResearch.WordTrace tailWord_230698 prefixEnd_230698 70197902240618445460175 := by
  unfold tailWord_230698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2103561829557005231677187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5609498212152013951139165 2103561829557005231677187)
  ·
    refine ⟨3155342744335507847515781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2103561829557005231677187 3155342744335507847515781)
    ·
      refine ⟨591626764562907721409209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3155342744335507847515781 591626764562907721409209)
      ·
        refine ⟨443720073422180791056907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591626764562907721409209 443720073422180791056907)
        ·
          refine ⟨665580110133271186585361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443720073422180791056907 665580110133271186585361)
          ·
            refine ⟨499185082599953389939021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665580110133271186585361 499185082599953389939021)
            ·
              refine ⟨187194405974982521227133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499185082599953389939021 187194405974982521227133)
              ·
                refine ⟨70197902240618445460175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187194405974982521227133 70197902240618445460175)
                ·
                  rfl

theorem cell19_230698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_230698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230698 prefixEnd_230698 := by exact prefixLift 230698
  have htrace : WordTrace (prefixWord ++ tailWord_230698) baseStart_230698 baseEnd_230698 := by
    simpa [prefixWord, tailWord_230698, baseEnd_230698] using wordTrace_append hprefix tailTrace_230698
  have hstable : (prefixWord ++ tailWord_230698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230698).length < 2 ^ (prefixWord ++ tailWord_230698).sum := by decide
  have hdescent : baseEnd_230698 < baseStart_230698 := by decide
  rcases family_descends (prefixWord ++ tailWord_230698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230740 : List Nat := [2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_230740 : Nat := 118140960795 + 230740 * 2 ^ 59
def prefixEnd_230740 : Nat := 4983230072969 + 3 ^ 40 * 230740 * 2
def baseEnd_230740 : Nat := 70210682203574792526727

theorem tailTrace_230740 : CollatzResearch.WordTrace tailWord_230740 prefixEnd_230740 70210682203574792526727 := by
  unfold tailWord_230740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207889592037931049868837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5610519456050574733158449 4207889592037931049868837)
  ·
    refine ⟨788979298507112071850407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4207889592037931049868837 788979298507112071850407)
    ·
      refine ⟨1183468947760668107775611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788979298507112071850407 1183468947760668107775611)
      ·
        refine ⟨1775203421641002161663417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183468947760668107775611 1775203421641002161663417)
        ·
          refine ⟨1331402566230751621247563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775203421641002161663417 1331402566230751621247563)
          ·
            refine ⟨1997103849346127431871345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331402566230751621247563 1997103849346127431871345)
            ·
              refine ⟨1497827887009595573903509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997103849346127431871345 1497827887009595573903509)
              ·
                refine ⟨70210682203574792526727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1497827887009595573903509 70210682203574792526727)
                ·
                  rfl

theorem cell19_230740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_230740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230740 prefixEnd_230740 := by exact prefixLift 230740
  have htrace : WordTrace (prefixWord ++ tailWord_230740) baseStart_230740 baseEnd_230740 := by
    simpa [prefixWord, tailWord_230740, baseEnd_230740] using wordTrace_append hprefix tailTrace_230740
  have hstable : (prefixWord ++ tailWord_230740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230740).length < 2 ^ (prefixWord ++ tailWord_230740).sum := by decide
  have hdescent : baseEnd_230740 < baseStart_230740 := by decide
  rcases family_descends (prefixWord ++ tailWord_230740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230749 : List Nat := [1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_230749 : Nat := 118140960795 + 230749 * 2 ^ 59
def prefixEnd_230749 : Nat := 4983230072969 + 3 ^ 40 * 230749 * 2
def baseEnd_230749 : Nat := 70213420767065438326703

theorem tailTrace_230749 : CollatzResearch.WordTrace tailWord_230749 prefixEnd_230749 70213420767065438326703 := by
  unfold tailWord_230749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416107441043256636815301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5610738294028837757876867 8416107441043256636815301)
  ·
    refine ⟨1578020145195610619402869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8416107441043256636815301 1578020145195610619402869)
    ·
      refine ⟨147939388612088495569019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1578020145195610619402869 147939388612088495569019)
      ·
        refine ⟨221909082918132743353529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147939388612088495569019 221909082918132743353529)
        ·
          refine ⟨166431812188599557515147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221909082918132743353529 166431812188599557515147)
          ·
            refine ⟨249647718282899336272721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166431812188599557515147 249647718282899336272721)
            ·
              refine ⟨187235788712174502204541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249647718282899336272721 187235788712174502204541)
              ·
                refine ⟨70213420767065438326703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187235788712174502204541 70213420767065438326703)
                ·
                  rfl

theorem cell19_230749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_230749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230749 prefixEnd_230749 := by exact prefixLift 230749
  have htrace : WordTrace (prefixWord ++ tailWord_230749) baseStart_230749 baseEnd_230749 := by
    simpa [prefixWord, tailWord_230749, baseEnd_230749] using wordTrace_append hprefix tailTrace_230749
  have hstable : (prefixWord ++ tailWord_230749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230749).length < 2 ^ (prefixWord ++ tailWord_230749).sum := by decide
  have hdescent : baseEnd_230749 < baseStart_230749 := by decide
  rcases family_descends (prefixWord ++ tailWord_230749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230852 : List Nat := [2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_230852 : Nat := 118140960795 + 230852 * 2 ^ 59
def prefixEnd_230852 : Nat := 4983230072969 + 3 ^ 40 * 230852 * 2
def baseEnd_230852 : Nat := 70244762104791718037533

theorem tailTrace_230852 : CollatzResearch.WordTrace tailWord_230852 prefixEnd_230852 70244762104791718037533 := by
  unfold tailWord_230852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209932079835052613907405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5613242773113403485209873 4209932079835052613907405)
  ·
    refine ⟨1578724529938144730215277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4209932079835052613907405 1578724529938144730215277)
    ·
      refine ⟨592021698726804273830729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1578724529938144730215277 592021698726804273830729)
      ·
        refine ⟨444016274045103205373047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592021698726804273830729 444016274045103205373047)
        ·
          refine ⟨666024411067654808059571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444016274045103205373047 666024411067654808059571)
          ·
            refine ⟨999036616601482212089357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666024411067654808059571 999036616601482212089357)
            ·
              refine ⟨374638731225555829533509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 999036616601482212089357 374638731225555829533509)
              ·
                refine ⟨70244762104791718037533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374638731225555829533509 70244762104791718037533)
                ·
                  rfl

theorem cell19_230852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_230852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_230852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_230852 prefixEnd_230852 := by exact prefixLift 230852
  have htrace : WordTrace (prefixWord ++ tailWord_230852) baseStart_230852 baseEnd_230852 := by
    simpa [prefixWord, tailWord_230852, baseEnd_230852] using wordTrace_append hprefix tailTrace_230852
  have hstable : (prefixWord ++ tailWord_230852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230852).length < 2 ^ (prefixWord ++ tailWord_230852).sum := by decide
  have hdescent : baseEnd_230852 < baseStart_230852 := by decide
  rcases family_descends (prefixWord ++ tailWord_230852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
