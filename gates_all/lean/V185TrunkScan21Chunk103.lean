import V185TrunkScan21Chunk102

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1251306 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1251306 : Nat := 118140960795 + 1251306 * 2 ^ 59
def prefixEnd_1251306 : Nat := 4983230072969 + 3 ^ 40 * 1251306 * 2
def baseEnd_1251306 : Nat := 285565077268882885875713

theorem tailTrace_1251306 : CollatzResearch.WordTrace tailWord_1251306 prefixEnd_1251306 285565077268882885875713 := by
  unfold tailWord_1251306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11409719801184885723975443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30425919469826361930601181 11409719801184885723975443)
  ·
    refine ⟨17114579701777328585963165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11409719801184885723975443 17114579701777328585963165)
    ·
      refine ⟨6417967388166498219736187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17114579701777328585963165 6417967388166498219736187)
      ·
        refine ⟨9626951082249747329604281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417967388166498219736187 9626951082249747329604281)
        ·
          refine ⟨7220213311687310497203211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9626951082249747329604281 7220213311687310497203211)
          ·
            refine ⟨10830319967530965745804817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220213311687310497203211 10830319967530965745804817)
            ·
              refine ⟨8122739975648224309353613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10830319967530965745804817 8122739975648224309353613)
              ·
                refine ⟨3046027490868084116007605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8122739975648224309353613 3046027490868084116007605)
                ·
                  refine ⟨285565077268882885875713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3046027490868084116007605 285565077268882885875713)
                  ·
                    rfl

theorem cell21_1251306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1251306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251306 prefixEnd_1251306 := by exact prefixLift 1251306
  have htrace : WordTrace (prefixWord ++ tailWord_1251306) baseStart_1251306 baseEnd_1251306 := by
    simpa [prefixWord, tailWord_1251306, baseEnd_1251306] using wordTrace_append hprefix tailTrace_1251306
  have hstable : (prefixWord ++ tailWord_1251306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251306).length < 2 ^ (prefixWord ++ tailWord_1251306).sum := by decide
  have hdescent : baseEnd_1251306 < baseStart_1251306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251354 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1251354 : Nat := 118140960795 + 1251354 * 2 ^ 59
def prefixEnd_1251354 : Nat := 4983230072969 + 3 ^ 40 * 1251354 * 2
def baseEnd_1251354 : Nat := 285576031522845469075615

theorem tailTrace_1251354 : CollatzResearch.WordTrace tailWord_1251354 prefixEnd_1251354 285576031522845469075615 := by
  unfold tailWord_1251354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410157477141411773412279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30427086605710431395766077 11410157477141411773412279)
  ·
    refine ⟨17115236215712117660118419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11410157477141411773412279 17115236215712117660118419)
    ·
      refine ⟨25672854323568176490177629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17115236215712117660118419 25672854323568176490177629)
      ·
        refine ⟨9627320371338066183816611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25672854323568176490177629 9627320371338066183816611)
        ·
          refine ⟨14440980557007099275724917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9627320371338066183816611 14440980557007099275724917)
          ·
            refine ⟨1353841927219415557099211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14440980557007099275724917 1353841927219415557099211)
            ·
              refine ⟨2030762890829123335648817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353841927219415557099211 2030762890829123335648817)
              ·
                refine ⟨1523072168121842501736613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030762890829123335648817 1523072168121842501736613)
                ·
                  refine ⟨285576031522845469075615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523072168121842501736613 285576031522845469075615)
                  ·
                    rfl

theorem cell21_1251354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1251354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251354 prefixEnd_1251354 := by exact prefixLift 1251354
  have htrace : WordTrace (prefixWord ++ tailWord_1251354) baseStart_1251354 baseEnd_1251354 := by
    simpa [prefixWord, tailWord_1251354, baseEnd_1251354] using wordTrace_append hprefix tailTrace_1251354
  have hstable : (prefixWord ++ tailWord_1251354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251354).length < 2 ^ (prefixWord ++ tailWord_1251354).sum := by decide
  have hdescent : baseEnd_1251354 < baseStart_1251354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251385 : List Nat := [1, 2, 1, 5, 3, 2, 2, 5]
def baseStart_1251385 : Nat := 118140960795 + 1251385 * 2 ^ 59
def prefixEnd_1251385 : Nat := 4983230072969 + 3 ^ 40 * 1251385 * 2
def baseEnd_1251385 : Nat := 95194368715065434686295

theorem tailTrace_1251385 : CollatzResearch.WordTrace tailWord_1251385 prefixEnd_1251385 95194368715065434686295 := by
  unfold tailWord_1251385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45641760571453339388027609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30427840380968892925351739 45641760571453339388027609)
  ·
    refine ⟨34231320428590004541020707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45641760571453339388027609 34231320428590004541020707)
    ·
      refine ⟨51346980642885006811531061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34231320428590004541020707 51346980642885006811531061)
      ·
        refine ⟨4813779435270469388581037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51346980642885006811531061 4813779435270469388581037)
        ·
          refine ⟨1805167288226426020717889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4813779435270469388581037 1805167288226426020717889)
          ·
            refine ⟨1353875466169819515538417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805167288226426020717889 1353875466169819515538417)
            ·
              refine ⟨1015406599627364636653813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353875466169819515538417 1015406599627364636653813)
              ·
                refine ⟨95194368715065434686295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015406599627364636653813 95194368715065434686295)
                ·
                  rfl

theorem cell21_1251385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].length) (baseStart_1251385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251385 prefixEnd_1251385 := by exact prefixLift 1251385
  have htrace : WordTrace (prefixWord ++ tailWord_1251385) baseStart_1251385 baseEnd_1251385 := by
    simpa [prefixWord, tailWord_1251385, baseEnd_1251385] using wordTrace_append hprefix tailTrace_1251385
  have hstable : (prefixWord ++ tailWord_1251385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251385).length < 2 ^ (prefixWord ++ tailWord_1251385).sum := by decide
  have hdescent : baseEnd_1251385 < baseStart_1251385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251416 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_1251416 : Nat := 118140960795 + 1251416 * 2 ^ 59
def prefixEnd_1251416 : Nat := 4983230072969 + 3 ^ 40 * 1251416 * 2
def baseEnd_1251416 : Nat := 285590180767547139042155

theorem tailTrace_1251416 : CollatzResearch.WordTrace tailWord_1251416 prefixEnd_1251416 285590180767547139042155 := by
  unfold tailWord_1251416
  simp only [CollatzResearch.WordTrace]
  refine ⟨22821445617170515841203051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30428594156227354454937401 22821445617170515841203051)
  ·
    refine ⟨34232168425755773761804577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22821445617170515841203051 34232168425755773761804577)
    ·
      refine ⟨25674126319316830321353433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34232168425755773761804577 25674126319316830321353433)
      ·
        refine ⟨19255594739487622741015075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25674126319316830321353433 19255594739487622741015075)
        ·
          refine ⟨28883392109231434111522613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255594739487622741015075 28883392109231434111522613)
          ·
            refine ⟨2707818010240446947955245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28883392109231434111522613 2707818010240446947955245)
            ·
              refine ⟨1015431753840167605483217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707818010240446947955245 1015431753840167605483217)
              ·
                refine ⟨761573815380125704112413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015431753840167605483217 761573815380125704112413)
                ·
                  refine ⟨285590180767547139042155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761573815380125704112413 285590180767547139042155)
                  ·
                    rfl

theorem cell21_1251416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_1251416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251416 prefixEnd_1251416 := by exact prefixLift 1251416
  have htrace : WordTrace (prefixWord ++ tailWord_1251416) baseStart_1251416 baseEnd_1251416 := by
    simpa [prefixWord, tailWord_1251416, baseEnd_1251416] using wordTrace_append hprefix tailTrace_1251416
  have hstable : (prefixWord ++ tailWord_1251416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251416).length < 2 ^ (prefixWord ++ tailWord_1251416).sum := by decide
  have hdescent : baseEnd_1251416 < baseStart_1251416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251422 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1251422 : Nat := 118140960795 + 1251422 * 2 ^ 59
def prefixEnd_1251422 : Nat := 4983230072969 + 3 ^ 40 * 1251422 * 2
def baseEnd_1251422 : Nat := 285591550049292461942143

theorem tailTrace_1251422 : CollatzResearch.WordTrace tailWord_1251422 prefixEnd_1251422 285591550049292461942143 := by
  unfold tailWord_1251422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705388759039911838390565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30428740048212863138083013 5705388759039911838390565)
  ·
    refine ⟨1069760392319983469698231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5705388759039911838390565 1069760392319983469698231)
    ·
      refine ⟨1604640588479975204547347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069760392319983469698231 1604640588479975204547347)
      ·
        refine ⟨2406960882719962806821021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604640588479975204547347 2406960882719962806821021)
        ·
          refine ⟨902610331019986052557883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2406960882719962806821021 902610331019986052557883)
          ·
            refine ⟨1353915496529979078836825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902610331019986052557883 1353915496529979078836825)
            ·
              refine ⟨1015436622397484309127619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353915496529979078836825 1015436622397484309127619)
              ·
                refine ⟨1523154933596226463691429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015436622397484309127619 1523154933596226463691429)
                ·
                  refine ⟨285591550049292461942143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523154933596226463691429 285591550049292461942143)
                  ·
                    rfl

theorem cell21_1251422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1251422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251422 prefixEnd_1251422 := by exact prefixLift 1251422
  have htrace : WordTrace (prefixWord ++ tailWord_1251422) baseStart_1251422 baseEnd_1251422 := by
    simpa [prefixWord, tailWord_1251422, baseEnd_1251422] using wordTrace_append hprefix tailTrace_1251422
  have hstable : (prefixWord ++ tailWord_1251422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251422).length < 2 ^ (prefixWord ++ tailWord_1251422).sum := by decide
  have hdescent : baseEnd_1251422 < baseStart_1251422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251441 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1251441 : Nat := 118140960795 + 1251441 * 2 ^ 59
def prefixEnd_1251441 : Nat := 4983230072969 + 3 ^ 40 * 1251441 * 2
def baseEnd_1251441 : Nat := 285595886108152651125437

theorem tailTrace_1251441 : CollatzResearch.WordTrace tailWord_1251441 prefixEnd_1251441 285595886108152651125437 := by
  unfold tailWord_1251441
  simp only [CollatzResearch.WordTrace]
  refine ⟨45643803059250460952066177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30429202039500307301377451 45643803059250460952066177)
  ·
    refine ⟨34232852294437845714049633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45643803059250460952066177 34232852294437845714049633)
    ·
      refine ⟨25674639220828384285537225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34232852294437845714049633 25674639220828384285537225)
      ·
        refine ⟨19255979415621288214152919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25674639220828384285537225 19255979415621288214152919)
        ·
          refine ⟨28883969123431932321229379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255979415621288214152919 28883969123431932321229379)
          ·
            refine ⟨43325953685147898481844069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28883969123431932321229379 43325953685147898481844069)
            ·
              refine ⟨8123616315965230965345763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43325953685147898481844069 8123616315965230965345763)
              ·
                refine ⟨12185424473947846448018645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123616315965230965345763 12185424473947846448018645)
                ·
                  refine ⟨285595886108152651125437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12185424473947846448018645 285595886108152651125437)
                  ·
                    rfl

theorem cell21_1251441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1251441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251441 prefixEnd_1251441 := by exact prefixLift 1251441
  have htrace : WordTrace (prefixWord ++ tailWord_1251441) baseStart_1251441 baseEnd_1251441 := by
    simpa [prefixWord, tailWord_1251441, baseEnd_1251441] using wordTrace_append hprefix tailTrace_1251441
  have hstable : (prefixWord ++ tailWord_1251441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251441).length < 2 ^ (prefixWord ++ tailWord_1251441).sum := by decide
  have hdescent : baseEnd_1251441 < baseStart_1251441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251489 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1251489 : Nat := 118140960795 + 1251489 * 2 ^ 59
def prefixEnd_1251489 : Nat := 4983230072969 + 3 ^ 40 * 1251489 * 2
def baseEnd_1251489 : Nat := 285606840362115234325339

theorem tailTrace_1251489 : CollatzResearch.WordTrace tailWord_1251489 prefixEnd_1251489 285606840362115234325339 := by
  unfold tailWord_1251489
  simp only [CollatzResearch.WordTrace]
  refine ⟨45645553763076565149813521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30430369175384376766542347 45645553763076565149813521)
  ·
    refine ⟨34234165322307423862360141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45645553763076565149813521 34234165322307423862360141)
    ·
      refine ⟨12837811995865283948385053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34234165322307423862360141 12837811995865283948385053)
      ·
        refine ⟨4814179498449481480644395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12837811995865283948385053 4814179498449481480644395)
        ·
          refine ⟨7221269247674222220966593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814179498449481480644395 7221269247674222220966593)
          ·
            refine ⟨5415951935755666665724945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7221269247674222220966593 5415951935755666665724945)
            ·
              refine ⟨4061963951816749999293709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5415951935755666665724945 4061963951816749999293709)
              ·
                refine ⟨1523236481931281249735141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4061963951816749999293709 1523236481931281249735141)
                ·
                  refine ⟨285606840362115234325339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523236481931281249735141 285606840362115234325339)
                  ·
                    rfl

theorem cell21_1251489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1251489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251489 prefixEnd_1251489 := by exact prefixLift 1251489
  have htrace : WordTrace (prefixWord ++ tailWord_1251489) baseStart_1251489 baseEnd_1251489 := by
    simpa [prefixWord, tailWord_1251489, baseEnd_1251489] using wordTrace_append hprefix tailTrace_1251489
  have hstable : (prefixWord ++ tailWord_1251489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251489).length < 2 ^ (prefixWord ++ tailWord_1251489).sum := by decide
  have hdescent : baseEnd_1251489 < baseStart_1251489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251509 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1251509 : Nat := 118140960795 + 1251509 * 2 ^ 59
def prefixEnd_1251509 : Nat := 4983230072969 + 3 ^ 40 * 1251509 * 2
def baseEnd_1251509 : Nat := 285611404634599643991965

theorem tailTrace_1251509 : CollatzResearch.WordTrace tailWord_1251509 prefixEnd_1251509 285611404634599643991965 := by
  unfold tailWord_1251509
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646283223004108565541581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30430855482002739043694387 45646283223004108565541581)
  ·
    refine ⟨17117356208626540712078093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45646283223004108565541581 17117356208626540712078093)
    ·
      refine ⟨6419008578234952767029285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17117356208626540712078093 6419008578234952767029285)
      ·
        refine ⟨1203564108419053643817991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6419008578234952767029285 1203564108419053643817991)
        ·
          refine ⟨1805346162628580465726987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203564108419053643817991 1805346162628580465726987)
          ·
            refine ⟨2708019243942870698590481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805346162628580465726987 2708019243942870698590481)
            ·
              refine ⟨2031014432957153023942861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708019243942870698590481 2031014432957153023942861)
              ·
                refine ⟨761630412358932383978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2031014432957153023942861 761630412358932383978573)
                ·
                  refine ⟨285611404634599643991965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761630412358932383978573 285611404634599643991965)
                  ·
                    rfl

theorem cell21_1251509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1251509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251509 prefixEnd_1251509 := by exact prefixLift 1251509
  have htrace : WordTrace (prefixWord ++ tailWord_1251509) baseStart_1251509 baseEnd_1251509 := by
    simpa [prefixWord, tailWord_1251509, baseEnd_1251509] using wordTrace_append hprefix tailTrace_1251509
  have hstable : (prefixWord ++ tailWord_1251509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251509).length < 2 ^ (prefixWord ++ tailWord_1251509).sum := by decide
  have hdescent : baseEnd_1251509 < baseStart_1251509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251517 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1251517 : Nat := 118140960795 + 1251517 * 2 ^ 59
def prefixEnd_1251517 : Nat := 4983230072969 + 3 ^ 40 * 1251517 * 2
def baseEnd_1251517 : Nat := 285613230343593407858615

theorem tailTrace_1251517 : CollatzResearch.WordTrace tailWord_1251517 prefixEnd_1251517 285613230343593407858615 := by
  unfold tailWord_1251517
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646575006975125931832805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30431050004650083954555203 45646575006975125931832805)
  ·
    refine ⟨8558732813807836112218651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45646575006975125931832805 8558732813807836112218651)
    ·
      refine ⟨12838099220711754168327977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558732813807836112218651 12838099220711754168327977)
      ·
        refine ⟨9628574415533815626245983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12838099220711754168327977 9628574415533815626245983)
        ·
          refine ⟨14442861623300723439368975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628574415533815626245983 14442861623300723439368975)
          ·
            refine ⟨21664292434951085159053463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14442861623300723439368975 21664292434951085159053463)
            ·
              refine ⟨32496438652426627738580195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21664292434951085159053463 32496438652426627738580195)
              ·
                refine ⟨48744657978639941607870293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32496438652426627738580195 48744657978639941607870293)
                ·
                  refine ⟨285613230343593407858615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48744657978639941607870293 285613230343593407858615)
                  ·
                    rfl

theorem cell21_1251517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1251517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251517 prefixEnd_1251517 := by exact prefixLift 1251517
  have htrace : WordTrace (prefixWord ++ tailWord_1251517) baseStart_1251517 baseEnd_1251517 := by
    simpa [prefixWord, tailWord_1251517, baseEnd_1251517] using wordTrace_append hprefix tailTrace_1251517
  have hstable : (prefixWord ++ tailWord_1251517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251517).length < 2 ^ (prefixWord ++ tailWord_1251517).sum := by decide
  have hdescent : baseEnd_1251517 < baseStart_1251517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251534 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1251534 : Nat := 118140960795 + 1251534 * 2 ^ 59
def prefixEnd_1251534 : Nat := 4983230072969 + 3 ^ 40 * 1251534 * 2
def baseEnd_1251534 : Nat := 285617109975205156075247

theorem tailTrace_1251534 : CollatzResearch.WordTrace tailWord_1251534 prefixEnd_1251534 285617109975205156075247 := by
  unfold tailWord_1251534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705899380989192229400207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30431463365275691890134437 5705899380989192229400207)
  ·
    refine ⟨8558849071483788344100311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5705899380989192229400207 8558849071483788344100311)
    ·
      refine ⟨12838273607225682516150467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558849071483788344100311 12838273607225682516150467)
      ·
        refine ⟨19257410410838523774225701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838273607225682516150467 19257410410838523774225701)
        ·
          refine ⟨3610764452032223207667319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19257410410838523774225701 3610764452032223207667319)
          ·
            refine ⟨5416146678048334811500979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610764452032223207667319 5416146678048334811500979)
            ·
              refine ⟨8124220017072502217251469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416146678048334811500979 8124220017072502217251469)
              ·
                refine ⟨3046582506402188331469301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8124220017072502217251469 3046582506402188331469301)
                ·
                  refine ⟨285617109975205156075247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3046582506402188331469301 285617109975205156075247)
                  ·
                    rfl

theorem cell21_1251534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1251534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251534 prefixEnd_1251534 := by exact prefixLift 1251534
  have htrace : WordTrace (prefixWord ++ tailWord_1251534) baseStart_1251534 baseEnd_1251534 := by
    simpa [prefixWord, tailWord_1251534, baseEnd_1251534] using wordTrace_append hprefix tailTrace_1251534
  have hstable : (prefixWord ++ tailWord_1251534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251534).length < 2 ^ (prefixWord ++ tailWord_1251534).sum := by decide
  have hdescent : baseEnd_1251534 < baseStart_1251534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251554 : List Nat := [3, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1251554 : Nat := 118140960795 + 1251554 * 2 ^ 59
def prefixEnd_1251554 : Nat := 4983230072969 + 3 ^ 40 * 1251554 * 2
def baseEnd_1251554 : Nat := 95207224749229855247291

theorem tailTrace_1251554 : CollatzResearch.WordTrace tailWord_1251554 prefixEnd_1251554 95207224749229855247291 := by
  unfold tailWord_1251554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411981126960270312732429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30431949671894054167286477 11411981126960270312732429)
  ·
    refine ⟨4279492922610101367274661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11411981126960270312732429 4279492922610101367274661)
    ·
      refine ⟨802404922989394006363999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4279492922610101367274661 802404922989394006363999)
      ·
        refine ⟨1203607384484091009545999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802404922989394006363999 1203607384484091009545999)
        ·
          refine ⟨1805411076726136514318999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203607384484091009545999 1805411076726136514318999)
          ·
            refine ⟨2708116615089204771478499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805411076726136514318999 2708116615089204771478499)
            ·
              refine ⟨4062174922633807157217749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708116615089204771478499 4062174922633807157217749)
              ·
                refine ⟨95207224749229855247291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4062174922633807157217749 95207224749229855247291)
                ·
                  rfl

theorem cell21_1251554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1251554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251554 prefixEnd_1251554 := by exact prefixLift 1251554
  have htrace : WordTrace (prefixWord ++ tailWord_1251554) baseStart_1251554 baseEnd_1251554 := by
    simpa [prefixWord, tailWord_1251554, baseEnd_1251554] using wordTrace_append hprefix tailTrace_1251554
  have hstable : (prefixWord ++ tailWord_1251554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251554).length < 2 ^ (prefixWord ++ tailWord_1251554).sum := by decide
  have hdescent : baseEnd_1251554 < baseStart_1251554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251641 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_1251641 : Nat := 118140960795 + 1251641 * 2 ^ 59
def prefixEnd_1251641 : Nat := 4983230072969 + 3 ^ 40 * 1251641 * 2
def baseEnd_1251641 : Nat := 285641528832996747791695

theorem tailTrace_1251641 : CollatzResearch.WordTrace tailWord_1251641 prefixEnd_1251641 285641528832996747791695 := by
  unfold tailWord_1251641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45651097658525895109346777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30434065105683930072897851 45651097658525895109346777)
  ·
    refine ⟨34238323243894421332010083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45651097658525895109346777 34238323243894421332010083)
    ·
      refine ⟨51357484865841631998015125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34238323243894421332010083 51357484865841631998015125)
      ·
        refine ⟨2407382103086326499906959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51357484865841631998015125 2407382103086326499906959)
        ·
          refine ⟨3611073154629489749860439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407382103086326499906959 3611073154629489749860439)
          ·
            refine ⟨5416609731944234624790659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611073154629489749860439 5416609731944234624790659)
            ·
              refine ⟨8124914597916351937185989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416609731944234624790659 8124914597916351937185989)
              ·
                refine ⟨1523421487109315988222373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8124914597916351937185989 1523421487109315988222373)
                ·
                  refine ⟨285641528832996747791695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523421487109315988222373 285641528832996747791695)
                  ·
                    rfl

theorem cell21_1251641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_1251641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251641 prefixEnd_1251641 := by exact prefixLift 1251641
  have htrace : WordTrace (prefixWord ++ tailWord_1251641) baseStart_1251641 baseEnd_1251641 := by
    simpa [prefixWord, tailWord_1251641, baseEnd_1251641] using wordTrace_append hprefix tailTrace_1251641
  have hstable : (prefixWord ++ tailWord_1251641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251641).length < 2 ^ (prefixWord ++ tailWord_1251641).sum := by decide
  have hdescent : baseEnd_1251641 < baseStart_1251641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251754 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_1251754 : Nat := 118140960795 + 1251754 * 2 ^ 59
def prefixEnd_1251754 : Nat := 4983230072969 + 3 ^ 40 * 1251754 * 2
def baseEnd_1251754 : Nat := 285667316972533662408131

theorem tailTrace_1251754 : CollatzResearch.WordTrace tailWord_1251754 prefixEnd_1251754 285667316972533662408131 := by
  unfold tailWord_1251754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413804776779128852052579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30436812738077676938806877 11413804776779128852052579)
  ·
    refine ⟨17120707165168693278078869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11413804776779128852052579 17120707165168693278078869)
    ·
      refine ⟨802533148367282497409947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17120707165168693278078869 802533148367282497409947)
      ·
        refine ⟨1203799722550923746114921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802533148367282497409947 1203799722550923746114921)
        ·
          refine ⟨902849791913192809586191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203799722550923746114921 902849791913192809586191)
          ·
            refine ⟨1354274687869789214379287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902849791913192809586191 1354274687869789214379287)
            ·
              refine ⟨2031412031804683821568931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354274687869789214379287 2031412031804683821568931)
              ·
                refine ⟨3047118047707025732353397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031412031804683821568931 3047118047707025732353397)
                ·
                  refine ⟨285667316972533662408131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047118047707025732353397 285667316972533662408131)
                  ·
                    rfl

theorem cell21_1251754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_1251754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251754 prefixEnd_1251754 := by exact prefixLift 1251754
  have htrace : WordTrace (prefixWord ++ tailWord_1251754) baseStart_1251754 baseEnd_1251754 := by
    simpa [prefixWord, tailWord_1251754, baseEnd_1251754] using wordTrace_append hprefix tailTrace_1251754
  have hstable : (prefixWord ++ tailWord_1251754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251754).length < 2 ^ (prefixWord ++ tailWord_1251754).sum := by decide
  have hdescent : baseEnd_1251754 < baseStart_1251754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251813 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1251813 : Nat := 118140960795 + 1251813 * 2 ^ 59
def prefixEnd_1251813 : Nat := 4983230072969 + 3 ^ 40 * 1251813 * 2
def baseEnd_1251813 : Nat := 285680781576362670924677

theorem tailTrace_1251813 : CollatzResearch.WordTrace tailWord_1251813 prefixEnd_1251813 285680781576362670924677 := by
  unfold tailWord_1251813
  simp only [CollatzResearch.WordTrace]
  refine ⟨45657371013902768484608093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30438247342601845656405395 45657371013902768484608093)
  ·
    refine ⟨17121514130213538181728035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45657371013902768484608093 17121514130213538181728035)
    ·
      refine ⟨25682271195320307272592053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17121514130213538181728035 25682271195320307272592053)
      ·
        refine ⟨2407712924561278806805505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25682271195320307272592053 2407712924561278806805505)
        ·
          refine ⟨1805784693420959105104129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407712924561278806805505 1805784693420959105104129)
          ·
            refine ⟨1354338520065719328828097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805784693420959105104129 1354338520065719328828097)
            ·
              refine ⟨1015753890049289496621073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354338520065719328828097 1015753890049289496621073)
              ·
                refine ⟨761815417536967122465805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015753890049289496621073 761815417536967122465805)
                ·
                  refine ⟨285680781576362670924677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761815417536967122465805 285680781576362670924677)
                  ·
                    rfl

theorem cell21_1251813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1251813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251813 prefixEnd_1251813 := by exact prefixLift 1251813
  have htrace : WordTrace (prefixWord ++ tailWord_1251813) baseStart_1251813 baseEnd_1251813 := by
    simpa [prefixWord, tailWord_1251813, baseEnd_1251813] using wordTrace_append hprefix tailTrace_1251813
  have hstable : (prefixWord ++ tailWord_1251813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251813).length < 2 ^ (prefixWord ++ tailWord_1251813).sum := by decide
  have hdescent : baseEnd_1251813 < baseStart_1251813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251869 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1251869 : Nat := 118140960795 + 1251869 * 2 ^ 59
def prefixEnd_1251869 : Nat := 4983230072969 + 3 ^ 40 * 1251869 * 2
def baseEnd_1251869 : Nat := 285693561539319017991229

theorem tailTrace_1251869 : CollatzResearch.WordTrace tailWord_1251869 prefixEnd_1251869 285693561539319017991229 := by
  unfold tailWord_1251869
  simp only [CollatzResearch.WordTrace]
  refine ⟨45659413501699890048646661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30439609001133260032431107 45659413501699890048646661)
  ·
    refine ⟨8561140031568729384121249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45659413501699890048646661 8561140031568729384121249)
    ·
      refine ⟨6420855023676547038090937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8561140031568729384121249 6420855023676547038090937)
      ·
        refine ⟨4815641267757410278568203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6420855023676547038090937 4815641267757410278568203)
        ·
          refine ⟨7223461901636115417852305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815641267757410278568203 7223461901636115417852305)
          ·
            refine ⟨5417596426227086563389229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7223461901636115417852305 5417596426227086563389229)
            ·
              refine ⟨2031598659835157461270961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5417596426227086563389229 2031598659835157461270961)
              ·
                refine ⟨1523698994876368095953221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031598659835157461270961 1523698994876368095953221)
                ·
                  refine ⟨285693561539319017991229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523698994876368095953221 285693561539319017991229)
                  ·
                    rfl

theorem cell21_1251869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1251869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251869 prefixEnd_1251869 := by exact prefixLift 1251869
  have htrace : WordTrace (prefixWord ++ tailWord_1251869) baseStart_1251869 baseEnd_1251869 := by
    simpa [prefixWord, tailWord_1251869, baseEnd_1251869] using wordTrace_append hprefix tailTrace_1251869
  have hstable : (prefixWord ++ tailWord_1251869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251869).length < 2 ^ (prefixWord ++ tailWord_1251869).sum := by decide
  have hdescent : baseEnd_1251869 < baseStart_1251869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251897 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1251897 : Nat := 118140960795 + 1251897 * 2 ^ 59
def prefixEnd_1251897 : Nat := 4983230072969 + 3 ^ 40 * 1251897 * 2
def baseEnd_1251897 : Nat := 285699951520797191524505

theorem tailTrace_1251897 : CollatzResearch.WordTrace tailWord_1251897 prefixEnd_1251897 285699951520797191524505 := by
  unfold tailWord_1251897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660434745598450830665945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30440289830398967220443963 45660434745598450830665945)
  ·
    refine ⟨34245326059198838122999459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45660434745598450830665945 34245326059198838122999459)
    ·
      refine ⟨51367989088798257184499189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34245326059198838122999459 51367989088798257184499189)
      ·
        refine ⟨4815748977074836611046799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51367989088798257184499189 4815748977074836611046799)
        ·
          refine ⟨7223623465612254916570199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815748977074836611046799 7223623465612254916570199)
          ·
            refine ⟨10835435198418382374855299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223623465612254916570199 10835435198418382374855299)
            ·
              refine ⟨16253152797627573562282949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10835435198418382374855299 16253152797627573562282949)
              ·
                refine ⟨3047466149555170042928053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16253152797627573562282949 3047466149555170042928053)
                ·
                  refine ⟨285699951520797191524505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047466149555170042928053 285699951520797191524505)
                  ·
                    rfl

theorem cell21_1251897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1251897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251897 prefixEnd_1251897 := by exact prefixLift 1251897
  have htrace : WordTrace (prefixWord ++ tailWord_1251897) baseStart_1251897 baseEnd_1251897 := by
    simpa [prefixWord, tailWord_1251897, baseEnd_1251897] using wordTrace_append hprefix tailTrace_1251897
  have hstable : (prefixWord ++ tailWord_1251897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251897).length < 2 ^ (prefixWord ++ tailWord_1251897).sum := by decide
  have hdescent : baseEnd_1251897 < baseStart_1251897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251900 : List Nat := [2, 2, 2, 2, 3, 3, 2, 5]
def baseStart_1251900 : Nat := 118140960795 + 1251900 * 2 ^ 59
def prefixEnd_1251900 : Nat := 4983230072969 + 3 ^ 40 * 1251900 * 2
def baseEnd_1251900 : Nat := 95233545387223284324833

theorem tailTrace_1251900 : CollatzResearch.WordTrace tailWord_1251900 prefixEnd_1251900 95233545387223284324833 := by
  unfold tailWord_1251900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830272082293791171512577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30440362776391721562016769 22830272082293791171512577)
  ·
    refine ⟨17122704061720343378634433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22830272082293791171512577 17122704061720343378634433)
    ·
      refine ⟨12842028046290257533975825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17122704061720343378634433 12842028046290257533975825)
      ·
        refine ⟨9631521034717693150481869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12842028046290257533975825 9631521034717693150481869)
        ·
          refine ⟨3611820388019134931430701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9631521034717693150481869 3611820388019134931430701)
          ·
            refine ⟨1354432645507175599286513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611820388019134931430701 1354432645507175599286513)
            ·
              refine ⟨1015824484130381699464885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354432645507175599286513 1015824484130381699464885)
              ·
                refine ⟨95233545387223284324833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015824484130381699464885 95233545387223284324833)
                ·
                  rfl

theorem cell21_1251900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_1251900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251900 prefixEnd_1251900 := by exact prefixLift 1251900
  have htrace : WordTrace (prefixWord ++ tailWord_1251900) baseStart_1251900 baseEnd_1251900 := by
    simpa [prefixWord, tailWord_1251900, baseEnd_1251900] using wordTrace_append hprefix tailTrace_1251900
  have hstable : (prefixWord ++ tailWord_1251900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251900).length < 2 ^ (prefixWord ++ tailWord_1251900).sum := by decide
  have hdescent : baseEnd_1251900 < baseStart_1251900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251934 : List Nat := [4, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1251934 : Nat := 118140960795 + 1251934 * 2 ^ 59
def prefixEnd_1251934 : Nat := 4983230072969 + 3 ^ 40 * 1251934 * 2
def baseEnd_1251934 : Nat := 95236131808297783135921

theorem tailTrace_1251934 : CollatzResearch.WordTrace tailWord_1251934 prefixEnd_1251934 95236131808297783135921 := by
  unfold tailWord_1251934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707723030808050768720357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30441189497642937433175237 5707723030808050768720357)
  ·
    refine ⟨1070198068276509519135067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5707723030808050768720357 1070198068276509519135067)
    ·
      refine ⟨1605297102414764278702601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070198068276509519135067 1605297102414764278702601)
      ·
        refine ⟨1203972826811073209026951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605297102414764278702601 1203972826811073209026951)
        ·
          refine ⟨1805959240216609813540427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203972826811073209026951 1805959240216609813540427)
          ·
            refine ⟨2708938860324914720310641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805959240216609813540427 2708938860324914720310641)
            ·
              refine ⟨2031704145243686040232981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708938860324914720310641 2031704145243686040232981)
              ·
                refine ⟨95236131808297783135921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2031704145243686040232981 95236131808297783135921)
                ·
                  rfl

theorem cell21_1251934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1251934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251934 prefixEnd_1251934 := by exact prefixLift 1251934
  have htrace : WordTrace (prefixWord ++ tailWord_1251934) baseStart_1251934 baseEnd_1251934 := by
    simpa [prefixWord, tailWord_1251934, baseEnd_1251934] using wordTrace_append hprefix tailTrace_1251934
  have hstable : (prefixWord ++ tailWord_1251934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251934).length < 2 ^ (prefixWord ++ tailWord_1251934).sum := by decide
  have hdescent : baseEnd_1251934 < baseStart_1251934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252004 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1252004 : Nat := 118140960795 + 1252004 * 2 ^ 59
def prefixEnd_1252004 : Nat := 4983230072969 + 3 ^ 40 * 1252004 * 2
def baseEnd_1252004 : Nat := 285724370378588783240953

theorem tailTrace_1252004 : CollatzResearch.WordTrace tailWord_1252004 prefixEnd_1252004 285724370378588783240953 := by
  unfold tailWord_1252004
  simp only [CollatzResearch.WordTrace]
  refine ⟨22832168678105404052405533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30442891570807205403207377 22832168678105404052405533)
  ·
    refine ⟨8562063254289526519652075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22832168678105404052405533 8562063254289526519652075)
    ·
      refine ⟨12843094881434289779478113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562063254289526519652075 12843094881434289779478113)
      ·
        refine ⟨9632321161075717334608585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12843094881434289779478113 9632321161075717334608585)
        ·
          refine ⟨7224240870806788000956439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9632321161075717334608585 7224240870806788000956439)
          ·
            refine ⟨10836361306210182001434659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7224240870806788000956439 10836361306210182001434659)
            ·
              refine ⟨16254541959315273002151989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836361306210182001434659 16254541959315273002151989)
              ·
                refine ⟨1523863308685806843951749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16254541959315273002151989 1523863308685806843951749)
                ·
                  refine ⟨285724370378588783240953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523863308685806843951749 285724370378588783240953)
                  ·
                    rfl

theorem cell21_1252004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1252004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252004 prefixEnd_1252004 := by exact prefixLift 1252004
  have htrace : WordTrace (prefixWord ++ tailWord_1252004) baseStart_1252004 baseEnd_1252004 := by
    simpa [prefixWord, tailWord_1252004, baseEnd_1252004] using wordTrace_append hprefix tailTrace_1252004
  have hstable : (prefixWord ++ tailWord_1252004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252004).length < 2 ^ (prefixWord ++ tailWord_1252004).sum := by decide
  have hdescent : baseEnd_1252004 < baseStart_1252004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252007 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_1252007 : Nat := 118140960795 + 1252007 * 2 ^ 59
def prefixEnd_1252007 : Nat := 4983230072969 + 3 ^ 40 * 1252007 * 2
def baseEnd_1252007 : Nat := 285725055019461444690947

theorem tailTrace_1252007 : CollatzResearch.WordTrace tailWord_1252007 prefixEnd_1252007 285725055019461444690947 := by
  unfold tailWord_1252007
  simp only [CollatzResearch.WordTrace]
  refine ⟨45664446775199939617170275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30442964516799959744780183 45664446775199939617170275)
  ·
    refine ⟨68496670162799909425755413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45664446775199939617170275 68496670162799909425755413)
    ·
      refine ⟨3210781413881245754332285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68496670162799909425755413 3210781413881245754332285)
      ·
        refine ⟨1204043030205467157874607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3210781413881245754332285 1204043030205467157874607)
        ·
          refine ⟨1806064545308200736811911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204043030205467157874607 1806064545308200736811911)
          ·
            refine ⟨2709096817962301105217867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806064545308200736811911 2709096817962301105217867)
            ·
              refine ⟨4063645226943451657826801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709096817962301105217867 4063645226943451657826801)
              ·
                refine ⟨3047733920207588743370101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063645226943451657826801 3047733920207588743370101)
                ·
                  refine ⟨285725055019461444690947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047733920207588743370101 285725055019461444690947)
                  ·
                    rfl

theorem cell21_1252007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_1252007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252007 prefixEnd_1252007 := by exact prefixLift 1252007
  have htrace : WordTrace (prefixWord ++ tailWord_1252007) baseStart_1252007 baseEnd_1252007 := by
    simpa [prefixWord, tailWord_1252007, baseEnd_1252007] using wordTrace_append hprefix tailTrace_1252007
  have hstable : (prefixWord ++ tailWord_1252007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252007).length < 2 ^ (prefixWord ++ tailWord_1252007).sum := by decide
  have hdescent : baseEnd_1252007 < baseStart_1252007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252049 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_1252049 : Nat := 118140960795 + 1252049 * 2 ^ 59
def prefixEnd_1252049 : Nat := 4983230072969 + 3 ^ 40 * 1252049 * 2
def baseEnd_1252049 : Nat := 285734639991678704990861

theorem tailTrace_1252049 : CollatzResearch.WordTrace tailWord_1252049 prefixEnd_1252049 285734639991678704990861 := by
  unfold tailWord_1252049
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665978641047780790199201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30443985760698520526799467 45665978641047780790199201)
  ·
    refine ⟨34249483980785835592649401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45665978641047780790199201 34249483980785835592649401)
    ·
      refine ⟨25687112985589376694487051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34249483980785835592649401 25687112985589376694487051)
      ·
        refine ⟨38530669478384065041730577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25687112985589376694487051 38530669478384065041730577)
        ·
          refine ⟨28898002108788048781297933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38530669478384065041730577 28898002108788048781297933)
          ·
            refine ⟨10836750790795518292986725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28898002108788048781297933 10836750790795518292986725)
            ·
              refine ⟨2031890773274159679935011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10836750790795518292986725 2031890773274159679935011)
              ·
                refine ⟨3047836159911239519902517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031890773274159679935011 3047836159911239519902517)
                ·
                  refine ⟨285734639991678704990861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047836159911239519902517 285734639991678704990861)
                  ·
                    rfl

theorem cell21_1252049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_1252049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252049 prefixEnd_1252049 := by exact prefixLift 1252049
  have htrace : WordTrace (prefixWord ++ tailWord_1252049) baseStart_1252049 baseEnd_1252049 := by
    simpa [prefixWord, tailWord_1252049, baseEnd_1252049] using wordTrace_append hprefix tailTrace_1252049
  have hstable : (prefixWord ++ tailWord_1252049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252049).length < 2 ^ (prefixWord ++ tailWord_1252049).sum := by decide
  have hdescent : baseEnd_1252049 < baseStart_1252049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252114 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1252114 : Nat := 118140960795 + 1252114 * 2 ^ 59
def prefixEnd_1252114 : Nat := 4983230072969 + 3 ^ 40 * 1252114 * 2
def baseEnd_1252114 : Nat := 285749473877253036407395

theorem tailTrace_1252114 : CollatzResearch.WordTrace tailWord_1252114 prefixEnd_1252114 285749473877253036407395 := by
  unfold tailWord_1252114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417087346453074222828849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30445566257208197927543597 11417087346453074222828849)
  ·
    refine ⟨8562815509839805667121637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11417087346453074222828849 8562815509839805667121637)
    ·
      refine ⟨1605527908094963562585307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8562815509839805667121637 1605527908094963562585307)
      ·
        refine ⟨2408291862142445343877961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605527908094963562585307 2408291862142445343877961)
        ·
          refine ⟨1806218896606834007908471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408291862142445343877961 1806218896606834007908471)
          ·
            refine ⟨2709328344910251011862707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806218896606834007908471 2709328344910251011862707)
            ·
              refine ⟨4063992517365376517794061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709328344910251011862707 4063992517365376517794061)
              ·
                refine ⟨1523997194012016194172773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4063992517365376517794061 1523997194012016194172773)
                ·
                  refine ⟨285749473877253036407395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523997194012016194172773 285749473877253036407395)
                  ·
                    rfl

theorem cell21_1252114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1252114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252114 prefixEnd_1252114 := by exact prefixLift 1252114
  have htrace : WordTrace (prefixWord ++ tailWord_1252114) baseStart_1252114 baseEnd_1252114 := by
    simpa [prefixWord, tailWord_1252114, baseEnd_1252114] using wordTrace_append hprefix tailTrace_1252114
  have hstable : (prefixWord ++ tailWord_1252114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252114).length < 2 ^ (prefixWord ++ tailWord_1252114).sum := by decide
  have hdescent : baseEnd_1252114 < baseStart_1252114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252153 : List Nat := [1, 2, 1, 17]
def baseStart_1252153 : Nat := 118140960795 + 1252153 * 2 ^ 59
def prefixEnd_1252153 : Nat := 4983230072969 + 3 ^ 40 * 1252153 * 2
def baseEnd_1252153 : Nat := 1175960387689702202705

theorem tailTrace_1252153 : CollatzResearch.WordTrace tailWord_1252153 prefixEnd_1252153 1175960387689702202705 := by
  unfold tailWord_1252153
  simp only [CollatzResearch.WordTrace]
  refine ⟨45669771832671006551985113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30446514555114004367990075 45669771832671006551985113)
  ·
    refine ⟨34252328874503254913988835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45669771832671006551985113 34252328874503254913988835)
    ·
      refine ⟨51378493311754882370983253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34252328874503254913988835 51378493311754882370983253)
      ·
        refine ⟨1175960387689702202705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 51378493311754882370983253 1175960387689702202705)
        ·
          rfl

theorem cell21_1252153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 17].length) (baseStart_1252153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252153 prefixEnd_1252153 := by exact prefixLift 1252153
  have htrace : WordTrace (prefixWord ++ tailWord_1252153) baseStart_1252153 baseEnd_1252153 := by
    simpa [prefixWord, tailWord_1252153, baseEnd_1252153] using wordTrace_append hprefix tailTrace_1252153
  have hstable : (prefixWord ++ tailWord_1252153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252153).length < 2 ^ (prefixWord ++ tailWord_1252153).sum := by decide
  have hdescent : baseEnd_1252153 < baseStart_1252153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252159 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 3]
def baseStart_1252159 : Nat := 118140960795 + 1252159 * 2 ^ 59
def prefixEnd_1252159 : Nat := 4983230072969 + 3 ^ 40 * 1252159 * 2
def baseEnd_1252159 : Nat := 285759743490342958157303

theorem tailTrace_1252159 : CollatzResearch.WordTrace tailWord_1252159 prefixEnd_1252159 285759743490342958157303 := by
  unfold tailWord_1252159
  simp only [CollatzResearch.WordTrace]
  refine ⟨45669990670649269576703531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30446660447099513051135687 45669990670649269576703531)
  ·
    refine ⟨68504986005973904365055297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45669990670649269576703531 68504986005973904365055297)
    ·
      refine ⟨51378739504480428273791473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68504986005973904365055297 51378739504480428273791473)
      ·
        refine ⟨38534054628360321205343605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51378739504480428273791473 38534054628360321205343605)
        ·
          refine ⟨3612567621408780113000963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38534054628360321205343605 3612567621408780113000963)
          ·
            refine ⟨5418851432113170169501445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612567621408780113000963 5418851432113170169501445)
            ·
              refine ⟨1016034643521219406781521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5418851432113170169501445 1016034643521219406781521)
              ·
                refine ⟨762025982640914555086141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016034643521219406781521 762025982640914555086141)
                ·
                  refine ⟨285759743490342958157303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762025982640914555086141 285759743490342958157303)
                  ·
                    rfl

theorem cell21_1252159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].length) (baseStart_1252159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252159 prefixEnd_1252159 := by exact prefixLift 1252159
  have htrace : WordTrace (prefixWord ++ tailWord_1252159) baseStart_1252159 baseEnd_1252159 := by
    simpa [prefixWord, tailWord_1252159, baseEnd_1252159] using wordTrace_append hprefix tailTrace_1252159
  have hstable : (prefixWord ++ tailWord_1252159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252159).length < 2 ^ (prefixWord ++ tailWord_1252159).sum := by decide
  have hdescent : baseEnd_1252159 < baseStart_1252159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252252 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1252252 : Nat := 118140960795 + 1252252 * 2 ^ 59
def prefixEnd_1252252 : Nat := 4983230072969 + 3 ^ 40 * 1252252 * 2
def baseEnd_1252252 : Nat := 285780967357395463107113

theorem tailTrace_1252252 : CollatzResearch.WordTrace tailWord_1252252 prefixEnd_1252252 285780967357395463107113 := by
  unfold tailWord_1252252
  simp only [CollatzResearch.WordTrace]
  refine ⟨22836691329656173229919505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30448921772874897639892673 22836691329656173229919505)
  ·
    refine ⟨17127518497242129922439629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22836691329656173229919505 17127518497242129922439629)
    ·
      refine ⟨6422819436465798720914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17127518497242129922439629 6422819436465798720914861)
      ·
        refine ⟨2408557288674674520343073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6422819436465798720914861 2408557288674674520343073)
        ·
          refine ⟨1806417966506005890257305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408557288674674520343073 1806417966506005890257305)
          ·
            refine ⟨1354813474879504417692979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806417966506005890257305 1354813474879504417692979)
            ·
              refine ⟨2032220212319256626539469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354813474879504417692979 2032220212319256626539469)
              ·
                refine ⟨762082579619721234952301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032220212319256626539469 762082579619721234952301)
                ·
                  refine ⟨285780967357395463107113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762082579619721234952301 285780967357395463107113)
                  ·
                    rfl

theorem cell21_1252252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1252252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252252 prefixEnd_1252252 := by exact prefixLift 1252252
  have htrace : WordTrace (prefixWord ++ tailWord_1252252) baseStart_1252252 baseEnd_1252252 := by
    simpa [prefixWord, tailWord_1252252, baseEnd_1252252] using wordTrace_append hprefix tailTrace_1252252
  have hstable : (prefixWord ++ tailWord_1252252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252252).length < 2 ^ (prefixWord ++ tailWord_1252252).sum := by decide
  have hdescent : baseEnd_1252252 < baseStart_1252252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252263 : List Nat := [1, 1, 6, 1, 3, 2, 7]
def baseStart_1252263 : Nat := 118140960795 + 1252263 * 2 ^ 59
def prefixEnd_1252263 : Nat := 4983230072969 + 3 ^ 40 * 1252263 * 2
def baseEnd_1252263 : Nat := 31753719745251320935973

theorem tailTrace_1252263 : CollatzResearch.WordTrace tailWord_1252263 prefixEnd_1252263 31753719745251320935973 := by
  unfold tailWord_1252263
  simp only [CollatzResearch.WordTrace]
  refine ⟨45673783862272495338489443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30449189241514996892326295 45673783862272495338489443)
  ·
    refine ⟨68510675793408743007734165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45673783862272495338489443 68510675793408743007734165)
    ·
      refine ⟨3211437927816034828487539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68510675793408743007734165 3211437927816034828487539)
      ·
        refine ⟨4817156891724052242731309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211437927816034828487539 4817156891724052242731309)
        ·
          refine ⟨1806433834396519591024241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4817156891724052242731309 1806433834396519591024241)
          ·
            refine ⟨1354825375797389693268181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806433834396519591024241 1354825375797389693268181)
            ·
              refine ⟨31753719745251320935973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1354825375797389693268181 31753719745251320935973)
              ·
                rfl

theorem cell21_1252263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 7].length) (baseStart_1252263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252263 prefixEnd_1252263 := by exact prefixLift 1252263
  have htrace : WordTrace (prefixWord ++ tailWord_1252263) baseStart_1252263 baseEnd_1252263 := by
    simpa [prefixWord, tailWord_1252263, baseEnd_1252263] using wordTrace_append hprefix tailTrace_1252263
  have hstable : (prefixWord ++ tailWord_1252263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252263).length < 2 ^ (prefixWord ++ tailWord_1252263).sum := by decide
  have hdescent : baseEnd_1252263 < baseStart_1252263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252269 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1252269 : Nat := 118140960795 + 1252269 * 2 ^ 59
def prefixEnd_1252269 : Nat := 4983230072969 + 3 ^ 40 * 1252269 * 2
def baseEnd_1252269 : Nat := 285784846989007211323745

theorem tailTrace_1252269 : CollatzResearch.WordTrace tailWord_1252269 prefixEnd_1252269 285784846989007211323745 := by
  unfold tailWord_1252269
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674002700250758363207861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30449335133500505575471907 45674002700250758363207861)
  ·
    refine ⟨4281937753148508596550737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45674002700250758363207861 4281937753148508596550737)
    ·
      refine ⟨3211453314861381447413053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4281937753148508596550737 3211453314861381447413053)
      ·
        refine ⟨1204294993073018042779895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3211453314861381447413053 1204294993073018042779895)
        ·
          refine ⟨1806442489609527064169843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204294993073018042779895 1806442489609527064169843)
          ·
            refine ⟨2709663734414290596254765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806442489609527064169843 2709663734414290596254765)
            ·
              refine ⟨1016123900405358973595537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2709663734414290596254765 1016123900405358973595537)
              ·
                refine ⟨762092925304019230196653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016123900405358973595537 762092925304019230196653)
                ·
                  refine ⟨285784846989007211323745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762092925304019230196653 285784846989007211323745)
                  ·
                    rfl

theorem cell21_1252269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1252269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252269 prefixEnd_1252269 := by exact prefixLift 1252269
  have htrace : WordTrace (prefixWord ++ tailWord_1252269) baseStart_1252269 baseEnd_1252269 := by
    simpa [prefixWord, tailWord_1252269, baseEnd_1252269] using wordTrace_append hprefix tailTrace_1252269
  have hstable : (prefixWord ++ tailWord_1252269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252269).length < 2 ^ (prefixWord ++ tailWord_1252269).sum := by decide
  have hdescent : baseEnd_1252269 < baseStart_1252269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252291 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_1252291 : Nat := 118140960795 + 1252291 * 2 ^ 59
def prefixEnd_1252291 : Nat := 4983230072969 + 3 ^ 40 * 1252291 * 2
def baseEnd_1252291 : Nat := 285789867688740061957033

theorem tailTrace_1252291 : CollatzResearch.WordTrace tailWord_1252291 prefixEnd_1252291 285789867688740061957033 := by
  unfold tailWord_1252291
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674805106171056120508727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30449870070780704080339151 45674805106171056120508727)
  ·
    refine ⟨68512207659256584180763091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45674805106171056120508727 68512207659256584180763091)
    ·
      refine ⟨102768311488884876271144637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68512207659256584180763091 102768311488884876271144637)
      ·
        refine ⟨38538116808331828601679239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102768311488884876271144637 38538116808331828601679239)
        ·
          refine ⟨57807175212497742902518859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38538116808331828601679239 57807175212497742902518859)
          ·
            refine ⟨86710762818746614353778289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57807175212497742902518859 86710762818746614353778289)
            ·
              refine ⟨65033072114059960765333717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86710762818746614353778289 65033072114059960765333717)
              ·
                refine ⟨1524212627673280330437509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65033072114059960765333717 1524212627673280330437509)
                ·
                  refine ⟨285789867688740061957033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524212627673280330437509 285789867688740061957033)
                  ·
                    rfl

theorem cell21_1252291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_1252291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252291 prefixEnd_1252291 := by exact prefixLift 1252291
  have htrace : WordTrace (prefixWord ++ tailWord_1252291) baseStart_1252291 baseEnd_1252291 := by
    simpa [prefixWord, tailWord_1252291, baseEnd_1252291] using wordTrace_append hprefix tailTrace_1252291
  have hstable : (prefixWord ++ tailWord_1252291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252291).length < 2 ^ (prefixWord ++ tailWord_1252291).sum := by decide
  have hdescent : baseEnd_1252291 < baseStart_1252291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252305 : List Nat := [1, 2, 2, 1, 2, 1, 3, 9]
def baseStart_1252305 : Nat := 118140960795 + 1252305 * 2 ^ 59
def prefixEnd_1252305 : Nat := 4983230072969 + 3 ^ 40 * 1252305 * 2
def baseEnd_1252305 : Nat := 95264354226493049574557

theorem tailTrace_1252305 : CollatzResearch.WordTrace tailWord_1252305 prefixEnd_1252305 95264354226493049574557 := by
  unfold tailWord_1252305
  simp only [CollatzResearch.WordTrace]
  refine ⟨45675315728120336511518369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30450210485413557674345579 45675315728120336511518369)
  ·
    refine ⟨34256486796090252383638777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45675315728120336511518369 34256486796090252383638777)
    ·
      refine ⟨25692365097067689287729083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34256486796090252383638777 25692365097067689287729083)
      ·
        refine ⟨38538547645601533931593625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25692365097067689287729083 38538547645601533931593625)
        ·
          refine ⟨28903910734201150448695219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38538547645601533931593625 28903910734201150448695219)
          ·
            refine ⟨43355866101301725673042829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28903910734201150448695219 43355866101301725673042829)
            ·
              refine ⟨16258449787988147127391061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43355866101301725673042829 16258449787988147127391061)
              ·
                refine ⟨95264354226493049574557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16258449787988147127391061 95264354226493049574557)
                ·
                  rfl

theorem cell21_1252305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_1252305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252305 prefixEnd_1252305 := by exact prefixLift 1252305
  have htrace : WordTrace (prefixWord ++ tailWord_1252305) baseStart_1252305 baseEnd_1252305 := by
    simpa [prefixWord, tailWord_1252305, baseEnd_1252305] using wordTrace_append hprefix tailTrace_1252305
  have hstable : (prefixWord ++ tailWord_1252305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252305).length < 2 ^ (prefixWord ++ tailWord_1252305).sum := by decide
  have hdescent : baseEnd_1252305 < baseStart_1252305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252336 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_1252336 : Nat := 118140960795 + 1252336 * 2 ^ 59
def prefixEnd_1252336 : Nat := 4983230072969 + 3 ^ 40 * 1252336 * 2
def baseEnd_1252336 : Nat := 285800137301829983706941

theorem tailTrace_1252336 : CollatzResearch.WordTrace tailWord_1252336 prefixEnd_1252336 285800137301829983706941 := by
  unfold tailWord_1252336
  simp only [CollatzResearch.WordTrace]
  refine ⟨22838223195504014402948431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30450964260672019203931241 22838223195504014402948431)
  ·
    refine ⟨34257334793256021604422647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22838223195504014402948431 34257334793256021604422647)
    ·
      refine ⟨51386002189884032406633971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34257334793256021604422647 51386002189884032406633971)
      ·
        refine ⟨77079003284826048609950957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51386002189884032406633971 77079003284826048609950957)
        ·
          refine ⟨28904626231809768228731609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77079003284826048609950957 28904626231809768228731609)
          ·
            refine ⟨21678469673857326171548707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28904626231809768228731609 21678469673857326171548707)
            ·
              refine ⟨32517704510785989257323061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21678469673857326171548707 32517704510785989257323061)
              ·
                refine ⟨3048534797886186492874037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32517704510785989257323061 3048534797886186492874037)
                ·
                  refine ⟨285800137301829983706941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3048534797886186492874037 285800137301829983706941)
                  ·
                    rfl

theorem cell21_1252336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_1252336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252336 prefixEnd_1252336 := by exact prefixLift 1252336
  have htrace : WordTrace (prefixWord ++ tailWord_1252336) baseStart_1252336 baseEnd_1252336 := by
    simpa [prefixWord, tailWord_1252336, baseEnd_1252336] using wordTrace_append hprefix tailTrace_1252336
  have hstable : (prefixWord ++ tailWord_1252336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252336).length < 2 ^ (prefixWord ++ tailWord_1252336).sum := by decide
  have hdescent : baseEnd_1252336 < baseStart_1252336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252353 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1252353 : Nat := 118140960795 + 1252353 * 2 ^ 59
def prefixEnd_1252353 : Nat := 4983230072969 + 3 ^ 40 * 1252353 * 2
def baseEnd_1252353 : Nat := 285804016933441731923573

theorem tailTrace_1252353 : CollatzResearch.WordTrace tailWord_1252353 prefixEnd_1252353 285804016933441731923573 := by
  unfold tailWord_1252353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45677066431946440709265713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30451377621297627139510475 45677066431946440709265713)
  ·
    refine ⟨34257799823959830531949285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45677066431946440709265713 34257799823959830531949285)
    ·
      refine ⟨6423337466992468224740491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34257799823959830531949285 6423337466992468224740491)
      ·
        refine ⟨9635006200488702337110737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423337466992468224740491 9635006200488702337110737)
        ·
          refine ⟨7226254650366526752833053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9635006200488702337110737 7226254650366526752833053)
          ·
            refine ⟨2709845493887447532312395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7226254650366526752833053 2709845493887447532312395)
            ·
              refine ⟨4064768240831171298468593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709845493887447532312395 4064768240831171298468593)
              ·
                refine ⟨3048576180623378473851445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064768240831171298468593 3048576180623378473851445)
                ·
                  refine ⟨285804016933441731923573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3048576180623378473851445 285804016933441731923573)
                  ·
                    rfl

theorem cell21_1252353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1252353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252353 prefixEnd_1252353 := by exact prefixLift 1252353
  have htrace : WordTrace (prefixWord ++ tailWord_1252353) baseStart_1252353 baseEnd_1252353 := by
    simpa [prefixWord, tailWord_1252353, baseEnd_1252353] using wordTrace_append hprefix tailTrace_1252353
  have hstable : (prefixWord ++ tailWord_1252353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252353).length < 2 ^ (prefixWord ++ tailWord_1252353).sum := by decide
  have hdescent : baseEnd_1252353 < baseStart_1252353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252398 : List Nat := [4, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1252398 : Nat := 118140960795 + 1252398 * 2 ^ 59
def prefixEnd_1252398 : Nat := 4983230072969 + 3 ^ 40 * 1252398 * 2
def baseEnd_1252398 : Nat := 95271428848843884557827

theorem tailTrace_1252398 : CollatzResearch.WordTrace tailWord_1252398 prefixEnd_1252398 95271428848843884557827 := by
  unfold tailWord_1252398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709838464597926674331731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30452471811188942263102565 5709838464597926674331731)
  ·
    refine ⟨8564757696896890011497597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709838464597926674331731 8564757696896890011497597)
    ·
      refine ⟨3211784136336333754311599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8564757696896890011497597 3211784136336333754311599)
      ·
        refine ⟨4817676204504500631467399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211784136336333754311599 4817676204504500631467399)
        ·
          refine ⟨7226514306756750947201099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817676204504500631467399 7226514306756750947201099)
          ·
            refine ⟨10839771460135126420801649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226514306756750947201099 10839771460135126420801649)
            ·
              refine ⟨8129828595101344815601237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839771460135126420801649 8129828595101344815601237)
              ·
                refine ⟨95271428848843884557827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8129828595101344815601237 95271428848843884557827)
                ·
                  rfl

theorem cell21_1252398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1252398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252398 prefixEnd_1252398 := by exact prefixLift 1252398
  have htrace : WordTrace (prefixWord ++ tailWord_1252398) baseStart_1252398 baseEnd_1252398 := by
    simpa [prefixWord, tailWord_1252398, baseEnd_1252398] using wordTrace_append hprefix tailTrace_1252398
  have hstable : (prefixWord ++ tailWord_1252398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252398).length < 2 ^ (prefixWord ++ tailWord_1252398).sum := by decide
  have hdescent : baseEnd_1252398 < baseStart_1252398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252457 : List Nat := [1, 2, 1, 1, 1, 6, 1, 8]
def baseStart_1252457 : Nat := 118140960795 + 1252457 * 2 ^ 59
def prefixEnd_1252457 : Nat := 4983230072969 + 3 ^ 40 * 1252457 * 2
def baseEnd_1252457 : Nat := 95275917050120220730009

theorem tailTrace_1252457 : CollatzResearch.WordTrace tailWord_1252457 prefixEnd_1252457 95275917050120220730009 := by
  unfold tailWord_1252457
  simp only [CollatzResearch.WordTrace]
  refine ⟨45680859623569666471051625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30453906415713110980701083 45680859623569666471051625)
  ·
    refine ⟨34260644717677249853288719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45680859623569666471051625 34260644717677249853288719)
    ·
      refine ⟨51390967076515874779933079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34260644717677249853288719 51390967076515874779933079)
      ·
        refine ⟨77086450614773812169899619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51390967076515874779933079 77086450614773812169899619)
        ·
          refine ⟨115629675922160718254849429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77086450614773812169899619 115629675922160718254849429)
          ·
            refine ⟨5420141058851283668196067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115629675922160718254849429 5420141058851283668196067)
            ·
              refine ⟨8130211588276925502294101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420141058851283668196067 8130211588276925502294101)
              ·
                refine ⟨95275917050120220730009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8130211588276925502294101 95275917050120220730009)
                ·
                  rfl

theorem cell21_1252457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_1252457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252457 prefixEnd_1252457 := by exact prefixLift 1252457
  have htrace : WordTrace (prefixWord ++ tailWord_1252457) baseStart_1252457 baseEnd_1252457 := by
    simpa [prefixWord, tailWord_1252457, baseEnd_1252457] using wordTrace_append hprefix tailTrace_1252457
  have hstable : (prefixWord ++ tailWord_1252457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252457).length < 2 ^ (prefixWord ++ tailWord_1252457).sum := by decide
  have hdescent : baseEnd_1252457 < baseStart_1252457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252522 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1252522 : Nat := 118140960795 + 1252522 * 2 ^ 59
def prefixEnd_1252522 : Nat := 4983230072969 + 3 ^ 40 * 1252522 * 2
def baseEnd_1252522 : Nat := 285842585035934993606561

theorem tailTrace_1252522 : CollatzResearch.WordTrace tailWord_1252522 prefixEnd_1252522 285842585035934993606561 := by
  unfold tailWord_1252522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11420807592083545643041955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30455486912222788381445213 11420807592083545643041955)
  ·
    refine ⟨17131211388125318464562933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11420807592083545643041955 17131211388125318464562933)
    ·
      refine ⟨1606051067636748606052775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17131211388125318464562933 1606051067636748606052775)
      ·
        refine ⟨2409076601455122909079163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606051067636748606052775 2409076601455122909079163)
        ·
          refine ⟨3613614902182684363618745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409076601455122909079163 3613614902182684363618745)
          ·
            refine ⟨2710211176637013272714059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3613614902182684363618745 2710211176637013272714059)
            ·
              refine ⟨4065316764955519909071089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710211176637013272714059 4065316764955519909071089)
              ·
                refine ⟨3048987573716639931803317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065316764955519909071089 3048987573716639931803317)
                ·
                  refine ⟨285842585035934993606561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3048987573716639931803317 285842585035934993606561)
                  ·
                    rfl

theorem cell21_1252522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1252522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252522 prefixEnd_1252522 := by exact prefixLift 1252522
  have htrace : WordTrace (prefixWord ++ tailWord_1252522) baseStart_1252522 baseEnd_1252522 := by
    simpa [prefixWord, tailWord_1252522, baseEnd_1252522] using wordTrace_append hprefix tailTrace_1252522
  have hstable : (prefixWord ++ tailWord_1252522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252522).length < 2 ^ (prefixWord ++ tailWord_1252522).sum := by decide
  have hdescent : baseEnd_1252522 < baseStart_1252522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252609 : List Nat := [1, 2, 4, 1, 1, 3, 9]
def baseStart_1252609 : Nat := 118140960795 + 1252609 * 2 ^ 59
def prefixEnd_1252609 : Nat := 4983230072969 + 3 ^ 40 * 1252609 * 2
def baseEnd_1252609 : Nat := 31762493291249130628487

theorem tailTrace_1252609 : CollatzResearch.WordTrace tailWord_1252609 prefixEnd_1252609 31762493291249130628487 := by
  unfold tailWord_1252609
  simp only [CollatzResearch.WordTrace]
  refine ⟨45686403519018996430584881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30457602346012664287056587 45686403519018996430584881)
  ·
    refine ⟨34264802639264247322938661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45686403519018996430584881 34264802639264247322938661)
    ·
      refine ⟨6424650494862046373050999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34264802639264247322938661 6424650494862046373050999)
      ·
        refine ⟨9636975742293069559576499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424650494862046373050999 9636975742293069559576499)
        ·
          refine ⟨14455463613439604339364749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636975742293069559576499 14455463613439604339364749)
          ·
            refine ⟨5420798855039851627261781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14455463613439604339364749 5420798855039851627261781)
            ·
              refine ⟨31762493291249130628487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5420798855039851627261781 31762493291249130628487)
              ·
                rfl

theorem cell21_1252609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 9].length) (baseStart_1252609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252609 prefixEnd_1252609 := by exact prefixLift 1252609
  have htrace : WordTrace (prefixWord ++ tailWord_1252609) baseStart_1252609 baseEnd_1252609 := by
    simpa [prefixWord, tailWord_1252609, baseEnd_1252609] using wordTrace_append hprefix tailTrace_1252609
  have hstable : (prefixWord ++ tailWord_1252609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252609).length < 2 ^ (prefixWord ++ tailWord_1252609).sum := by decide
  have hdescent : baseEnd_1252609 < baseStart_1252609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252671 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_1252671 : Nat := 118140960795 + 1252671 * 2 ^ 59
def prefixEnd_1252671 : Nat := 4983230072969 + 3 ^ 40 * 1252671 * 2
def baseEnd_1252671 : Nat := 285876588865943845622923

theorem tailTrace_1252671 : CollatzResearch.WordTrace tailWord_1252671 prefixEnd_1252671 285876588865943845622923 := by
  unfold tailWord_1252671
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688664844794381019341867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30459109896529587346227911 45688664844794381019341867)
  ·
    refine ⟨68532997267191571529012801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45688664844794381019341867 68532997267191571529012801)
    ·
      refine ⟨51399747950393678646759601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68532997267191571529012801 51399747950393678646759601)
      ·
        refine ⟨38549810962795258985069701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51399747950393678646759601 38549810962795258985069701)
        ·
          refine ⟨7228089555524111059700569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38549810962795258985069701 7228089555524111059700569)
          ·
            refine ⟨5421067166643083294775427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7228089555524111059700569 5421067166643083294775427)
            ·
              refine ⟨8131600749964624942163141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421067166643083294775427 8131600749964624942163141)
              ·
                refine ⟨1524675140618367176655589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8131600749964624942163141 1524675140618367176655589)
                ·
                  refine ⟨285876588865943845622923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524675140618367176655589 285876588865943845622923)
                  ·
                    rfl

theorem cell21_1252671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_1252671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252671 prefixEnd_1252671 := by exact prefixLift 1252671
  have htrace : WordTrace (prefixWord ++ tailWord_1252671) baseStart_1252671 baseEnd_1252671 := by
    simpa [prefixWord, tailWord_1252671, baseEnd_1252671] using wordTrace_append hprefix tailTrace_1252671
  have hstable : (prefixWord ++ tailWord_1252671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252671).length < 2 ^ (prefixWord ++ tailWord_1252671).sum := by decide
  have hdescent : baseEnd_1252671 < baseStart_1252671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252694 : List Nat := [5, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1252694 : Nat := 118140960795 + 1252694 * 2 ^ 59
def prefixEnd_1252694 : Nat := 4983230072969 + 3 ^ 40 * 1252694 * 2
def baseEnd_1252694 : Nat := 95293945926433638913181

theorem tailTrace_1252694 : CollatzResearch.WordTrace tailWord_1252694 prefixEnd_1252694 95293945926433638913181 := by
  unfold tailWord_1252694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855593982731940996714321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30459669149140703964952757 2855593982731940996714321)
  ·
    refine ⟨2141695487048955747535741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2855593982731940996714321 2141695487048955747535741)
    ·
      refine ⟨803135807643358405325903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2141695487048955747535741 803135807643358405325903)
      ·
        refine ⟨1204703711465037607988855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803135807643358405325903 1204703711465037607988855)
        ·
          refine ⟨1807055567197556411983283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204703711465037607988855 1807055567197556411983283)
          ·
            refine ⟨2710583350796334617974925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807055567197556411983283 2710583350796334617974925)
            ·
              refine ⟨1016468756548625481740597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2710583350796334617974925 1016468756548625481740597)
              ·
                refine ⟨95293945926433638913181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016468756548625481740597 95293945926433638913181)
                ·
                  rfl

theorem cell21_1252694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1252694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252694 prefixEnd_1252694 := by exact prefixLift 1252694
  have htrace : WordTrace (prefixWord ++ tailWord_1252694) baseStart_1252694 baseEnd_1252694 := by
    simpa [prefixWord, tailWord_1252694, baseEnd_1252694] using wordTrace_append hprefix tailTrace_1252694
  have hstable : (prefixWord ++ tailWord_1252694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252694).length < 2 ^ (prefixWord ++ tailWord_1252694).sum := by decide
  have hdescent : baseEnd_1252694 < baseStart_1252694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252730 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1252730 : Nat := 118140960795 + 1252730 * 2 ^ 59
def prefixEnd_1252730 : Nat := 4983230072969 + 3 ^ 40 * 1252730 * 2
def baseEnd_1252730 : Nat := 285890053469772854139469

theorem tailTrace_1252730 : CollatzResearch.WordTrace tailWord_1252730 prefixEnd_1252730 285890053469772854139469 := by
  unfold tailWord_1252730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422704187895158523934911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30460544501053756063826429 11422704187895158523934911)
  ·
    refine ⟨17134056281842737785902367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11422704187895158523934911 17134056281842737785902367)
    ·
      refine ⟨25701084422764106678853551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17134056281842737785902367 25701084422764106678853551)
      ·
        refine ⟨38551626634146160018280327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25701084422764106678853551 38551626634146160018280327)
        ·
          refine ⟨57827439951219240027420491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38551626634146160018280327 57827439951219240027420491)
          ·
            refine ⟨86741159926828860041130737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57827439951219240027420491 86741159926828860041130737)
            ·
              refine ⟨65055869945121645030848053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86741159926828860041130737 65055869945121645030848053)
              ·
                refine ⟨6098987807355154221642005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65055869945121645030848053 6098987807355154221642005)
                ·
                  refine ⟨285890053469772854139469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6098987807355154221642005 285890053469772854139469)
                  ·
                    rfl

theorem cell21_1252730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1252730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252730 prefixEnd_1252730 := by exact prefixLift 1252730
  have htrace : WordTrace (prefixWord ++ tailWord_1252730) baseStart_1252730 baseEnd_1252730 := by
    simpa [prefixWord, tailWord_1252730, baseEnd_1252730] using wordTrace_append hprefix tailTrace_1252730
  have hstable : (prefixWord ++ tailWord_1252730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252730).length < 2 ^ (prefixWord ++ tailWord_1252730).sum := by decide
  have hdescent : baseEnd_1252730 < baseStart_1252730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252733 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1252733 : Nat := 118140960795 + 1252733 * 2 ^ 59
def prefixEnd_1252733 : Nat := 4983230072969 + 3 ^ 40 * 1252733 * 2
def baseEnd_1252733 : Nat := 285890738110645515589463

theorem tailTrace_1252733 : CollatzResearch.WordTrace tailWord_1252733 prefixEnd_1252733 285890738110645515589463 := by
  unfold tailWord_1252733
  simp only [CollatzResearch.WordTrace]
  refine ⟨45690926170569765608098853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30460617447046510405399235 45690926170569765608098853)
  ·
    refine ⟨8567048656981831051518535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45690926170569765608098853 8567048656981831051518535)
    ·
      refine ⟨12850572985472746577277803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567048656981831051518535 12850572985472746577277803)
      ·
        refine ⟨19275859478209119865916705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12850572985472746577277803 19275859478209119865916705)
        ·
          refine ⟨14456894608656839899437529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19275859478209119865916705 14456894608656839899437529)
          ·
            refine ⟨10842670956492629924578147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14456894608656839899437529 10842670956492629924578147)
            ·
              refine ⟨16264006434738944886867221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10842670956492629924578147 16264006434738944886867221)
              ·
                refine ⟨762375301628388041571901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16264006434738944886867221 762375301628388041571901)
                ·
                  refine ⟨285890738110645515589463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762375301628388041571901 285890738110645515589463)
                  ·
                    rfl

theorem cell21_1252733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1252733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252733 prefixEnd_1252733 := by exact prefixLift 1252733
  have htrace : WordTrace (prefixWord ++ tailWord_1252733) baseStart_1252733 baseEnd_1252733 := by
    simpa [prefixWord, tailWord_1252733, baseEnd_1252733] using wordTrace_append hprefix tailTrace_1252733
  have hstable : (prefixWord ++ tailWord_1252733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252733).length < 2 ^ (prefixWord ++ tailWord_1252733).sum := by decide
  have hdescent : baseEnd_1252733 < baseStart_1252733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252761 : List Nat := [1, 2, 1, 2, 1, 6, 1, 7]
def baseStart_1252761 : Nat := 118140960795 + 1252761 * 2 ^ 59
def prefixEnd_1252761 : Nat := 4983230072969 + 3 ^ 40 * 1252761 * 2
def baseEnd_1252761 : Nat := 95299042697374563040913

theorem tailTrace_1252761 : CollatzResearch.WordTrace tailWord_1252761 prefixEnd_1252761 95299042697374563040913 := by
  unfold tailWord_1252761
  simp only [CollatzResearch.WordTrace]
  refine ⟨45691947414468326390118137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30461298276312217593412091 45691947414468326390118137)
  ·
    refine ⟨34268960560851244792588603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45691947414468326390118137 34268960560851244792588603)
    ·
      refine ⟨51403440841276867188882905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34268960560851244792588603 51403440841276867188882905)
      ·
        refine ⟨38552580630957650391662179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51403440841276867188882905 38552580630957650391662179)
        ·
          refine ⟨57828870946436475587493269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38552580630957650391662179 57828870946436475587493269)
          ·
            refine ⟨2710728325614209793163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57828870946436475587493269 2710728325614209793163747)
            ·
              refine ⟨4066092488421314689745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710728325614209793163747 4066092488421314689745621)
              ·
                refine ⟨95299042697374563040913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4066092488421314689745621 95299042697374563040913)
                ·
                  rfl

theorem cell21_1252761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_1252761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252761 prefixEnd_1252761 := by exact prefixLift 1252761
  have htrace : WordTrace (prefixWord ++ tailWord_1252761) baseStart_1252761 baseEnd_1252761 := by
    simpa [prefixWord, tailWord_1252761, baseEnd_1252761] using wordTrace_append hprefix tailTrace_1252761
  have hstable : (prefixWord ++ tailWord_1252761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252761).length < 2 ^ (prefixWord ++ tailWord_1252761).sum := by decide
  have hdescent : baseEnd_1252761 < baseStart_1252761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252792 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_1252792 : Nat := 118140960795 + 1252792 * 2 ^ 59
def prefixEnd_1252792 : Nat := 4983230072969 + 3 ^ 40 * 1252792 * 2
def baseEnd_1252792 : Nat := 285904202714474524106009

theorem tailTrace_1252792 : CollatzResearch.WordTrace tailWord_1252792 prefixEnd_1252792 285904202714474524106009 := by
  unfold tailWord_1252792
  simp only [CollatzResearch.WordTrace]
  refine ⟨22846539038678009342248315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30462052051570679122997753 22846539038678009342248315)
  ·
    refine ⟨34269808558017014013372473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22846539038678009342248315 34269808558017014013372473)
    ·
      refine ⟨25702356418512760510029355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34269808558017014013372473 25702356418512760510029355)
      ·
        refine ⟨38553534627769140765044033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25702356418512760510029355 38553534627769140765044033)
        ·
          refine ⟨28915150970826855573783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38553534627769140765044033 28915150970826855573783025)
          ·
            refine ⟨21686363228120141680337269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28915150970826855573783025 21686363228120141680337269)
            ·
              refine ⟨2033096552636263282531619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21686363228120141680337269 2033096552636263282531619)
              ·
                refine ⟨3049644828954394923797429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033096552636263282531619 3049644828954394923797429)
                ·
                  refine ⟨285904202714474524106009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3049644828954394923797429 285904202714474524106009)
                  ·
                    rfl

theorem cell21_1252792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_1252792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252792 prefixEnd_1252792 := by exact prefixLift 1252792
  have htrace : WordTrace (prefixWord ++ tailWord_1252792) baseStart_1252792 baseEnd_1252792 := by
    simpa [prefixWord, tailWord_1252792, baseEnd_1252792] using wordTrace_append hprefix tailTrace_1252792
  have hstable : (prefixWord ++ tailWord_1252792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252792).length < 2 ^ (prefixWord ++ tailWord_1252792).sum := by decide
  have hdescent : baseEnd_1252792 < baseStart_1252792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252837 : List Nat := [1, 3, 1, 5, 1, 10]
def baseStart_1252837 : Nat := 118140960795 + 1252837 * 2 ^ 59
def prefixEnd_1252837 : Nat := 4983230072969 + 3 ^ 40 * 1252837 * 2
def baseEnd_1252837 : Nat := 10589424901020905402071

theorem tailTrace_1252837 : CollatzResearch.WordTrace tailWord_1252837 prefixEnd_1252837 10589424901020905402071 := by
  unfold tailWord_1252837
  simp only [CollatzResearch.WordTrace]
  refine ⟨45694719362192991369884765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30463146241461994246589843 45694719362192991369884765)
  ·
    refine ⟨17135519760822371763706787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45694719362192991369884765 17135519760822371763706787)
    ·
      refine ⟨25703279641233557645560181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17135519760822371763706787 25703279641233557645560181)
      ·
        refine ⟨2409682466365646029271267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25703279641233557645560181 2409682466365646029271267)
        ·
          refine ⟨3614523699548469043906901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409682466365646029271267 3614523699548469043906901)
          ·
            refine ⟨10589424901020905402071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3614523699548469043906901 10589424901020905402071)
            ·
              rfl

theorem cell21_1252837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 10].length) (baseStart_1252837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252837 prefixEnd_1252837 := by exact prefixLift 1252837
  have htrace : WordTrace (prefixWord ++ tailWord_1252837) baseStart_1252837 baseEnd_1252837 := by
    simpa [prefixWord, tailWord_1252837, baseEnd_1252837] using wordTrace_append hprefix tailTrace_1252837
  have hstable : (prefixWord ++ tailWord_1252837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252837).length < 2 ^ (prefixWord ++ tailWord_1252837).sum := by decide
  have hdescent : baseEnd_1252837 < baseStart_1252837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252854 : List Nat := [5, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1252854 : Nat := 118140960795 + 1252854 * 2 ^ 59
def prefixEnd_1252854 : Nat := 4983230072969 + 3 ^ 40 * 1252854 * 2
def baseEnd_1252854 : Nat := 95306117319725398024183

theorem tailTrace_1252854 : CollatzResearch.WordTrace tailWord_1252854 prefixEnd_1252854 95306117319725398024183 := by
  unfold tailWord_1252854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855958712695712704578351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30463559602087602182169077 2855958712695712704578351)
  ·
    refine ⟨4283938069043569056867527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2855958712695712704578351 4283938069043569056867527)
    ·
      refine ⟨6425907103565353585301291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283938069043569056867527 6425907103565353585301291)
      ·
        refine ⟨9638860655348030377951937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425907103565353585301291 9638860655348030377951937)
        ·
          refine ⟨7229145491511022783463953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9638860655348030377951937 7229145491511022783463953)
          ·
            refine ⟨5421859118633267087597965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229145491511022783463953 5421859118633267087597965)
            ·
              refine ⟨2033197169487475157849237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5421859118633267087597965 2033197169487475157849237)
              ·
                refine ⟨95306117319725398024183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2033197169487475157849237 95306117319725398024183)
                ·
                  rfl

theorem cell21_1252854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1252854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252854 prefixEnd_1252854 := by exact prefixLift 1252854
  have htrace : WordTrace (prefixWord ++ tailWord_1252854) baseStart_1252854 baseEnd_1252854 := by
    simpa [prefixWord, tailWord_1252854, baseEnd_1252854] using wordTrace_append hprefix tailTrace_1252854
  have hstable : (prefixWord ++ tailWord_1252854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252854).length < 2 ^ (prefixWord ++ tailWord_1252854).sum := by decide
  have hdescent : baseEnd_1252854 < baseStart_1252854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252885 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1252885 : Nat := 118140960795 + 1252885 * 2 ^ 59
def prefixEnd_1252885 : Nat := 4983230072969 + 3 ^ 40 * 1252885 * 2
def baseEnd_1252885 : Nat := 285925426581527029055819

theorem tailTrace_1252885 : CollatzResearch.WordTrace tailWord_1252885 prefixEnd_1252885 285925426581527029055819 := by
  unfold tailWord_1252885
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696470066019095567632109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30464313377346063711754739 45696470066019095567632109)
  ·
    refine ⟨17136176274757160837862041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45696470066019095567632109 17136176274757160837862041)
    ·
      refine ⟨12852132206067870628396531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17136176274757160837862041 12852132206067870628396531)
      ·
        refine ⟨19278198309101805942594797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12852132206067870628396531 19278198309101805942594797)
        ·
          refine ⟨7229324365913177228473049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19278198309101805942594797 7229324365913177228473049)
          ·
            refine ⟨5421993274434882921354787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229324365913177228473049 5421993274434882921354787)
            ·
              refine ⟨8132989911652324382032181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421993274434882921354787 8132989911652324382032181)
              ·
                refine ⟨762467804217405410815517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8132989911652324382032181 762467804217405410815517)
                ·
                  refine ⟨285925426581527029055819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762467804217405410815517 285925426581527029055819)
                  ·
                    rfl

theorem cell21_1252885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1252885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252885 prefixEnd_1252885 := by exact prefixLift 1252885
  have htrace : WordTrace (prefixWord ++ tailWord_1252885) baseStart_1252885 baseEnd_1252885 := by
    simpa [prefixWord, tailWord_1252885, baseEnd_1252885] using wordTrace_append hprefix tailTrace_1252885
  have hstable : (prefixWord ++ tailWord_1252885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252885).length < 2 ^ (prefixWord ++ tailWord_1252885).sum := by decide
  have hdescent : baseEnd_1252885 < baseStart_1252885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252899 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_1252899 : Nat := 118140960795 + 1252899 * 2 ^ 59
def prefixEnd_1252899 : Nat := 4983230072969 + 3 ^ 40 * 1252899 * 2
def baseEnd_1252899 : Nat := 285928621572266115822457

theorem tailTrace_1252899 : CollatzResearch.WordTrace tailWord_1252899 prefixEnd_1252899 285928621572266115822457 := by
  unfold tailWord_1252899
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696980687968375958641751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30464653791978917305761167 45696980687968375958641751)
  ·
    refine ⟨68545471031952563937962627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45696980687968375958641751 68545471031952563937962627)
    ·
      refine ⟨102818206547928845906943941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68545471031952563937962627 102818206547928845906943941)
      ·
        refine ⟨19278413727736658607551989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102818206547928845906943941 19278413727736658607551989)
        ·
          refine ⟨1807351286975311744457999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19278413727736658607551989 1807351286975311744457999)
          ·
            refine ⟨2711026930462967616686999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807351286975311744457999 2711026930462967616686999)
            ·
              refine ⟨4066540395694451425030499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711026930462967616686999 4066540395694451425030499)
              ·
                refine ⟨6099810593541677137545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066540395694451425030499 6099810593541677137545749)
                ·
                  refine ⟨285928621572266115822457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6099810593541677137545749 285928621572266115822457)
                  ·
                    rfl

theorem cell21_1252899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_1252899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252899 prefixEnd_1252899 := by exact prefixLift 1252899
  have htrace : WordTrace (prefixWord ++ tailWord_1252899) baseStart_1252899 baseEnd_1252899 := by
    simpa [prefixWord, tailWord_1252899, baseEnd_1252899] using wordTrace_append hprefix tailTrace_1252899
  have hstable : (prefixWord ++ tailWord_1252899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252899).length < 2 ^ (prefixWord ++ tailWord_1252899).sum := by decide
  have hdescent : baseEnd_1252899 < baseStart_1252899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252989 : List Nat := [1, 4, 1, 1, 4, 1, 2, 7]
def baseStart_1252989 : Nat := 118140960795 + 1252989 * 2 ^ 59
def prefixEnd_1252989 : Nat := 4983230072969 + 3 ^ 40 * 1252989 * 2
def baseEnd_1252989 : Nat := 95316386932815319774091

theorem tailTrace_1252989 : CollatzResearch.WordTrace tailWord_1252989 prefixEnd_1252989 95316386932815319774091 := by
  unfold tailWord_1252989
  simp only [CollatzResearch.WordTrace]
  refine ⟨45700263257642321329418021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30466842171761547552945347 45700263257642321329418021)
  ·
    refine ⟨8568799360807935249265879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45700263257642321329418021 8568799360807935249265879)
    ·
      refine ⟨12853199041211902873898819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8568799360807935249265879 12853199041211902873898819)
      ·
        refine ⟨19279798561817854310848229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12853199041211902873898819 19279798561817854310848229)
        ·
          refine ⟨3614962230340847683284043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19279798561817854310848229 3614962230340847683284043)
          ·
            refine ⟨5422443345511271524926065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614962230340847683284043 5422443345511271524926065)
            ·
              refine ⟨4066832509133453643694549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5422443345511271524926065 4066832509133453643694549)
              ·
                refine ⟨95316386932815319774091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4066832509133453643694549 95316386932815319774091)
                ·
                  rfl

theorem cell21_1252989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_1252989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1252989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1252989 prefixEnd_1252989 := by exact prefixLift 1252989
  have htrace : WordTrace (prefixWord ++ tailWord_1252989) baseStart_1252989 baseEnd_1252989 := by
    simpa [prefixWord, tailWord_1252989, baseEnd_1252989] using wordTrace_append hprefix tailTrace_1252989
  have hstable : (prefixWord ++ tailWord_1252989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252989).length < 2 ^ (prefixWord ++ tailWord_1252989).sum := by decide
  have hdescent : baseEnd_1252989 < baseStart_1252989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253012 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1253012 : Nat := 118140960795 + 1253012 * 2 ^ 59
def prefixEnd_1253012 : Nat := 4983230072969 + 3 ^ 40 * 1253012 * 2
def baseEnd_1253012 : Nat := 285954409711803030438893

theorem tailTrace_1253012 : CollatzResearch.WordTrace tailWord_1253012 prefixEnd_1253012 285954409711803030438893 := by
  unfold tailWord_1253012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850551068279498128752645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30467401424372664171670193 22850551068279498128752645)
  ·
    refine ⟨4284478325302405899141121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22850551068279498128752645 4284478325302405899141121)
    ·
      refine ⟨3213358743976804424355841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4284478325302405899141121 3213358743976804424355841)
      ·
        refine ⟨2410019057982603318266881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3213358743976804424355841 2410019057982603318266881)
        ·
          refine ⟨1807514293486952488700161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410019057982603318266881 1807514293486952488700161)
          ·
            refine ⟨1355635720115214366525121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807514293486952488700161 1355635720115214366525121)
            ·
              refine ⟨1016726790086410774893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355635720115214366525121 1016726790086410774893841)
              ·
                refine ⟨762545092564808081170381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016726790086410774893841 762545092564808081170381)
                ·
                  refine ⟨285954409711803030438893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762545092564808081170381 285954409711803030438893)
                  ·
                    rfl

theorem cell21_1253012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1253012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253012 prefixEnd_1253012 := by exact prefixLift 1253012
  have htrace : WordTrace (prefixWord ++ tailWord_1253012) baseStart_1253012 baseEnd_1253012 := by
    simpa [prefixWord, tailWord_1253012, baseEnd_1253012] using wordTrace_append hprefix tailTrace_1253012
  have hstable : (prefixWord ++ tailWord_1253012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253012).length < 2 ^ (prefixWord ++ tailWord_1253012).sum := by decide
  have hdescent : baseEnd_1253012 < baseStart_1253012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253023 : List Nat := [1, 1, 2, 7, 1, 2, 1, 6]
def baseStart_1253023 : Nat := 118140960795 + 1253023 * 2 ^ 59
def prefixEnd_1253023 : Nat := 4983230072969 + 3 ^ 40 * 1253023 * 2
def baseEnd_1253023 : Nat := 95318973353889818585179

theorem tailTrace_1253023 : CollatzResearch.WordTrace tailWord_1253023 prefixEnd_1253023 95318973353889818585179 := by
  unfold tailWord_1253023
  simp only [CollatzResearch.WordTrace]
  refine ⟨45701503339519145136155723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30467668893012763424103815 45701503339519145136155723)
  ·
    refine ⟨68552255009278717704233585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45701503339519145136155723 68552255009278717704233585)
    ·
      refine ⟨51414191256959038278175189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68552255009278717704233585 51414191256959038278175189)
      ·
        refine ⟨1205020107584977459644731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 51414191256959038278175189 1205020107584977459644731)
        ·
          refine ⟨1807530161377466189467097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205020107584977459644731 1807530161377466189467097)
          ·
            refine ⟨1355647621033099642100323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807530161377466189467097 1355647621033099642100323)
            ·
              refine ⟨2033471431549649463150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355647621033099642100323 2033471431549649463150485)
              ·
                refine ⟨95318973353889818585179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2033471431549649463150485 95318973353889818585179)
                ·
                  rfl

theorem cell21_1253023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_1253023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253023 prefixEnd_1253023 := by exact prefixLift 1253023
  have htrace : WordTrace (prefixWord ++ tailWord_1253023) baseStart_1253023 baseEnd_1253023 := by
    simpa [prefixWord, tailWord_1253023, baseEnd_1253023] using wordTrace_append hprefix tailTrace_1253023
  have hstable : (prefixWord ++ tailWord_1253023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253023).length < 2 ^ (prefixWord ++ tailWord_1253023).sum := by decide
  have hdescent : baseEnd_1253023 < baseStart_1253023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253048 : List Nat := [2, 1, 2, 1, 2, 1, 1, 11]
def baseStart_1253048 : Nat := 118140960795 + 1253048 * 2 ^ 59
def prefixEnd_1253048 : Nat := 4983230072969 + 3 ^ 40 * 1253048 * 2
def baseEnd_1253048 : Nat := 95320875134091655946273

theorem tailTrace_1253048 : CollatzResearch.WordTrace tailWord_1253048 prefixEnd_1253048 95320875134091655946273 := by
  unfold tailWord_1253048
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851207582214287202907899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30468276776285716270543865 22851207582214287202907899)
  ·
    refine ⟨34276811373321430804361849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22851207582214287202907899 34276811373321430804361849)
    ·
      refine ⟨25707608529991073103271387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34276811373321430804361849 25707608529991073103271387)
      ·
        refine ⟨38561412794986609654907081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25707608529991073103271387 38561412794986609654907081)
        ·
          refine ⟨28921059596239957241180311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38561412794986609654907081 28921059596239957241180311)
          ·
            refine ⟨43381589394359935861770467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28921059596239957241180311 43381589394359935861770467)
            ·
              refine ⟨65072384091539903792655701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43381589394359935861770467 65072384091539903792655701)
              ·
                refine ⟨95320875134091655946273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65072384091539903792655701 95320875134091655946273)
                ·
                  rfl

theorem cell21_1253048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_1253048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253048 prefixEnd_1253048 := by exact prefixLift 1253048
  have htrace : WordTrace (prefixWord ++ tailWord_1253048) baseStart_1253048 baseEnd_1253048 := by
    simpa [prefixWord, tailWord_1253048, baseEnd_1253048] using wordTrace_append hprefix tailTrace_1253048
  have hstable : (prefixWord ++ tailWord_1253048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253048).length < 2 ^ (prefixWord ++ tailWord_1253048).sum := by decide
  have hdescent : baseEnd_1253048 < baseStart_1253048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253054 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1253054 : Nat := 118140960795 + 1253054 * 2 ^ 59
def prefixEnd_1253054 : Nat := 4983230072969 + 3 ^ 40 * 1253054 * 2
def baseEnd_1253054 : Nat := 285963994684020290738807

theorem tailTrace_1253054 : CollatzResearch.WordTrace tailWord_1253054 prefixEnd_1253054 285963994684020290738807 := by
  unfold tailWord_1253054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712829250300854678816777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30468422668271224953689477 5712829250300854678816777)
  ·
    refine ⟨4284621937725641009112583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5712829250300854678816777 4284621937725641009112583)
    ·
      refine ⟨6426932906588461513668875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284621937725641009112583 6426932906588461513668875)
      ·
        refine ⟨9640399359882692270503313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426932906588461513668875 9640399359882692270503313)
        ·
          refine ⟨7230299519912019202877485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640399359882692270503313 7230299519912019202877485)
          ·
            refine ⟨2711362319967007201079057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7230299519912019202877485 2711362319967007201079057)
            ·
              refine ⟨2033521739975255400809293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711362319967007201079057 2033521739975255400809293)
              ·
                refine ⟨762570652490720775303485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2033521739975255400809293 762570652490720775303485)
                ·
                  refine ⟨285963994684020290738807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762570652490720775303485 285963994684020290738807)
                  ·
                    rfl

theorem cell21_1253054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1253054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253054 prefixEnd_1253054 := by exact prefixLift 1253054
  have htrace : WordTrace (prefixWord ++ tailWord_1253054) baseStart_1253054 baseEnd_1253054 := by
    simpa [prefixWord, tailWord_1253054, baseEnd_1253054] using wordTrace_append hprefix tailTrace_1253054
  have hstable : (prefixWord ++ tailWord_1253054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253054).length < 2 ^ (prefixWord ++ tailWord_1253054).sum := by decide
  have hdescent : baseEnd_1253054 < baseStart_1253054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253096 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_1253096 : Nat := 118140960795 + 1253096 * 2 ^ 59
def prefixEnd_1253096 : Nat := 4983230072969 + 3 ^ 40 * 1253096 * 2
def baseEnd_1253096 : Nat := 285973579656237551038721

theorem tailTrace_1253096 : CollatzResearch.WordTrace tailWord_1253096 prefixEnd_1253096 285973579656237551038721 := by
  unfold tailWord_1253096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22852082934127339301781571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30469443912169785735708761 22852082934127339301781571)
  ·
    refine ⟨34278124401191008952672357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22852082934127339301781571 34278124401191008952672357)
    ·
      refine ⟨6427148325223314178626067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34278124401191008952672357 6427148325223314178626067)
      ·
        refine ⟨9640722487834971267939101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427148325223314178626067 9640722487834971267939101)
        ·
          refine ⟨3615270932938114225477163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9640722487834971267939101 3615270932938114225477163)
          ·
            refine ⟨5422906399407171338215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615270932938114225477163 5422906399407171338215745)
            ·
              refine ⟨4067179799555378503661809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5422906399407171338215745 4067179799555378503661809)
              ·
                refine ⟨3050384849666533877746357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067179799555378503661809 3050384849666533877746357)
                ·
                  refine ⟨285973579656237551038721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050384849666533877746357 285973579656237551038721)
                  ·
                    rfl

theorem cell21_1253096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_1253096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253096 prefixEnd_1253096 := by exact prefixLift 1253096
  have htrace : WordTrace (prefixWord ++ tailWord_1253096) baseStart_1253096 baseEnd_1253096 := by
    simpa [prefixWord, tailWord_1253096, baseEnd_1253096] using wordTrace_append hprefix tailTrace_1253096
  have hstable : (prefixWord ++ tailWord_1253096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253096).length < 2 ^ (prefixWord ++ tailWord_1253096).sum := by decide
  have hdescent : baseEnd_1253096 < baseStart_1253096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253130 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1253130 : Nat := 118140960795 + 1253130 * 2 ^ 59
def prefixEnd_1253130 : Nat := 4983230072969 + 3 ^ 40 * 1253130 * 2
def baseEnd_1253130 : Nat := 285981338919461047471985

theorem tailTrace_1253130 : CollatzResearch.WordTrace tailWord_1253130 prefixEnd_1253130 285981338919461047471985 := by
  unfold tailWord_1253130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11426351487532875602575211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30470270633421001606867229 11426351487532875602575211)
  ·
    refine ⟨17139527231299313403862817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11426351487532875602575211 17139527231299313403862817)
    ·
      refine ⟨12854645423474485052897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17139527231299313403862817 12854645423474485052897113)
      ·
        refine ⟨9640984067605863789672835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12854645423474485052897113 9640984067605863789672835)
        ·
          refine ⟨14461476101408795684509253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640984067605863789672835 14461476101408795684509253)
          ·
            refine ⟨2711526769014149190845485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14461476101408795684509253 2711526769014149190845485)
            ·
              refine ⟨1016822538380305946567057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2711526769014149190845485 1016822538380305946567057)
              ·
                refine ⟨762616903785229459925293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016822538380305946567057 762616903785229459925293)
                ·
                  refine ⟨285981338919461047471985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762616903785229459925293 285981338919461047471985)
                  ·
                    rfl

theorem cell21_1253130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1253130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253130 prefixEnd_1253130 := by exact prefixLift 1253130
  have htrace : WordTrace (prefixWord ++ tailWord_1253130) baseStart_1253130 baseEnd_1253130 := by
    simpa [prefixWord, tailWord_1253130, baseEnd_1253130] using wordTrace_append hprefix tailTrace_1253130
  have hstable : (prefixWord ++ tailWord_1253130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253130).length < 2 ^ (prefixWord ++ tailWord_1253130).sum := by decide
  have hdescent : baseEnd_1253130 < baseStart_1253130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253133 : List Nat := [1, 7, 2, 1, 1, 1, 2, 6]
def baseStart_1253133 : Nat := 118140960795 + 1253133 * 2 ^ 59
def prefixEnd_1253133 : Nat := 4983230072969 + 3 ^ 40 * 1253133 * 2
def baseEnd_1253133 : Nat := 95327341186777902973993

theorem tailTrace_1253133 : CollatzResearch.WordTrace tailWord_1253133 prefixEnd_1253133 95327341186777902973993 := by
  unfold tailWord_1253133
  simp only [CollatzResearch.WordTrace]
  refine ⟨45705515369120633922660053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30470343579413755948440035 45705515369120633922660053)
  ·
    refine ⟨1071223016463764857562345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45705515369120633922660053 1071223016463764857562345)
    ·
      refine ⟨803417262347823643171759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071223016463764857562345 803417262347823643171759)
      ·
        refine ⟨1205125893521735464757639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803417262347823643171759 1205125893521735464757639)
        ·
          refine ⟨1807688840282603197136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205125893521735464757639 1807688840282603197136459)
          ·
            refine ⟨2711533260423904795704689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807688840282603197136459 2711533260423904795704689)
            ·
              refine ⟨2033649945317928596778517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711533260423904795704689 2033649945317928596778517)
              ·
                refine ⟨95327341186777902973993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2033649945317928596778517 95327341186777902973993)
                ·
                  rfl

theorem cell21_1253133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].length) (baseStart_1253133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253133 prefixEnd_1253133 := by exact prefixLift 1253133
  have htrace : WordTrace (prefixWord ++ tailWord_1253133) baseStart_1253133 baseEnd_1253133 := by
    simpa [prefixWord, tailWord_1253133, baseEnd_1253133] using wordTrace_append hprefix tailTrace_1253133
  have hstable : (prefixWord ++ tailWord_1253133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253133).length < 2 ^ (prefixWord ++ tailWord_1253133).sum := by decide
  have hdescent : baseEnd_1253133 < baseStart_1253133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253141 : List Nat := [1, 3, 2, 1, 2, 4, 2, 6]
def baseStart_1253141 : Nat := 118140960795 + 1253141 * 2 ^ 59
def prefixEnd_1253141 : Nat := 4983230072969 + 3 ^ 40 * 1253141 * 2
def baseEnd_1253141 : Nat := 95327949756442490929543

theorem tailTrace_1253141 : CollatzResearch.WordTrace tailWord_1253141 prefixEnd_1253141 95327949756442490929543 := by
  unfold tailWord_1253141
  simp only [CollatzResearch.WordTrace]
  refine ⟨45705807153091651288951277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30470538102061100859300851 45705807153091651288951277)
  ·
    refine ⟨17139677682409369233356729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45705807153091651288951277 17139677682409369233356729)
    ·
      refine ⟨12854758261807026925017547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17139677682409369233356729 12854758261807026925017547)
      ·
        refine ⟨19282137392710540387526321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854758261807026925017547 19282137392710540387526321)
        ·
          refine ⟨14461603044532905290644741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19282137392710540387526321 14461603044532905290644741)
          ·
            refine ⟨2711550570849919741995889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14461603044532905290644741 2711550570849919741995889)
            ·
              refine ⟨2033662928137439806496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711550570849919741995889 2033662928137439806496917)
              ·
                refine ⟨95327949756442490929543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2033662928137439806496917 95327949756442490929543)
                ·
                  rfl

theorem cell21_1253141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_1253141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253141 prefixEnd_1253141 := by exact prefixLift 1253141
  have htrace : WordTrace (prefixWord ++ tailWord_1253141) baseStart_1253141 baseEnd_1253141 := by
    simpa [prefixWord, tailWord_1253141, baseEnd_1253141] using wordTrace_append hprefix tailTrace_1253141
  have hstable : (prefixWord ++ tailWord_1253141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253141).length < 2 ^ (prefixWord ++ tailWord_1253141).sum := by decide
  have hdescent : baseEnd_1253141 < baseStart_1253141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253155 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_1253155 : Nat := 118140960795 + 1253155 * 2 ^ 59
def prefixEnd_1253155 : Nat := 4983230072969 + 3 ^ 40 * 1253155 * 2
def baseEnd_1253155 : Nat := 285987044260066559555267

theorem tailTrace_1253155 : CollatzResearch.WordTrace tailWord_1253155 prefixEnd_1253155 285987044260066559555267 := by
  unfold tailWord_1253155
  simp only [CollatzResearch.WordTrace]
  refine ⟨45706317775040931679960919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30470878516693954453307279 45706317775040931679960919)
  ·
    refine ⟨68559476662561397519941379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45706317775040931679960919 68559476662561397519941379)
    ·
      refine ⟨102839214993842096279912069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68559476662561397519941379 102839214993842096279912069)
      ·
        refine ⟨19282352811345393052483513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102839214993842096279912069 19282352811345393052483513)
        ·
          refine ⟨14461764608509044789362635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19282352811345393052483513 14461764608509044789362635)
          ·
            refine ⟨21692646912763567184043953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14461764608509044789362635 21692646912763567184043953)
            ·
              refine ⟨16269485184572675388032965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21692646912763567184043953 16269485184572675388032965)
              ·
                refine ⟨3050528472107376635256181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16269485184572675388032965 3050528472107376635256181)
                ·
                  refine ⟨285987044260066559555267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050528472107376635256181 285987044260066559555267)
                  ·
                    rfl

theorem cell21_1253155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_1253155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253155 prefixEnd_1253155 := by exact prefixLift 1253155
  have htrace : WordTrace (prefixWord ++ tailWord_1253155) baseStart_1253155 baseEnd_1253155 := by
    simpa [prefixWord, tailWord_1253155, baseEnd_1253155] using wordTrace_append hprefix tailTrace_1253155
  have hstable : (prefixWord ++ tailWord_1253155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253155).length < 2 ^ (prefixWord ++ tailWord_1253155).sum := by decide
  have hdescent : baseEnd_1253155 < baseStart_1253155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253217 : List Nat := [1, 2, 3, 1, 1, 1, 7, 5]
def baseStart_1253217 : Nat := 118140960795 + 1253217 * 2 ^ 59
def prefixEnd_1253217 : Nat := 4983230072969 + 3 ^ 40 * 1253217 * 2
def baseEnd_1253217 : Nat := 95333731168256076507269

theorem tailTrace_1253217 : CollatzResearch.WordTrace tailWord_1253217 prefixEnd_1253217 95333731168256076507269 := by
  unfold tailWord_1253217
  simp only [CollatzResearch.WordTrace]
  refine ⟨45708579100816316268717905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30472386067210877512478603 45708579100816316268717905)
  ·
    refine ⟨34281434325612237201538429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45708579100816316268717905 34281434325612237201538429)
    ·
      refine ⟨12855537872104588950576911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34281434325612237201538429 12855537872104588950576911)
      ·
        refine ⟨19283306808156883425865367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12855537872104588950576911 19283306808156883425865367)
        ·
          refine ⟨28924960212235325138798051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19283306808156883425865367 28924960212235325138798051)
          ·
            refine ⟨43387440318352987708197077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28924960212235325138798051 43387440318352987708197077)
            ·
              refine ⟨1016893132461398149410869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43387440318352987708197077 1016893132461398149410869)
              ·
                refine ⟨95333731168256076507269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016893132461398149410869 95333731168256076507269)
                ·
                  rfl

theorem cell21_1253217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].length) (baseStart_1253217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253217 prefixEnd_1253217 := by exact prefixLift 1253217
  have htrace : WordTrace (prefixWord ++ tailWord_1253217) baseStart_1253217 baseEnd_1253217 := by
    simpa [prefixWord, tailWord_1253217, baseEnd_1253217] using wordTrace_append hprefix tailTrace_1253217
  have hstable : (prefixWord ++ tailWord_1253217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253217).length < 2 ^ (prefixWord ++ tailWord_1253217).sum := by decide
  have hdescent : baseEnd_1253217 < baseStart_1253217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253248 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_1253248 : Nat := 118140960795 + 1253248 * 2 ^ 59
def prefixEnd_1253248 : Nat := 4983230072969 + 3 ^ 40 * 1253248 * 2
def baseEnd_1253248 : Nat := 286008268127119064505077

theorem tailTrace_1253248 : CollatzResearch.WordTrace tailWord_1253248 prefixEnd_1253248 286008268127119064505077 := by
  unfold tailWord_1253248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854854881852004281548199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30473139842469339042064265 22854854881852004281548199)
  ·
    refine ⟨34282282322778006422322299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22854854881852004281548199 34282282322778006422322299)
    ·
      refine ⟨51423423484167009633483449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34282282322778006422322299 51423423484167009633483449)
      ·
        refine ⟨38567567613125257225112587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51423423484167009633483449 38567567613125257225112587)
        ·
          refine ⟨57851351419687885837668881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38567567613125257225112587 57851351419687885837668881)
          ·
            refine ⟨43388513564765914378251661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57851351419687885837668881 43388513564765914378251661)
            ·
              refine ⟨16270692586787217891844373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43388513564765914378251661 16270692586787217891844373)
              ·
                refine ⟨762688715005650838680205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16270692586787217891844373 762688715005650838680205)
                ·
                  refine ⟨286008268127119064505077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762688715005650838680205 286008268127119064505077)
                  ·
                    rfl

theorem cell21_1253248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_1253248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253248 prefixEnd_1253248 := by exact prefixLift 1253248
  have htrace : WordTrace (prefixWord ++ tailWord_1253248) baseStart_1253248 baseEnd_1253248 := by
    simpa [prefixWord, tailWord_1253248, baseEnd_1253248] using wordTrace_append hprefix tailTrace_1253248
  have hstable : (prefixWord ++ tailWord_1253248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253248).length < 2 ^ (prefixWord ++ tailWord_1253248).sum := by decide
  have hdescent : baseEnd_1253248 < baseStart_1253248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253358 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1253358 : Nat := 118140960795 + 1253358 * 2 ^ 59
def prefixEnd_1253358 : Nat := 4983230072969 + 3 ^ 40 * 1253358 * 2
def baseEnd_1253358 : Nat := 286033371625783317671519

theorem tailTrace_1253358 : CollatzResearch.WordTrace tailWord_1253358 prefixEnd_1253358 286033371625783317671519 := by
  unfold tailWord_1253358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5714215224163187168700091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30475814528870331566400485 5714215224163187168700091)
  ·
    refine ⟨8571322836244780753050137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5714215224163187168700091 8571322836244780753050137)
    ·
      refine ⟨6428492127183585564787603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8571322836244780753050137 6428492127183585564787603)
      ·
        refine ⟨9642738190775378347181405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428492127183585564787603 9642738190775378347181405)
        ·
          refine ⟨3616026821540766880193027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9642738190775378347181405 3616026821540766880193027)
          ·
            refine ⟨5424040232311150320289541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616026821540766880193027 5424040232311150320289541)
            ·
              refine ⟨1017007543558340685054289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5424040232311150320289541 1017007543558340685054289)
              ·
                refine ⟨762755657668755513790717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017007543558340685054289 762755657668755513790717)
                ·
                  refine ⟨286033371625783317671519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762755657668755513790717 286033371625783317671519)
                  ·
                    rfl

theorem cell21_1253358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1253358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253358 prefixEnd_1253358 := by exact prefixLift 1253358
  have htrace : WordTrace (prefixWord ++ tailWord_1253358) baseStart_1253358 baseEnd_1253358 := by
    simpa [prefixWord, tailWord_1253358, baseEnd_1253358] using wordTrace_append hprefix tailTrace_1253358
  have hstable : (prefixWord ++ tailWord_1253358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253358).length < 2 ^ (prefixWord ++ tailWord_1253358).sum := by decide
  have hdescent : baseEnd_1253358 < baseStart_1253358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253369 : List Nat := [1, 2, 1, 3, 1, 6, 1, 6]
def baseStart_1253369 : Nat := 118140960795 + 1253369 * 2 ^ 59
def prefixEnd_1253369 : Nat := 4983230072969 + 3 ^ 40 * 1253369 * 2
def baseEnd_1253369 : Nat := 95345293991883247662721

theorem tailTrace_1253369 : CollatzResearch.WordTrace tailWord_1253369 prefixEnd_1253369 95345293991883247662721 := by
  unfold tailWord_1253369
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714122996265646228251161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30476081997510430818834107 45714122996265646228251161)
  ·
    refine ⟨34285592247199234671188371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45714122996265646228251161 34285592247199234671188371)
    ·
      refine ⟨51428388370798852006782557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34285592247199234671188371 51428388370798852006782557)
      ·
        refine ⟨19285645639049569502543459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51428388370798852006782557 19285645639049569502543459)
        ·
          refine ⟨28928468458574354253815189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19285645639049569502543459 28928468458574354253815189)
          ·
            refine ⟨1356021958995672855647587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28928468458574354253815189 1356021958995672855647587)
            ·
              refine ⟨2034032938493509283471381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356021958995672855647587 2034032938493509283471381)
              ·
                refine ⟨95345293991883247662721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034032938493509283471381 95345293991883247662721)
                ·
                  rfl

theorem cell21_1253369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_1253369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253369 prefixEnd_1253369 := by exact prefixLift 1253369
  have htrace : WordTrace (prefixWord ++ tailWord_1253369) baseStart_1253369 baseEnd_1253369 := by
    simpa [prefixWord, tailWord_1253369, baseEnd_1253369] using wordTrace_append hprefix tailTrace_1253369
  have hstable : (prefixWord ++ tailWord_1253369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253369).length < 2 ^ (prefixWord ++ tailWord_1253369).sum := by decide
  have hdescent : baseEnd_1253369 < baseStart_1253369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253383 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_1253383 : Nat := 118140960795 + 1253383 * 2 ^ 59
def prefixEnd_1253383 : Nat := 4983230072969 + 3 ^ 40 * 1253383 * 2
def baseEnd_1253383 : Nat := 286039076966388829754801

theorem tailTrace_1253383 : CollatzResearch.WordTrace tailWord_1253383 prefixEnd_1253383 286039076966388829754801 := by
  unfold tailWord_1253383
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714633618214926619260803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30476422412143284412840535 45714633618214926619260803)
  ·
    refine ⟨68571950427322389928891205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45714633618214926619260803 68571950427322389928891205)
    ·
      refine ⟨12857240705122948111667101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68571950427322389928891205 12857240705122948111667101)
      ·
        refine ⟨4821465264421105541875163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12857240705122948111667101 4821465264421105541875163)
        ·
          refine ⟨7232197896631658312812745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821465264421105541875163 7232197896631658312812745)
          ·
            refine ⟨5424148422473743734609559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232197896631658312812745 5424148422473743734609559)
            ·
              refine ⟨8136222633710615601914339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424148422473743734609559 8136222633710615601914339)
              ·
                refine ⟨12204333950565923402871509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136222633710615601914339 12204333950565923402871509)
                ·
                  refine ⟨286039076966388829754801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12204333950565923402871509 286039076966388829754801)
                  ·
                    rfl

theorem cell21_1253383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_1253383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253383 prefixEnd_1253383 := by exact prefixLift 1253383
  have htrace : WordTrace (prefixWord ++ tailWord_1253383) baseStart_1253383 baseEnd_1253383 := by
    simpa [prefixWord, tailWord_1253383, baseEnd_1253383] using wordTrace_append hprefix tailTrace_1253383
  have hstable : (prefixWord ++ tailWord_1253383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253383).length < 2 ^ (prefixWord ++ tailWord_1253383).sum := by decide
  have hdescent : baseEnd_1253383 < baseStart_1253383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253386 : List Nat := [3, 1, 2, 2, 4, 1, 3, 5]
def baseStart_1253386 : Nat := 118140960795 + 1253386 * 2 ^ 59
def prefixEnd_1253386 : Nat := 4983230072969 + 3 ^ 40 * 1253386 * 2
def baseEnd_1253386 : Nat := 95346587202420497068265

theorem tailTrace_1253386 : CollatzResearch.WordTrace tailWord_1253386 prefixEnd_1253386 95346587202420497068265 := by
  unfold tailWord_1253386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428685759301014532905003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30476495358136038754413341 11428685759301014532905003)
  ·
    refine ⟨17143028638951521799357505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11428685759301014532905003 17143028638951521799357505)
    ·
      refine ⟨12857271479213641349518129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17143028638951521799357505 12857271479213641349518129)
      ·
        refine ⟨9642953609410231012138597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12857271479213641349518129 9642953609410231012138597)
        ·
          refine ⟨1808053801764418314775987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9642953609410231012138597 1808053801764418314775987)
          ·
            refine ⟨2712080702646627472163981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808053801764418314775987 2712080702646627472163981)
            ·
              refine ⟨1017030263492485302061493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2712080702646627472163981 1017030263492485302061493)
              ·
                refine ⟨95346587202420497068265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1017030263492485302061493 95346587202420497068265)
                ·
                  rfl

theorem cell21_1253386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_1253386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253386 prefixEnd_1253386 := by exact prefixLift 1253386
  have htrace : WordTrace (prefixWord ++ tailWord_1253386) baseStart_1253386 baseEnd_1253386 := by
    simpa [prefixWord, tailWord_1253386, baseEnd_1253386] using wordTrace_append hprefix tailTrace_1253386
  have hstable : (prefixWord ++ tailWord_1253386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253386).length < 2 ^ (prefixWord ++ tailWord_1253386).sum := by decide
  have hdescent : baseEnd_1253386 < baseStart_1253386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253462 : List Nat := [5, 2, 2, 1, 1, 1, 9]
def baseStart_1253462 : Nat := 118140960795 + 1253462 * 2 ^ 59
def prefixEnd_1253462 : Nat := 4983230072969 + 3 ^ 40 * 1253462 * 2
def baseEnd_1253462 : Nat := 31784122871411360881997

theorem tailTrace_1253462 : CollatzResearch.WordTrace tailWord_1253462 prefixEnd_1253462 31784122871411360881997 := by
  unfold tailWord_1253462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857344686558045194461665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30478343323285815407591093 2857344686558045194461665)
  ·
    refine ⟨2143008514918533895846249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2857344686558045194461665 2143008514918533895846249)
    ·
      refine ⟨1607256386188900421884687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143008514918533895846249 1607256386188900421884687)
      ·
        refine ⟨2410884579283350632827031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607256386188900421884687 2410884579283350632827031)
        ·
          refine ⟨3616326868925025949240547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410884579283350632827031 3616326868925025949240547)
          ·
            refine ⟨5424490303387538923860821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616326868925025949240547 5424490303387538923860821)
            ·
              refine ⟨31784122871411360881997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5424490303387538923860821 31784122871411360881997)
              ·
                rfl

theorem cell21_1253462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 9].length) (baseStart_1253462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253462 prefixEnd_1253462 := by exact prefixLift 1253462
  have htrace : WordTrace (prefixWord ++ tailWord_1253462) baseStart_1253462 baseEnd_1253462 := by
    simpa [prefixWord, tailWord_1253462, baseEnd_1253462] using wordTrace_append hprefix tailTrace_1253462
  have hstable : (prefixWord ++ tailWord_1253462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253462).length < 2 ^ (prefixWord ++ tailWord_1253462).sum := by decide
  have hdescent : baseEnd_1253462 < baseStart_1253462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253476 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1253476 : Nat := 118140960795 + 1253476 * 2 ^ 59
def prefixEnd_1253476 : Nat := 4983230072969 + 3 ^ 40 * 1253476 * 2
def baseEnd_1253476 : Nat := 286060300833441334704611

theorem tailTrace_1253476 : CollatzResearch.WordTrace tailWord_1253476 prefixEnd_1253476 286060300833441334704611 := by
  unfold tailWord_1253476
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859012803439001751198141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30478683737918669001597521 22859012803439001751198141)
  ·
    refine ⟨8572129801289625656699303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22859012803439001751198141 8572129801289625656699303)
    ·
      refine ⟨12858194701934438485048955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8572129801289625656699303 12858194701934438485048955)
      ·
        refine ⟨19287292052901657727573433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12858194701934438485048955 19287292052901657727573433)
        ·
          refine ⟨14465469039676243295680075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19287292052901657727573433 14465469039676243295680075)
          ·
            refine ⟨21698203559514364943520113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465469039676243295680075 21698203559514364943520113)
            ·
              refine ⟨16273652669635773707640085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21698203559514364943520113 16273652669635773707640085)
              ·
                refine ⟨762827468889176892545629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16273652669635773707640085 762827468889176892545629)
                ·
                  refine ⟨286060300833441334704611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762827468889176892545629 286060300833441334704611)
                  ·
                    rfl

theorem cell21_1253476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1253476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253476 prefixEnd_1253476 := by exact prefixLift 1253476
  have htrace : WordTrace (prefixWord ++ tailWord_1253476) baseStart_1253476 baseEnd_1253476 := by
    simpa [prefixWord, tailWord_1253476, baseEnd_1253476] using wordTrace_append hprefix tailTrace_1253476
  have hstable : (prefixWord ++ tailWord_1253476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253476).length < 2 ^ (prefixWord ++ tailWord_1253476).sum := by decide
  have hdescent : baseEnd_1253476 < baseStart_1253476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253527 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 3]
def baseStart_1253527 : Nat := 118140960795 + 1253527 * 2 ^ 59
def prefixEnd_1253527 : Nat := 4983230072969 + 3 ^ 40 * 1253527 * 2
def baseEnd_1253527 : Nat := 286071939728276579354507

theorem tailTrace_1253527 : CollatzResearch.WordTrace tailWord_1253527 prefixEnd_1253527 286071939728276579354507 := by
  unfold tailWord_1253527
  simp only [CollatzResearch.WordTrace]
  refine ⟨45719885729693239212502835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30479923819795492808335223 45719885729693239212502835)
  ·
    refine ⟨68579828594539858818754253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45719885729693239212502835 68579828594539858818754253)
    ·
      refine ⟨25717435722952447057032845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68579828594539858818754253 25717435722952447057032845)
      ·
        refine ⟨9644038396107167646387317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25717435722952447057032845 9644038396107167646387317)
        ·
          refine ⟨904128599635046966848811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9644038396107167646387317 904128599635046966848811)
          ·
            refine ⟨1356192899452570450273217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904128599635046966848811 1356192899452570450273217)
            ·
              refine ⟨1017144674589427837704913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356192899452570450273217 1017144674589427837704913)
              ·
                refine ⟨762858505942070878278685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017144674589427837704913 762858505942070878278685)
                ·
                  refine ⟨286071939728276579354507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762858505942070878278685 286071939728276579354507)
                  ·
                    rfl

theorem cell21_1253527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].length) (baseStart_1253527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253527 prefixEnd_1253527 := by exact prefixLift 1253527
  have htrace : WordTrace (prefixWord ++ tailWord_1253527) baseStart_1253527 baseEnd_1253527 := by
    simpa [prefixWord, tailWord_1253527, baseEnd_1253527] using wordTrace_append hprefix tailTrace_1253527
  have hstable : (prefixWord ++ tailWord_1253527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253527).length < 2 ^ (prefixWord ++ tailWord_1253527).sum := by decide
  have hdescent : baseEnd_1253527 < baseStart_1253527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253538 : List Nat := [3, 3, 1, 3, 1, 3, 1, 6]
def baseStart_1253538 : Nat := 118140960795 + 1253538 * 2 ^ 59
def prefixEnd_1253538 : Nat := 4983230072969 + 3 ^ 40 * 1253538 * 2
def baseEnd_1253538 : Nat := 95358150026047668223717

theorem tailTrace_1253538 : CollatzResearch.WordTrace tailWord_1253538 prefixEnd_1253538 95358150026047668223717 := by
  unfold tailWord_1253538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430071733163347022788317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30480191288435592060768845 11430071733163347022788317)
  ·
    refine ⟨4286276899936255133545619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11430071733163347022788317 4286276899936255133545619)
    ·
      refine ⟨6429415349904382700318429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286276899936255133545619 6429415349904382700318429)
      ·
        refine ⟨2411030756214143512619411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6429415349904382700318429 2411030756214143512619411)
        ·
          refine ⟨3616546134321215268929117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411030756214143512619411 3616546134321215268929117)
          ·
            refine ⟨1356204800370455725848419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3616546134321215268929117 1356204800370455725848419)
            ·
              refine ⟨2034307200555683588772629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356204800370455725848419 2034307200555683588772629)
              ·
                refine ⟨95358150026047668223717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034307200555683588772629 95358150026047668223717)
                ·
                  rfl

theorem cell21_1253538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_1253538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253538 prefixEnd_1253538 := by exact prefixLift 1253538
  have htrace : WordTrace (prefixWord ++ tailWord_1253538) baseStart_1253538 baseEnd_1253538 := by
    simpa [prefixWord, tailWord_1253538, baseEnd_1253538] using wordTrace_append hprefix tailTrace_1253538
  have hstable : (prefixWord ++ tailWord_1253538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253538).length < 2 ^ (prefixWord ++ tailWord_1253538).sum := by decide
  have hdescent : baseEnd_1253538 < baseStart_1253538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253656 : List Nat := [2, 1, 2, 3, 1, 2, 4, 6]
def baseStart_1253656 : Nat := 118140960795 + 1253656 * 2 ^ 59
def prefixEnd_1253656 : Nat := 4983230072969 + 3 ^ 40 * 1253656 * 2
def baseEnd_1253656 : Nat := 95367126428600340568081

theorem tailTrace_1253656 : CollatzResearch.WordTrace tailWord_1253656 prefixEnd_1253656 95367126428600340568081 := by
  unfold tailWord_1253656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22862295373112947121974411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30483060497483929495965881 22862295373112947121974411)
  ·
    refine ⟨34293443059669420682961617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22862295373112947121974411 34293443059669420682961617)
    ·
      refine ⟨25720082294752065512221213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34293443059669420682961617 25720082294752065512221213)
      ·
        refine ⟨9645030860532024567082955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25720082294752065512221213 9645030860532024567082955)
        ·
          refine ⟨14467546290798036850624433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9645030860532024567082955 14467546290798036850624433)
          ·
            refine ⟨10850659718098527637968325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14467546290798036850624433 10850659718098527637968325)
            ·
              refine ⟨2034498697143473932119061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10850659718098527637968325 2034498697143473932119061)
              ·
                refine ⟨95367126428600340568081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034498697143473932119061 95367126428600340568081)
                ·
                  rfl

theorem cell21_1253656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_1253656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253656 prefixEnd_1253656 := by exact prefixLift 1253656
  have htrace : WordTrace (prefixWord ++ tailWord_1253656) baseStart_1253656 baseEnd_1253656 := by
    simpa [prefixWord, tailWord_1253656, baseEnd_1253656] using wordTrace_append hprefix tailTrace_1253656
  have hstable : (prefixWord ++ tailWord_1253656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253656).length < 2 ^ (prefixWord ++ tailWord_1253656).sum := by decide
  have hdescent : baseEnd_1253656 < baseStart_1253656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253715 : List Nat := [1, 1, 1, 2, 1, 1, 4, 10]
def baseStart_1253715 : Nat := 118140960795 + 1253715 * 2 ^ 59
def prefixEnd_1253715 : Nat := 4983230072969 + 3 ^ 40 * 1253715 * 2
def baseEnd_1253715 : Nat := 95371614629876676740263

theorem tailTrace_1253715 : CollatzResearch.WordTrace tailWord_1253715 prefixEnd_1253715 95371614629876676740263 := by
  unfold tailWord_1253715
  simp only [CollatzResearch.WordTrace]
  refine ⟨45726742653012147320346599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30484495102008098213564399 45726742653012147320346599)
  ·
    refine ⟨68590113979518220980519899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45726742653012147320346599 68590113979518220980519899)
    ·
      refine ⟨102885170969277331470779849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68590113979518220980519899 102885170969277331470779849)
      ·
        refine ⟨77163878226957998603084887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102885170969277331470779849 77163878226957998603084887)
        ·
          refine ⟨115745817340436997904627331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77163878226957998603084887 115745817340436997904627331)
          ·
            refine ⟨173618726010655496856940997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115745817340436997904627331 173618726010655496856940997)
            ·
              refine ⟨32553511126997905660676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173618726010655496856940997 32553511126997905660676437)
              ·
                refine ⟨95371614629876676740263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32553511126997905660676437 95371614629876676740263)
                ·
                  rfl

theorem cell21_1253715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_1253715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253715 prefixEnd_1253715 := by exact prefixLift 1253715
  have htrace : WordTrace (prefixWord ++ tailWord_1253715) baseStart_1253715 baseEnd_1253715 := by
    simpa [prefixWord, tailWord_1253715, baseEnd_1253715] using wordTrace_append hprefix tailTrace_1253715
  have hstable : (prefixWord ++ tailWord_1253715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253715).length < 2 ^ (prefixWord ++ tailWord_1253715).sum := by decide
  have hdescent : baseEnd_1253715 < baseStart_1253715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253870 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_1253870 : Nat := 118140960795 + 1253870 * 2 ^ 59
def prefixEnd_1253870 : Nat := 4983230072969 + 3 ^ 40 * 1253870 * 2
def baseEnd_1253870 : Nat := 286150217001384205137139

theorem tailTrace_1253870 : CollatzResearch.WordTrace tailWord_1253870 prefixEnd_1253870 286150217001384205137139 := by
  unfold tailWord_1253870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716549495931326099029883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30488263978300405861492709 5716549495931326099029883)
  ·
    refine ⟨8574824243896989148544825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5716549495931326099029883 8574824243896989148544825)
    ·
      refine ⟨6431118182922741861408619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574824243896989148544825 6431118182922741861408619)
      ·
        refine ⟨9646677274384112792112929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431118182922741861408619 9646677274384112792112929)
        ·
          refine ⟨7235007955788084594084697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9646677274384112792112929 7235007955788084594084697)
          ·
            refine ⟨5426255966841063445563523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7235007955788084594084697 5426255966841063445563523)
            ·
              refine ⟨8139383950261595168345285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5426255966841063445563523 8139383950261595168345285)
              ·
                refine ⟨1526134490674049094064741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8139383950261595168345285 1526134490674049094064741)
                ·
                  refine ⟨286150217001384205137139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526134490674049094064741 286150217001384205137139)
                  ·
                    rfl

theorem cell21_1253870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_1253870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253870 prefixEnd_1253870 := by exact prefixLift 1253870
  have htrace : WordTrace (prefixWord ++ tailWord_1253870) baseStart_1253870 baseEnd_1253870 := by
    simpa [prefixWord, tailWord_1253870, baseEnd_1253870] using wordTrace_append hprefix tailTrace_1253870
  have hstable : (prefixWord ++ tailWord_1253870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253870).length < 2 ^ (prefixWord ++ tailWord_1253870).sum := by decide
  have hdescent : baseEnd_1253870 < baseStart_1253870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253943 : List Nat := [1, 1, 3, 1, 2, 3, 2, 8]
def baseStart_1253943 : Nat := 118140960795 + 1253943 * 2 ^ 59
def prefixEnd_1253943 : Nat := 4983230072969 + 3 ^ 40 * 1253943 * 2
def baseEnd_1253943 : Nat := 95388958865317433473441

theorem tailTrace_1253943 : CollatzResearch.WordTrace tailWord_1253943 prefixEnd_1253943 95388958865317433473441 := by
  unfold tailWord_1253943
  simp only [CollatzResearch.WordTrace]
  refine ⟨45735058496186142259646483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30490038997457428173097655 45735058496186142259646483)
  ·
    refine ⟨68602587744279213389469725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45735058496186142259646483 68602587744279213389469725)
    ·
      refine ⟨25725970404104705021051147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68602587744279213389469725 25725970404104705021051147)
      ·
        refine ⟨38588955606157057531576721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25725970404104705021051147 38588955606157057531576721)
        ·
          refine ⟨28941716704617793148682541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38588955606157057531576721 28941716704617793148682541)
          ·
            refine ⟨10853143764231672430755953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28941716704617793148682541 10853143764231672430755953)
            ·
              refine ⟨8139857823173754323066965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10853143764231672430755953 8139857823173754323066965)
              ·
                refine ⟨95388958865317433473441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8139857823173754323066965 95388958865317433473441)
                ·
                  rfl

theorem cell21_1253943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_1253943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1253943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1253943 prefixEnd_1253943 := by exact prefixLift 1253943
  have htrace : WordTrace (prefixWord ++ tailWord_1253943) baseStart_1253943 baseEnd_1253943 := by
    simpa [prefixWord, tailWord_1253943, baseEnd_1253943] using wordTrace_append hprefix tailTrace_1253943
  have hstable : (prefixWord ++ tailWord_1253943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253943).length < 2 ^ (prefixWord ++ tailWord_1253943).sum := by decide
  have hdescent : baseEnd_1253943 < baseStart_1253943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254019 : List Nat := [1, 1, 1, 3, 3, 1, 4, 7]
def baseStart_1254019 : Nat := 118140960795 + 1254019 * 2 ^ 59
def prefixEnd_1254019 : Nat := 4983230072969 + 3 ^ 40 * 1254019 * 2
def baseEnd_1254019 : Nat := 95394740277131019051167

theorem tailTrace_1254019 : CollatzResearch.WordTrace tailWord_1254019 prefixEnd_1254019 95394740277131019051167 := by
  unfold tailWord_1254019
  simp only [CollatzResearch.WordTrace]
  refine ⟨45737830443910807239413111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30491886962607204826275407 45737830443910807239413111)
  ·
    refine ⟨68606745665866210859119667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45737830443910807239413111 68606745665866210859119667)
    ·
      refine ⟨102910118498799316288679501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68606745665866210859119667 102910118498799316288679501)
      ·
        refine ⟨38591294437049743608254813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102910118498799316288679501 38591294437049743608254813)
        ·
          refine ⟨14471735413893653853095555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38591294437049743608254813 14471735413893653853095555)
          ·
            refine ⟨21707603120840480779643333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14471735413893653853095555 21707603120840480779643333)
            ·
              refine ⟨4070175585157590146183125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21707603120840480779643333 4070175585157590146183125)
              ·
                refine ⟨95394740277131019051167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4070175585157590146183125 95394740277131019051167)
                ·
                  rfl

theorem cell21_1254019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_1254019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254019 prefixEnd_1254019 := by exact prefixLift 1254019
  have htrace : WordTrace (prefixWord ++ tailWord_1254019) baseStart_1254019 baseEnd_1254019 := by
    simpa [prefixWord, tailWord_1254019, baseEnd_1254019] using wordTrace_append hprefix tailTrace_1254019
  have hstable : (prefixWord ++ tailWord_1254019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254019).length < 2 ^ (prefixWord ++ tailWord_1254019).sum := by decide
  have hdescent : baseEnd_1254019 < baseStart_1254019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254036 : List Nat := [2, 4, 2, 2, 1, 10]
def baseStart_1254036 : Nat := 118140960795 + 1254036 * 2 ^ 59
def prefixEnd_1254036 : Nat := 4983230072969 + 3 ^ 40 * 1254036 * 2
def baseEnd_1254036 : Nat := 10599559276407585384079

theorem tailTrace_1254036 : CollatzResearch.WordTrace tailWord_1254036 prefixEnd_1254036 10599559276407585384079 := by
  unfold tailWord_1254036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869225242424609571390981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30492300323232812761854641 22869225242424609571390981)
  ·
    refine ⟨4287979732954614294635809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22869225242424609571390981 4287979732954614294635809)
    ·
      refine ⟨3215984799715960720976857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4287979732954614294635809 3215984799715960720976857)
      ·
        refine ⟨2411988599786970540732643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3215984799715960720976857 2411988599786970540732643)
        ·
          refine ⟨3617982899680455811098965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411988599786970540732643 3617982899680455811098965)
          ·
            refine ⟨10599559276407585384079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3617982899680455811098965 10599559276407585384079)
            ·
              rfl

theorem cell21_1254036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 10].length) (baseStart_1254036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254036 prefixEnd_1254036 := by exact prefixLift 1254036
  have htrace : WordTrace (prefixWord ++ tailWord_1254036) baseStart_1254036 baseEnd_1254036 := by
    simpa [prefixWord, tailWord_1254036, baseEnd_1254036] using wordTrace_append hprefix tailTrace_1254036
  have hstable : (prefixWord ++ tailWord_1254036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254036).length < 2 ^ (prefixWord ++ tailWord_1254036).sum := by decide
  have hdescent : baseEnd_1254036 < baseStart_1254036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254064 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_1254064 : Nat := 118140960795 + 1254064 * 2 ^ 59
def prefixEnd_1254064 : Nat := 4983230072969 + 3 ^ 40 * 1254064 * 2
def baseEnd_1254064 : Nat := 286194490444482978903409

theorem tailTrace_1254064 : CollatzResearch.WordTrace tailWord_1254064 prefixEnd_1254064 286194490444482978903409 := by
  unfold tailWord_1254064
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869735864373889962400623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30492981152498519949867497 22869735864373889962400623)
  ·
    refine ⟨34304603796560834943600935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22869735864373889962400623 34304603796560834943600935)
    ·
      refine ⟨51456905694841252415401403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34304603796560834943600935 51456905694841252415401403)
      ·
        refine ⟨77185358542261878623102105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51456905694841252415401403 77185358542261878623102105)
        ·
          refine ⟨57889018906696408967326579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77185358542261878623102105 57889018906696408967326579)
          ·
            refine ⟨86833528360044613450989869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57889018906696408967326579 86833528360044613450989869)
            ·
              refine ⟨32562573135016730044121201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86833528360044613450989869 32562573135016730044121201)
              ·
                refine ⟨24421929851262547533090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32562573135016730044121201 24421929851262547533090901)
                ·
                  refine ⟨286194490444482978903409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24421929851262547533090901 286194490444482978903409)
                  ·
                    rfl

theorem cell21_1254064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_1254064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254064 prefixEnd_1254064 := by exact prefixLift 1254064
  have htrace : WordTrace (prefixWord ++ tailWord_1254064) baseStart_1254064 baseEnd_1254064 := by
    simpa [prefixWord, tailWord_1254064, baseEnd_1254064] using wordTrace_append hprefix tailTrace_1254064
  have hstable : (prefixWord ++ tailWord_1254064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254064).length < 2 ^ (prefixWord ++ tailWord_1254064).sum := by decide
  have hdescent : baseEnd_1254064 < baseStart_1254064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254084 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1254084 : Nat := 118140960795 + 1254084 * 2 ^ 59
def prefixEnd_1254084 : Nat := 4983230072969 + 3 ^ 40 * 1254084 * 2
def baseEnd_1254084 : Nat := 286199054716967388570035

theorem tailTrace_1254084 : CollatzResearch.WordTrace tailWord_1254084 prefixEnd_1254084 286199054716967388570035 := by
  unfold tailWord_1254084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870100594337661670264653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30493467459116882227019537 22870100594337661670264653)
  ·
    refine ⟨8576287722876623126349245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22870100594337661670264653 8576287722876623126349245)
    ·
      refine ⟨3216107896078733672380967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8576287722876623126349245 3216107896078733672380967)
      ·
        refine ⟨4824161844118100508571451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216107896078733672380967 4824161844118100508571451)
        ·
          refine ⟨7236242766177150762857177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4824161844118100508571451 7236242766177150762857177)
          ·
            refine ⟨5427182074632863072142883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7236242766177150762857177 5427182074632863072142883)
            ·
              refine ⟨8140773111949294608214325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427182074632863072142883 8140773111949294608214325)
              ·
                refine ⟨763197479245246369520093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8140773111949294608214325 763197479245246369520093)
                ·
                  refine ⟨286199054716967388570035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763197479245246369520093 286199054716967388570035)
                  ·
                    rfl

theorem cell21_1254084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1254084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254084 prefixEnd_1254084 := by exact prefixLift 1254084
  have htrace : WordTrace (prefixWord ++ tailWord_1254084) baseStart_1254084 baseEnd_1254084 := by
    simpa [prefixWord, tailWord_1254084, baseEnd_1254084] using wordTrace_append hprefix tailTrace_1254084
  have hstable : (prefixWord ++ tailWord_1254084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254084).length < 2 ^ (prefixWord ++ tailWord_1254084).sum := by decide
  have hdescent : baseEnd_1254084 < baseStart_1254084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254098 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1254098 : Nat := 118140960795 + 1254098 * 2 ^ 59
def prefixEnd_1254098 : Nat := 4983230072969 + 3 ^ 40 * 1254098 * 2
def baseEnd_1254098 : Nat := 286202249707706475336673

theorem tailTrace_1254098 : CollatzResearch.WordTrace tailWord_1254098 prefixEnd_1254098 286202249707706475336673 := by
  unfold tailWord_1254098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435177952656150932884737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30493807873749735821025965 11435177952656150932884737)
  ·
    refine ⟨8576383464492113199663553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11435177952656150932884737 8576383464492113199663553)
    ·
      refine ⟨6432287598369084899747665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8576383464492113199663553 6432287598369084899747665)
      ·
        refine ⟨4824215698776813674810749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6432287598369084899747665 4824215698776813674810749)
        ·
          refine ⟨1809080887041305128054031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4824215698776813674810749 1809080887041305128054031)
          ·
            refine ⟨2713621330561957692081047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809080887041305128054031 2713621330561957692081047)
            ·
              refine ⟨4070431995842936538121571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713621330561957692081047 4070431995842936538121571)
              ·
                refine ⟨6105647993764404807182357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070431995842936538121571 6105647993764404807182357)
                ·
                  refine ⟨286202249707706475336673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6105647993764404807182357 286202249707706475336673)
                  ·
                    rfl

theorem cell21_1254098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1254098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254098 prefixEnd_1254098 := by exact prefixLift 1254098
  have htrace : WordTrace (prefixWord ++ tailWord_1254098) baseStart_1254098 baseEnd_1254098 := by
    simpa [prefixWord, tailWord_1254098, baseEnd_1254098] using wordTrace_append hprefix tailTrace_1254098
  have hstable : (prefixWord ++ tailWord_1254098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254098).length < 2 ^ (prefixWord ++ tailWord_1254098).sum := by decide
  have hdescent : baseEnd_1254098 < baseStart_1254098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254115 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 4]
def baseStart_1254115 : Nat := 118140960795 + 1254115 * 2 ^ 59
def prefixEnd_1254115 : Nat := 4983230072969 + 3 ^ 40 * 1254115 * 2
def baseEnd_1254115 : Nat := 286206129339318223553305

theorem tailTrace_1254115 : CollatzResearch.WordTrace tailWord_1254115 prefixEnd_1254115 286206129339318223553305 := by
  unfold tailWord_1254115
  simp only [CollatzResearch.WordTrace]
  refine ⟨45741331851563015634907799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30494221234375343756605199 45741331851563015634907799)
  ·
    refine ⟨68611997777344523452361699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45741331851563015634907799 68611997777344523452361699)
    ·
      refine ⟨102917996666016785178542549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68611997777344523452361699 102917996666016785178542549)
      ·
        refine ⟨2412140546859768402622091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102917996666016785178542549 2412140546859768402622091)
        ·
          refine ⟨3618210820289652603933137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412140546859768402622091 3618210820289652603933137)
          ·
            refine ⟨2713658115217239452949853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3618210820289652603933137 2713658115217239452949853)
            ·
              refine ⟨1017621793206464794856195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2713658115217239452949853 1017621793206464794856195)
              ·
                refine ⟨1526432689809697192284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017621793206464794856195 1526432689809697192284293)
                ·
                  refine ⟨286206129339318223553305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526432689809697192284293 286206129339318223553305)
                  ·
                    rfl

theorem cell21_1254115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_1254115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254115 prefixEnd_1254115 := by exact prefixLift 1254115
  have htrace : WordTrace (prefixWord ++ tailWord_1254115) baseStart_1254115 baseEnd_1254115 := by
    simpa [prefixWord, tailWord_1254115, baseEnd_1254115] using wordTrace_append hprefix tailTrace_1254115
  have hstable : (prefixWord ++ tailWord_1254115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254115).length < 2 ^ (prefixWord ++ tailWord_1254115).sum := by decide
  have hdescent : baseEnd_1254115 < baseStart_1254115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254233 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_1254233 : Nat := 118140960795 + 1254233 * 2 ^ 59
def prefixEnd_1254233 : Nat := 4983230072969 + 3 ^ 40 * 1254233 * 2
def baseEnd_1254233 : Nat := 286233058546976240586397

theorem tailTrace_1254233 : CollatzResearch.WordTrace tailWord_1254233 prefixEnd_1254233 286233058546976240586397 := by
  unfold tailWord_1254233
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745635665135521787703353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30497090443423681191802235 45745635665135521787703353)
  ·
    refine ⟨34309226748851641340777515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45745635665135521787703353 34309226748851641340777515)
    ·
      refine ⟨51463840123277462011166273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34309226748851641340777515 51463840123277462011166273)
      ·
        refine ⟨38597880092458096508374705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51463840123277462011166273 38597880092458096508374705)
        ·
          refine ⟨28948410069343572381281029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38597880092458096508374705 28948410069343572381281029)
          ·
            refine ⟨5427826888001919821490193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28948410069343572381281029 5427826888001919821490193)
            ·
              refine ⟨4070870166001439866117645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427826888001919821490193 4070870166001439866117645)
              ·
                refine ⟨1526576312250539949794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4070870166001439866117645 1526576312250539949794117)
                ·
                  refine ⟨286233058546976240586397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526576312250539949794117 286233058546976240586397)
                  ·
                    rfl

theorem cell21_1254233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_1254233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254233 prefixEnd_1254233 := by exact prefixLift 1254233
  have htrace : WordTrace (prefixWord ++ tailWord_1254233) baseStart_1254233 baseEnd_1254233 := by
    simpa [prefixWord, tailWord_1254233, baseEnd_1254233] using wordTrace_append hprefix tailTrace_1254233
  have hstable : (prefixWord ++ tailWord_1254233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254233).length < 2 ^ (prefixWord ++ tailWord_1254233).sum := by decide
  have hdescent : baseEnd_1254233 < baseStart_1254233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254298 : List Nat := [3, 1, 1, 4, 4, 1, 2, 5]
def baseStart_1254298 : Nat := 118140960795 + 1254298 * 2 ^ 59
def prefixEnd_1254298 : Nat := 4983230072969 + 3 ^ 40 * 1254298 * 2
def baseEnd_1254298 : Nat := 95415964144183524000977

theorem tailTrace_1254298 : CollatzResearch.WordTrace tailWord_1254298 prefixEnd_1254298 95415964144183524000977 := by
  unfold tailWord_1254298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11437001602475009472204887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30498670939933358592546365 11437001602475009472204887)
  ·
    refine ⟨17155502403712514208307331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11437001602475009472204887 17155502403712514208307331)
    ·
      refine ⟨25733253605568771312460997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17155502403712514208307331 25733253605568771312460997)
      ·
        refine ⟨4824985051044144621086437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25733253605568771312460997 4824985051044144621086437)
        ·
          refine ⟨904684697070777116453707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4824985051044144621086437 904684697070777116453707)
          ·
            refine ⟨1357027045606165674680561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904684697070777116453707 1357027045606165674680561)
            ·
              refine ⟨1017770284204624256010421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357027045606165674680561 1017770284204624256010421)
              ·
                refine ⟨95415964144183524000977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1017770284204624256010421 95415964144183524000977)
                ·
                  rfl

theorem cell21_1254298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_1254298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254298 prefixEnd_1254298 := by exact prefixLift 1254298
  have htrace : WordTrace (prefixWord ++ tailWord_1254298) baseStart_1254298 baseEnd_1254298 := by
    simpa [prefixWord, tailWord_1254298, baseEnd_1254298] using wordTrace_append hprefix tailTrace_1254298
  have hstable : (prefixWord ++ tailWord_1254298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254298).length < 2 ^ (prefixWord ++ tailWord_1254298).sum := by decide
  have hdescent : baseEnd_1254298 < baseStart_1254298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254371 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 3]
def baseStart_1254371 : Nat := 118140960795 + 1254371 * 2 ^ 59
def prefixEnd_1254371 : Nat := 4983230072969 + 3 ^ 40 * 1254371 * 2
def baseEnd_1254371 : Nat := 286264552027118667286115

theorem tailTrace_1254371 : CollatzResearch.WordTrace tailWord_1254371 prefixEnd_1254371 286264552027118667286115 := by
  unfold tailWord_1254371
  simp only [CollatzResearch.WordTrace]
  refine ⟨45750668938635571356226967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30500445959090380904151311 45750668938635571356226967)
  ·
    refine ⟨68626003407953357034340451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45750668938635571356226967 68626003407953357034340451)
    ·
      refine ⟨102939005111930035551510677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68626003407953357034340451 102939005111930035551510677)
      ·
        refine ⟨4825265864621720416477063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102939005111930035551510677 4825265864621720416477063)
        ·
          refine ⟨7237898796932580624715595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4825265864621720416477063 7237898796932580624715595)
          ·
            refine ⟨10856848195398870937073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237898796932580624715595 10856848195398870937073393)
            ·
              refine ⟨8142636146549153202805045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10856848195398870937073393 8142636146549153202805045)
              ·
                refine ⟨763372138738983112762973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8142636146549153202805045 763372138738983112762973)
                ·
                  refine ⟨286264552027118667286115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763372138738983112762973 286264552027118667286115)
                  ·
                    rfl

theorem cell21_1254371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].length) (baseStart_1254371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254371 prefixEnd_1254371 := by exact prefixLift 1254371
  have htrace : WordTrace (prefixWord ++ tailWord_1254371) baseStart_1254371 baseEnd_1254371 := by
    simpa [prefixWord, tailWord_1254371, baseEnd_1254371] using wordTrace_append hprefix tailTrace_1254371
  have hstable : (prefixWord ++ tailWord_1254371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254371).length < 2 ^ (prefixWord ++ tailWord_1254371).sum := by decide
  have hdescent : baseEnd_1254371 < baseStart_1254371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254385 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_1254385 : Nat := 118140960795 + 1254385 * 2 ^ 59
def prefixEnd_1254385 : Nat := 4983230072969 + 3 ^ 40 * 1254385 * 2
def baseEnd_1254385 : Nat := 286267747017857754052753

theorem tailTrace_1254385 : CollatzResearch.WordTrace tailWord_1254385 prefixEnd_1254385 286267747017857754052753 := by
  unfold tailWord_1254385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45751179560584851747236609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30500786373723234498157739 45751179560584851747236609)
  ·
    refine ⟨34313384670438638810427457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45751179560584851747236609 34313384670438638810427457)
    ·
      refine ⟨25735038502828979107820593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34313384670438638810427457 25735038502828979107820593)
      ·
        refine ⟨19301278877121734330865445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25735038502828979107820593 19301278877121734330865445)
        ·
          refine ⟨3618989789460325187037271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19301278877121734330865445 3618989789460325187037271)
          ·
            refine ⟨5428484684190487780555907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618989789460325187037271 5428484684190487780555907)
            ·
              refine ⟨8142727026285731670833861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428484684190487780555907 8142727026285731670833861)
              ·
                refine ⟨1526761317428574688281349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8142727026285731670833861 1526761317428574688281349)
                ·
                  refine ⟨286267747017857754052753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526761317428574688281349 286267747017857754052753)
                  ·
                    rfl

theorem cell21_1254385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_1254385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254385 prefixEnd_1254385 := by exact prefixLift 1254385
  have htrace : WordTrace (prefixWord ++ tailWord_1254385) baseStart_1254385 baseEnd_1254385 := by
    simpa [prefixWord, tailWord_1254385, baseEnd_1254385] using wordTrace_append hprefix tailTrace_1254385
  have hstable : (prefixWord ++ tailWord_1254385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254385).length < 2 ^ (prefixWord ++ tailWord_1254385).sum := by decide
  have hdescent : baseEnd_1254385 < baseStart_1254385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254444 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1254444 : Nat := 118140960795 + 1254444 * 2 ^ 59
def prefixEnd_1254444 : Nat := 4983230072969 + 3 ^ 40 * 1254444 * 2
def baseEnd_1254444 : Nat := 286281211621686762569299

theorem tailTrace_1254444 : CollatzResearch.WordTrace tailWord_1254444 prefixEnd_1254444 286281211621686762569299 := by
  unfold tailWord_1254444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876665733685552411817193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30502220978247403215756257 22876665733685552411817193)
  ·
    refine ⟨17157499300264164308862895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22876665733685552411817193 17157499300264164308862895)
    ·
      refine ⟨25736248950396246463294343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17157499300264164308862895 25736248950396246463294343)
      ·
        refine ⟨38604373425594369694941515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25736248950396246463294343 38604373425594369694941515)
        ·
          refine ⟨57906560138391554542412273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38604373425594369694941515 57906560138391554542412273)
          ·
            refine ⟨43429920103793665906809205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57906560138391554542412273 43429920103793665906809205)
            ·
              refine ⟨4071555009730656178763363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43429920103793665906809205 4071555009730656178763363)
              ·
                refine ⟨6107332514595984268145045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071555009730656178763363 6107332514595984268145045)
                ·
                  refine ⟨286281211621686762569299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6107332514595984268145045 286281211621686762569299)
                  ·
                    rfl

theorem cell21_1254444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1254444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254444 prefixEnd_1254444 := by exact prefixLift 1254444
  have htrace : WordTrace (prefixWord ++ tailWord_1254444) baseStart_1254444 baseEnd_1254444 := by
    simpa [prefixWord, tailWord_1254444, baseEnd_1254444] using wordTrace_append hprefix tailTrace_1254444
  have hstable : (prefixWord ++ tailWord_1254444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254444).length < 2 ^ (prefixWord ++ tailWord_1254444).sum := by decide
  have hdescent : baseEnd_1254444 < baseStart_1254444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254554 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1254554 : Nat := 118140960795 + 1254554 * 2 ^ 59
def prefixEnd_1254554 : Nat := 4983230072969 + 3 ^ 40 * 1254554 * 2
def baseEnd_1254554 : Nat := 286306315120351015735741

theorem tailTrace_1254554 : CollatzResearch.WordTrace tailWord_1254554 prefixEnd_1254554 286306315120351015735741 := by
  unfold tailWord_1254554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439335874243148402534679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30504895664648395740092477 11439335874243148402534679)
  ·
    refine ⟨17159003811364722603802019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11439335874243148402534679 17159003811364722603802019)
    ·
      refine ⟨25738505717047083905703029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159003811364722603802019 25738505717047083905703029)
      ·
        refine ⟨2412984910973164116159659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25738505717047083905703029 2412984910973164116159659)
        ·
          refine ⟨3619477366459746174239489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412984910973164116159659 3619477366459746174239489)
          ·
            refine ⟨2714608024844809630679617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619477366459746174239489 2714608024844809630679617)
            ·
              refine ⟨2035956018633607223009713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714608024844809630679617 2035956018633607223009713)
              ·
                refine ⟨1526967013975205417257285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035956018633607223009713 1526967013975205417257285)
                ·
                  refine ⟨286306315120351015735741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526967013975205417257285 286306315120351015735741)
                  ·
                    rfl

theorem cell21_1254554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1254554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254554 prefixEnd_1254554 := by exact prefixLift 1254554
  have htrace : WordTrace (prefixWord ++ tailWord_1254554) baseStart_1254554 baseEnd_1254554 := by
    simpa [prefixWord, tailWord_1254554, baseEnd_1254554] using wordTrace_append hprefix tailTrace_1254554
  have hstable : (prefixWord ++ tailWord_1254554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254554).length < 2 ^ (prefixWord ++ tailWord_1254554).sum := by decide
  have hdescent : baseEnd_1254554 < baseStart_1254554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254605 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1254605 : Nat := 118140960795 + 1254605 * 2 ^ 59
def prefixEnd_1254605 : Nat := 4983230072969 + 3 ^ 40 * 1254605 * 2
def baseEnd_1254605 : Nat := 286317954015186260385637

theorem tailTrace_1254605 : CollatzResearch.WordTrace tailWord_1254605 prefixEnd_1254605 286317954015186260385637 := by
  unfold tailWord_1254605
  simp only [CollatzResearch.WordTrace]
  refine ⟨45759203619787829320245269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30506135746525219546830179 45759203619787829320245269)
  ·
    refine ⟨2144962669677554499386497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45759203619787829320245269 2144962669677554499386497)
    ·
      refine ⟨1608722002258165874539873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2144962669677554499386497 1608722002258165874539873)
      ·
        refine ⟨1206541501693624405904905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1608722002258165874539873 1206541501693624405904905)
        ·
          refine ⟨904906126270218304428679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1206541501693624405904905 904906126270218304428679)
          ·
            refine ⟨1357359189405327456643019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904906126270218304428679 1357359189405327456643019)
            ·
              refine ⟨2036038784107991184964529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357359189405327456643019 2036038784107991184964529)
              ·
                refine ⟨1527029088080993388723397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036038784107991184964529 1527029088080993388723397)
                ·
                  refine ⟨286317954015186260385637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527029088080993388723397 286317954015186260385637)
                  ·
                    rfl

theorem cell21_1254605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1254605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254605 prefixEnd_1254605 := by exact prefixLift 1254605
  have htrace : WordTrace (prefixWord ++ tailWord_1254605) baseStart_1254605 baseEnd_1254605 := by
    simpa [prefixWord, tailWord_1254605, baseEnd_1254605] using wordTrace_append hprefix tailTrace_1254605
  have hstable : (prefixWord ++ tailWord_1254605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254605).length < 2 ^ (prefixWord ++ tailWord_1254605).sum := by decide
  have hdescent : baseEnd_1254605 < baseStart_1254605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254613 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1254613 : Nat := 118140960795 + 1254613 * 2 ^ 59
def prefixEnd_1254613 : Nat := 4983230072969 + 3 ^ 40 * 1254613 * 2
def baseEnd_1254613 : Nat := 286319779724180024252287

theorem tailTrace_1254613 : CollatzResearch.WordTrace tailWord_1254613 prefixEnd_1254613 286319779724180024252287 := by
  unfold tailWord_1254613
  simp only [CollatzResearch.WordTrace]
  refine ⟨45759495403758846686536493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30506330269172564457690995 45759495403758846686536493)
  ·
    refine ⟨17159810776409567507451185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45759495403758846686536493 17159810776409567507451185)
    ·
      refine ⟨12869858082307175630588389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17159810776409567507451185 12869858082307175630588389)
      ·
        refine ⟨2413098390432595430735323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12869858082307175630588389 2413098390432595430735323)
        ·
          refine ⟨3619647585648893146102985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413098390432595430735323 3619647585648893146102985)
          ·
            refine ⟨2714735689236669859577239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619647585648893146102985 2714735689236669859577239)
            ·
              refine ⟨4072103533855004789365859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714735689236669859577239 4072103533855004789365859)
              ·
                refine ⟨6108155300782507184048789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072103533855004789365859 6108155300782507184048789)
                ·
                  refine ⟨286319779724180024252287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6108155300782507184048789 286319779724180024252287)
                  ·
                    rfl

theorem cell21_1254613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1254613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254613 prefixEnd_1254613 := by exact prefixLift 1254613
  have htrace : WordTrace (prefixWord ++ tailWord_1254613) baseStart_1254613 baseEnd_1254613 := by
    simpa [prefixWord, tailWord_1254613, baseEnd_1254613] using wordTrace_append hprefix tailTrace_1254613
  have hstable : (prefixWord ++ tailWord_1254613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254613).length < 2 ^ (prefixWord ++ tailWord_1254613).sum := by decide
  have hdescent : baseEnd_1254613 < baseStart_1254613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254726 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1254726 : Nat := 118140960795 + 1254726 * 2 ^ 59
def prefixEnd_1254726 : Nat := 4983230072969 + 3 ^ 40 * 1254726 * 2
def baseEnd_1254726 : Nat := 286345567863716938868723

theorem tailTrace_1254726 : CollatzResearch.WordTrace tailWord_1254726 prefixEnd_1254726 286345567863716938868723 := by
  unfold tailWord_1254726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430113026635920843293751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30509077901566311323600021 1430113026635920843293751)
  ·
    refine ⟨2145169539953881264940627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430113026635920843293751 2145169539953881264940627)
    ·
      refine ⟨3217754309930821897410941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145169539953881264940627 3217754309930821897410941)
      ·
        refine ⟨1206657866224058211529103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3217754309930821897410941 1206657866224058211529103)
        ·
          refine ⟨1809986799336087317293655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206657866224058211529103 1809986799336087317293655)
          ·
            refine ⟨2714980199004130975940483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809986799336087317293655 2714980199004130975940483)
            ·
              refine ⟨4072470298506196463910725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714980199004130975940483 4072470298506196463910725)
              ·
                refine ⟨763588180969911836983261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4072470298506196463910725 763588180969911836983261)
                ·
                  refine ⟨286345567863716938868723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763588180969911836983261 286345567863716938868723)
                  ·
                    rfl

theorem cell21_1254726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1254726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254726 prefixEnd_1254726 := by exact prefixLift 1254726
  have htrace : WordTrace (prefixWord ++ tailWord_1254726) baseStart_1254726 baseEnd_1254726 := by
    simpa [prefixWord, tailWord_1254726, baseEnd_1254726] using wordTrace_append hprefix tailTrace_1254726
  have hstable : (prefixWord ++ tailWord_1254726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254726).length < 2 ^ (prefixWord ++ tailWord_1254726).sum := by decide
  have hdescent : baseEnd_1254726 < baseStart_1254726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254731 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_1254731 : Nat := 118140960795 + 1254731 * 2 ^ 59
def prefixEnd_1254731 : Nat := 4983230072969 + 3 ^ 40 * 1254731 * 2
def baseEnd_1254731 : Nat := 286346708931838041285379

theorem tailTrace_1254731 : CollatzResearch.WordTrace tailWord_1254731 prefixEnd_1254731 286346708931838041285379 := by
  unfold tailWord_1254731
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763799217331352839332047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30509199478220901892888031 45763799217331352839332047)
  ·
    refine ⟨68645698825997029258998071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45763799217331352839332047 68645698825997029258998071)
    ·
      refine ⟨102968548238995543888497107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68645698825997029258998071 102968548238995543888497107)
      ·
        refine ⟨154452822358493315832745661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102968548238995543888497107 154452822358493315832745661)
        ·
          refine ⟨57919808384434993437279623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154452822358493315832745661 57919808384434993437279623)
          ·
            refine ⟨86879712576652490155919435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57919808384434993437279623 86879712576652490155919435)
            ·
              refine ⟨130319568864978735233879153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86879712576652490155919435 130319568864978735233879153)
              ·
                refine ⟨97739676648734051425409365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130319568864978735233879153 97739676648734051425409365)
                ·
                  refine ⟨286346708931838041285379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97739676648734051425409365 286346708931838041285379)
                  ·
                    rfl

theorem cell21_1254731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_1254731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254731 prefixEnd_1254731 := by exact prefixLift 1254731
  have htrace : WordTrace (prefixWord ++ tailWord_1254731) baseStart_1254731 baseEnd_1254731 := by
    simpa [prefixWord, tailWord_1254731, baseEnd_1254731] using wordTrace_append hprefix tailTrace_1254731
  have hstable : (prefixWord ++ tailWord_1254731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254731).length < 2 ^ (prefixWord ++ tailWord_1254731).sum := by decide
  have hdescent : baseEnd_1254731 < baseStart_1254731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254844 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1254844 : Nat := 118140960795 + 1254844 * 2 ^ 59
def prefixEnd_1254844 : Nat := 4983230072969 + 3 ^ 40 * 1254844 * 2
def baseEnd_1254844 : Nat := 286372497071374955901815

theorem tailTrace_1254844 : CollatzResearch.WordTrace tailWord_1254844 prefixEnd_1254844 286372497071374955901815 := by
  unfold tailWord_1254844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22883960332960986569097793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30511947110614648758797057 22883960332960986569097793)
  ·
    refine ⟨17162970249720739926823345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22883960332960986569097793 17162970249720739926823345)
    ·
      refine ⟨12872227687290554945117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17162970249720739926823345 12872227687290554945117509)
      ·
        refine ⟨2413542691366979052209533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12872227687290554945117509 2413542691366979052209533)
        ·
          refine ⟨905078509262617144578575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2413542691366979052209533 905078509262617144578575)
          ·
            refine ⟨1357617763893925716867863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905078509262617144578575 1357617763893925716867863)
            ·
              refine ⟨2036426645840888575301795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357617763893925716867863 2036426645840888575301795)
              ·
                refine ⟨3054639968761332862952693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036426645840888575301795 3054639968761332862952693)
                ·
                  refine ⟨286372497071374955901815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054639968761332862952693 286372497071374955901815)
                  ·
                    rfl

theorem cell21_1254844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1254844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254844 prefixEnd_1254844 := by exact prefixLift 1254844
  have htrace : WordTrace (prefixWord ++ tailWord_1254844) baseStart_1254844 baseEnd_1254844 := by
    simpa [prefixWord, tailWord_1254844, baseEnd_1254844] using wordTrace_append hprefix tailTrace_1254844
  have hstable : (prefixWord ++ tailWord_1254844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254844).length < 2 ^ (prefixWord ++ tailWord_1254844).sum := by decide
  have hdescent : baseEnd_1254844 < baseStart_1254844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254850 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1254850 : Nat := 118140960795 + 1254850 * 2 ^ 59
def prefixEnd_1254850 : Nat := 4983230072969 + 3 ^ 40 * 1254850 * 2
def baseEnd_1254850 : Nat := 286373866353120278801803

theorem tailTrace_1254850 : CollatzResearch.WordTrace tailWord_1254850 prefixEnd_1254850 286373866353120278801803 := by
  unfold tailWord_1254850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442034875975059040728501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30512093002600157441942669 11442034875975059040728501)
  ·
    refine ⟨1072690769622661785068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11442034875975059040728501 1072690769622661785068297)
    ·
      refine ⟨804518077216996338801223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1072690769622661785068297 804518077216996338801223)
      ·
        refine ⟨1206777115825494508201835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804518077216996338801223 1206777115825494508201835)
        ·
          refine ⟨1810165673738241762302753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206777115825494508201835 1810165673738241762302753)
          ·
            refine ⟨1357624255303681321727065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810165673738241762302753 1357624255303681321727065)
            ·
              refine ⟨1018218191477760991295299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357624255303681321727065 1018218191477760991295299)
              ·
                refine ⟨1527327287216641486942949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018218191477760991295299 1527327287216641486942949)
                ·
                  refine ⟨286373866353120278801803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527327287216641486942949 286373866353120278801803)
                  ·
                    rfl

theorem cell21_1254850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1254850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254850 prefixEnd_1254850 := by exact prefixLift 1254850
  have htrace : WordTrace (prefixWord ++ tailWord_1254850) baseStart_1254850 baseEnd_1254850 := by
    simpa [prefixWord, tailWord_1254850, baseEnd_1254850] using wordTrace_append hprefix tailTrace_1254850
  have hstable : (prefixWord ++ tailWord_1254850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254850).length < 2 ^ (prefixWord ++ tailWord_1254850).sum := by decide
  have hdescent : baseEnd_1254850 < baseStart_1254850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254858 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1254858 : Nat := 118140960795 + 1254858 * 2 ^ 59
def prefixEnd_1254858 : Nat := 4983230072969 + 3 ^ 40 * 1254858 * 2
def baseEnd_1254858 : Nat := 286375692062114042668453

theorem tailTrace_1254858 : CollatzResearch.WordTrace tailWord_1254858 prefixEnd_1254858 286375692062114042668453 := by
  unfold tailWord_1254858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442107821967813382301307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30512287525247502352803485 11442107821967813382301307)
  ·
    refine ⟨17163161732951720073451961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442107821967813382301307 17163161732951720073451961)
    ·
      refine ⟨12872371299713790055088971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17163161732951720073451961 12872371299713790055088971)
      ·
        refine ⟨19308556949570685082633457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872371299713790055088971 19308556949570685082633457)
        ·
          refine ⟨14481417712178013811975093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19308556949570685082633457 14481417712178013811975093)
          ·
            refine ⟨1357632910516688794872665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14481417712178013811975093 1357632910516688794872665)
            ·
              refine ⟨1018224682887516596154499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357632910516688794872665 1018224682887516596154499)
              ·
                refine ⟨1527337024331274894231749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018224682887516596154499 1527337024331274894231749)
                ·
                  refine ⟨286375692062114042668453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527337024331274894231749 286375692062114042668453)
                  ·
                    rfl

theorem cell21_1254858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1254858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254858 prefixEnd_1254858 := by exact prefixLift 1254858
  have htrace : WordTrace (prefixWord ++ tailWord_1254858) baseStart_1254858 baseEnd_1254858 := by
    simpa [prefixWord, tailWord_1254858, baseEnd_1254858] using wordTrace_append hprefix tailTrace_1254858
  have hstable : (prefixWord ++ tailWord_1254858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254858).length < 2 ^ (prefixWord ++ tailWord_1254858).sum := by decide
  have hdescent : baseEnd_1254858 < baseStart_1254858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254869 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1254869 : Nat := 118140960795 + 1254869 * 2 ^ 59
def prefixEnd_1254869 : Nat := 4983230072969 + 3 ^ 40 * 1254869 * 2
def baseEnd_1254869 : Nat := 286378202411980467985097

theorem tailTrace_1254869 : CollatzResearch.WordTrace tailWord_1254869 prefixEnd_1254869 286378202411980467985097 := by
  unfold tailWord_1254869
  simp only [CollatzResearch.WordTrace]
  refine ⟨45768832490831402407855661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30512554993887601605237107 45768832490831402407855661)
  ·
    refine ⟨17163312184061775902945873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45768832490831402407855661 17163312184061775902945873)
    ·
      refine ⟨12872484138046331927209405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17163312184061775902945873 12872484138046331927209405)
      ·
        refine ⟨4827181551767374472703527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12872484138046331927209405 4827181551767374472703527)
        ·
          refine ⟨7240772327651061709055291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827181551767374472703527 7240772327651061709055291)
          ·
            refine ⟨10861158491476592563582937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240772327651061709055291 10861158491476592563582937)
            ·
              refine ⟨8145868868607444422687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10861158491476592563582937 8145868868607444422687203)
              ·
                refine ⟨12218803302911166634030805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145868868607444422687203 12218803302911166634030805)
                ·
                  refine ⟨286378202411980467985097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12218803302911166634030805 286378202411980467985097)
                  ·
                    rfl

theorem cell21_1254869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1254869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254869 prefixEnd_1254869 := by exact prefixLift 1254869
  have htrace : WordTrace (prefixWord ++ tailWord_1254869) baseStart_1254869 baseEnd_1254869 := by
    simpa [prefixWord, tailWord_1254869, baseEnd_1254869] using wordTrace_append hprefix tailTrace_1254869
  have hstable : (prefixWord ++ tailWord_1254869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254869).length < 2 ^ (prefixWord ++ tailWord_1254869).sum := by decide
  have hdescent : baseEnd_1254869 < baseStart_1254869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254931 : List Nat := [1, 1, 1, 2, 1, 7, 3, 5]
def baseStart_1254931 : Nat := 118140960795 + 1254931 * 2 ^ 59
def prefixEnd_1254931 : Nat := 4983230072969 + 3 ^ 40 * 1254931 * 2
def baseEnd_1254931 : Nat := 95464117218894045983879

theorem tailTrace_1254931 : CollatzResearch.WordTrace tailWord_1254931 prefixEnd_1254931 95464117218894045983879 := by
  unfold tailWord_1254931
  simp only [CollatzResearch.WordTrace]
  refine ⟨45771093816606786996612647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30514062544404524664408431 45771093816606786996612647)
  ·
    refine ⟨68656640724910180494918971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45771093816606786996612647 68656640724910180494918971)
    ·
      refine ⟨102984961087365270742378457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68656640724910180494918971 102984961087365270742378457)
      ·
        refine ⟨77238720815523953056783843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102984961087365270742378457 77238720815523953056783843)
        ·
          refine ⟨115858081223285929585175765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77238720815523953056783843 115858081223285929585175765)
          ·
            refine ⟨2715423778670763974652557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115858081223285929585175765 2715423778670763974652557)
            ·
              refine ⟨1018283917001536490494709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2715423778670763974652557 1018283917001536490494709)
              ·
                refine ⟨95464117218894045983879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018283917001536490494709 95464117218894045983879)
                ·
                  rfl

theorem cell21_1254931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].length) (baseStart_1254931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254931 prefixEnd_1254931 := by exact prefixLift 1254931
  have htrace : WordTrace (prefixWord ++ tailWord_1254931) baseStart_1254931 baseEnd_1254931 := by
    simpa [prefixWord, tailWord_1254931, baseEnd_1254931] using wordTrace_append hprefix tailTrace_1254931
  have hstable : (prefixWord ++ tailWord_1254931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254931).length < 2 ^ (prefixWord ++ tailWord_1254931).sum := by decide
  have hdescent : baseEnd_1254931 < baseStart_1254931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254982 : List Nat := [6, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1254982 : Nat := 118140960795 + 1254982 * 2 ^ 59
def prefixEnd_1254982 : Nat := 4983230072969 + 3 ^ 40 * 1254982 * 2
def baseEnd_1254982 : Nat := 95467996850505794200511

theorem tailTrace_1254982 : CollatzResearch.WordTrace tailWord_1254982 prefixEnd_1254982 95467996850505794200511 := by
  unfold tailWord_1254982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430404810606938209584975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30515302626281348471146133 1430404810606938209584975)
  ·
    refine ⟨2145607215910407314377463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430404810606938209584975 2145607215910407314377463)
    ·
      refine ⟨3218410823865610971566195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145607215910407314377463 3218410823865610971566195)
      ·
        refine ⟨4827616235798416457349293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218410823865610971566195 4827616235798416457349293)
        ·
          refine ⟨1810356088424406171505985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4827616235798416457349293 1810356088424406171505985)
          ·
            refine ⟨1357767066318304628629489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810356088424406171505985 1357767066318304628629489)
            ·
              refine ⟨1018325299738728471472117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357767066318304628629489 1018325299738728471472117)
              ·
                refine ⟨95467996850505794200511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018325299738728471472117 95467996850505794200511)
                ·
                  rfl

theorem cell21_1254982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1254982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1254982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1254982 prefixEnd_1254982 := by exact prefixLift 1254982
  have htrace : WordTrace (prefixWord ++ tailWord_1254982) baseStart_1254982 baseEnd_1254982 := by
    simpa [prefixWord, tailWord_1254982, baseEnd_1254982] using wordTrace_append hprefix tailTrace_1254982
  have hstable : (prefixWord ++ tailWord_1254982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254982).length < 2 ^ (prefixWord ++ tailWord_1254982).sum := by decide
  have hdescent : baseEnd_1254982 < baseStart_1254982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255072 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_1255072 : Nat := 118140960795 + 1255072 * 2 ^ 59
def prefixEnd_1255072 : Nat := 4983230072969 + 3 ^ 40 * 1255072 * 2
def baseEnd_1255072 : Nat := 286424529777697226101349

theorem tailTrace_1255072 : CollatzResearch.WordTrace tailWord_1255072 prefixEnd_1255072 286424529777697226101349 := by
  unfold tailWord_1255072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888118254547984038747735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30517491006063978718330313 22888118254547984038747735)
  ·
    refine ⟨34332177381821976058121603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888118254547984038747735 34332177381821976058121603)
    ·
      refine ⟨51498266072732964087182405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34332177381821976058121603 51498266072732964087182405)
      ·
        refine ⟨9655924888637430766346701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51498266072732964087182405 9655924888637430766346701)
        ·
          refine ⟨3620971833239036537380013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9655924888637430766346701 3620971833239036537380013)
          ·
            refine ⟨1357864437464638701517505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620971833239036537380013 1357864437464638701517505)
            ·
              refine ⟨1018398328098479026138129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357864437464638701517505 1018398328098479026138129)
              ·
                refine ⟨763798746073859269603597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018398328098479026138129 763798746073859269603597)
                ·
                  refine ⟨286424529777697226101349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763798746073859269603597 286424529777697226101349)
                  ·
                    rfl

theorem cell21_1255072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_1255072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255072 prefixEnd_1255072 := by exact prefixLift 1255072
  have htrace : WordTrace (prefixWord ++ tailWord_1255072) baseStart_1255072 baseEnd_1255072 := by
    simpa [prefixWord, tailWord_1255072, baseEnd_1255072] using wordTrace_append hprefix tailTrace_1255072
  have hstable : (prefixWord ++ tailWord_1255072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255072).length < 2 ^ (prefixWord ++ tailWord_1255072).sum := by decide
  have hdescent : baseEnd_1255072 < baseStart_1255072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255106 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1255106 : Nat := 118140960795 + 1255106 * 2 ^ 59
def prefixEnd_1255106 : Nat := 4983230072969 + 3 ^ 40 * 1255106 * 2
def baseEnd_1255106 : Nat := 286432289040920722534613

theorem tailTrace_1255106 : CollatzResearch.WordTrace tailWord_1255106 prefixEnd_1255106 286432289040920722534613 := by
  unfold tailWord_1255106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444369147743197971058293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30518317727315194589488781 11444369147743197971058293)
  ·
    refine ⟨1072909607600924809786715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11444369147743197971058293 1072909607600924809786715)
    ·
      refine ⟨1609364411401387214680073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072909607600924809786715 1609364411401387214680073)
      ·
        refine ⟨1207023308551040411010055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609364411401387214680073 1207023308551040411010055)
        ·
          refine ⟨1810534962826560616515083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207023308551040411010055 1810534962826560616515083)
          ·
            refine ⟨2715802444239840924772625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810534962826560616515083 2715802444239840924772625)
            ·
              refine ⟨2036851833179880693579469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715802444239840924772625 2036851833179880693579469)
              ·
                refine ⟨763819437442455260092301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036851833179880693579469 763819437442455260092301)
                ·
                  refine ⟨286432289040920722534613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763819437442455260092301 286432289040920722534613)
                  ·
                    rfl

theorem cell21_1255106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1255106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255106 prefixEnd_1255106 := by exact prefixLift 1255106
  have htrace : WordTrace (prefixWord ++ tailWord_1255106) baseStart_1255106 baseEnd_1255106 := by
    simpa [prefixWord, tailWord_1255106, baseEnd_1255106] using wordTrace_append hprefix tailTrace_1255106
  have hstable : (prefixWord ++ tailWord_1255106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255106).length < 2 ^ (prefixWord ++ tailWord_1255106).sum := by decide
  have hdescent : baseEnd_1255106 < baseStart_1255106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255111 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_1255111 : Nat := 118140960795 + 1255111 * 2 ^ 59
def prefixEnd_1255111 : Nat := 4983230072969 + 3 ^ 40 * 1255111 * 2
def baseEnd_1255111 : Nat := 286433430109041824951269

theorem tailTrace_1255111 : CollatzResearch.WordTrace tailWord_1255111 prefixEnd_1255111 286433430109041824951269 := by
  unfold tailWord_1255111
  simp only [CollatzResearch.WordTrace]
  refine ⟨45777658955954677738165187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30518439303969785158776791 45777658955954677738165187)
  ·
    refine ⟨68666488433932016607247781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45777658955954677738165187 68666488433932016607247781)
    ·
      refine ⟨12874966581362253113858959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68666488433932016607247781 12874966581362253113858959)
      ·
        refine ⟨19312449872043379670788439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12874966581362253113858959 19312449872043379670788439)
        ·
          refine ⟨28968674808065069506182659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19312449872043379670788439 28968674808065069506182659)
          ·
            refine ⟨43453012212097604259273989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28968674808065069506182659 43453012212097604259273989)
            ·
              refine ⟨8147439789768300798613873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43453012212097604259273989 8147439789768300798613873)
              ·
                refine ⟨6110579842326225598960405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147439789768300798613873 6110579842326225598960405)
                ·
                  refine ⟨286433430109041824951269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6110579842326225598960405 286433430109041824951269)
                  ·
                    rfl

theorem cell21_1255111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_1255111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255111 prefixEnd_1255111 := by exact prefixLift 1255111
  have htrace : WordTrace (prefixWord ++ tailWord_1255111) baseStart_1255111 baseEnd_1255111 := by
    simpa [prefixWord, tailWord_1255111, baseEnd_1255111] using wordTrace_append hprefix tailTrace_1255111
  have hstable : (prefixWord ++ tailWord_1255111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255111).length < 2 ^ (prefixWord ++ tailWord_1255111).sum := by decide
  have hdescent : baseEnd_1255111 < baseStart_1255111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255218 : List Nat := [3, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1255218 : Nat := 118140960795 + 1255218 * 2 ^ 59
def prefixEnd_1255218 : Nat := 4983230072969 + 3 ^ 40 * 1255218 * 2
def baseEnd_1255218 : Nat := 95485949655611138889239

theorem tailTrace_1255218 : CollatzResearch.WordTrace tailWord_1255218 prefixEnd_1255218 95485949655611138889239 := by
  unfold tailWord_1255218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445390391641758753077577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30521041044378023341540205 11445390391641758753077577)
  ·
    refine ⟨8584042793731319064808183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11445390391641758753077577 8584042793731319064808183)
    ·
      refine ⟨12876064190596978597212275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584042793731319064808183 12876064190596978597212275)
      ·
        refine ⟨19314096285895467895818413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12876064190596978597212275 19314096285895467895818413)
        ·
          refine ⟨7242786107210800460931905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19314096285895467895818413 7242786107210800460931905)
          ·
            refine ⟨5432089580408100345698929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7242786107210800460931905 5432089580408100345698929)
            ·
              refine ⟨4074067185306075259274197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432089580408100345698929 4074067185306075259274197)
              ·
                refine ⟨95485949655611138889239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4074067185306075259274197 95485949655611138889239)
                ·
                  rfl

theorem cell21_1255218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1255218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255218 prefixEnd_1255218 := by exact prefixLift 1255218
  have htrace : WordTrace (prefixWord ++ tailWord_1255218) baseStart_1255218 baseEnd_1255218 := by
    simpa [prefixWord, tailWord_1255218, baseEnd_1255218] using wordTrace_append hprefix tailTrace_1255218
  have hstable : (prefixWord ++ tailWord_1255218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255218).length < 2 ^ (prefixWord ++ tailWord_1255218).sum := by decide
  have hdescent : baseEnd_1255218 < baseStart_1255218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255238 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1255238 : Nat := 118140960795 + 1255238 * 2 ^ 59
def prefixEnd_1255238 : Nat := 4983230072969 + 3 ^ 40 * 1255238 * 2
def baseEnd_1255238 : Nat := 286462413239317826334343

theorem tailTrace_1255238 : CollatzResearch.WordTrace tailWord_1255238 prefixEnd_1255238 286462413239317826334343 := by
  unfold tailWord_1255238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430696594577955575876199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30521527350996385618692245 1430696594577955575876199)
  ·
    refine ⟨2146044891866933363814299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430696594577955575876199 2146044891866933363814299)
    ·
      refine ⟨3219067337800400045721449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146044891866933363814299 3219067337800400045721449)
      ·
        refine ⟨2414300503350300034291087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219067337800400045721449 2414300503350300034291087)
        ·
          refine ⟨3621450755025450051436631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414300503350300034291087 3621450755025450051436631)
          ·
            refine ⟨5432176132538175077154947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621450755025450051436631 5432176132538175077154947)
            ·
              refine ⟨8148264198807262615732421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5432176132538175077154947 8148264198807262615732421)
              ·
                refine ⟨1527799537276361740449829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8148264198807262615732421 1527799537276361740449829)
                ·
                  refine ⟨286462413239317826334343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527799537276361740449829 286462413239317826334343)
                  ·
                    rfl

theorem cell21_1255238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1255238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255238 prefixEnd_1255238 := by exact prefixLift 1255238
  have htrace : WordTrace (prefixWord ++ tailWord_1255238) baseStart_1255238 baseEnd_1255238 := by
    simpa [prefixWord, tailWord_1255238, baseEnd_1255238] using wordTrace_append hprefix tailTrace_1255238
  have hstable : (prefixWord ++ tailWord_1255238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255238).length < 2 ^ (prefixWord ++ tailWord_1255238).sum := by decide
  have hdescent : baseEnd_1255238 < baseStart_1255238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255266 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1255266 : Nat := 118140960795 + 1255266 * 2 ^ 59
def prefixEnd_1255266 : Nat := 4983230072969 + 3 ^ 40 * 1255266 * 2
def baseEnd_1255266 : Nat := 286468803220795999867619

theorem tailTrace_1255266 : CollatzResearch.WordTrace tailWord_1255266 prefixEnd_1255266 286468803220795999867619 := by
  unfold tailWord_1255266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445828067598284802514413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30522208180262092806705101 11445828067598284802514413)
  ·
    refine ⟨4292185525349356800942905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11445828067598284802514413 4292185525349356800942905)
    ·
      refine ⟨3219139144012017600707179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4292185525349356800942905 3219139144012017600707179)
      ·
        refine ⟨4828708716018026401060769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219139144012017600707179 4828708716018026401060769)
        ·
          refine ⟨3621531537013519800795577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4828708716018026401060769 3621531537013519800795577)
          ·
            refine ⟨2716148652760139850596683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621531537013519800795577 2716148652760139850596683)
            ·
              refine ⟨4074222979140209775895025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716148652760139850596683 4074222979140209775895025)
              ·
                refine ⟨3055667234355157331921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074222979140209775895025 3055667234355157331921269)
                ·
                  refine ⟨286468803220795999867619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3055667234355157331921269 286468803220795999867619)
                  ·
                    rfl

theorem cell21_1255266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1255266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255266 prefixEnd_1255266 := by exact prefixLift 1255266
  have htrace : WordTrace (prefixWord ++ tailWord_1255266) baseStart_1255266 baseEnd_1255266 := by
    simpa [prefixWord, tailWord_1255266, baseEnd_1255266] using wordTrace_append hprefix tailTrace_1255266
  have hstable : (prefixWord ++ tailWord_1255266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255266).length < 2 ^ (prefixWord ++ tailWord_1255266).sum := by decide
  have hdescent : baseEnd_1255266 < baseStart_1255266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255297 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_1255297 : Nat := 118140960795 + 1255297 * 2 ^ 59
def prefixEnd_1255297 : Nat := 4983230072969 + 3 ^ 40 * 1255297 * 2
def baseEnd_1255297 : Nat := 286475877843146834850889

theorem tailTrace_1255297 : CollatzResearch.WordTrace tailWord_1255297 prefixEnd_1255297 286475877843146834850889 := by
  unfold tailWord_1255297
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784442933280831504436145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30522961955520554336290763 45784442933280831504436145)
  ·
    refine ⟨34338332199960623628327109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45784442933280831504436145 34338332199960623628327109)
    ·
      refine ⟨6438437287492616930311333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34338332199960623628327109 6438437287492616930311333)
      ·
        refine ⟨1207206991404865674433375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6438437287492616930311333 1207206991404865674433375)
        ·
          refine ⟨1810810487107298511650063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207206991404865674433375 1810810487107298511650063)
          ·
            refine ⟨2716215730660947767475095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810810487107298511650063 2716215730660947767475095)
            ·
              refine ⟨4074323595991421651212643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716215730660947767475095 4074323595991421651212643)
              ·
                refine ⟨6111485393987132476818965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074323595991421651212643 6111485393987132476818965)
                ·
                  refine ⟨286475877843146834850889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6111485393987132476818965 286475877843146834850889)
                  ·
                    rfl

theorem cell21_1255297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_1255297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255297 prefixEnd_1255297 := by exact prefixLift 1255297
  have htrace : WordTrace (prefixWord ++ tailWord_1255297) baseStart_1255297 baseEnd_1255297 := by
    simpa [prefixWord, tailWord_1255297, baseEnd_1255297] using wordTrace_append hprefix tailTrace_1255297
  have hstable : (prefixWord ++ tailWord_1255297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255297).length < 2 ^ (prefixWord ++ tailWord_1255297).sum := by decide
  have hdescent : baseEnd_1255297 < baseStart_1255297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255314 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1255314 : Nat := 118140960795 + 1255314 * 2 ^ 59
def prefixEnd_1255314 : Nat := 4983230072969 + 3 ^ 40 * 1255314 * 2
def baseEnd_1255314 : Nat := 286479757474758583067521

theorem tailTrace_1255314 : CollatzResearch.WordTrace tailWord_1255314 prefixEnd_1255314 286479757474758583067521 := by
  unfold tailWord_1255314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446265743554810851951249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30523375316146162271869997 11446265743554810851951249)
  ·
    refine ⟨8584699307666108138963437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11446265743554810851951249 8584699307666108138963437)
    ·
      refine ⟨3219262240374790552111289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8584699307666108138963437 3219262240374790552111289)
      ·
        refine ⟨2414446680281092914083467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219262240374790552111289 2414446680281092914083467)
        ·
          refine ⟨3621670020421639371125201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414446680281092914083467 3621670020421639371125201)
          ·
            refine ⟨2716252515316229528343901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621670020421639371125201 2716252515316229528343901)
            ·
              refine ⟨1018594693243586073128963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2716252515316229528343901 1018594693243586073128963)
              ·
                refine ⟨1527892039865379109693445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018594693243586073128963 1527892039865379109693445)
                ·
                  refine ⟨286479757474758583067521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527892039865379109693445 286479757474758583067521)
                  ·
                    rfl

theorem cell21_1255314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1255314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255314 prefixEnd_1255314 := by exact prefixLift 1255314
  have htrace : WordTrace (prefixWord ++ tailWord_1255314) baseStart_1255314 baseEnd_1255314 := by
    simpa [prefixWord, tailWord_1255314, baseEnd_1255314] using wordTrace_append hprefix tailTrace_1255314
  have hstable : (prefixWord ++ tailWord_1255314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255314).length < 2 ^ (prefixWord ++ tailWord_1255314).sum := by decide
  have hdescent : baseEnd_1255314 < baseStart_1255314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255325 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1255325 : Nat := 118140960795 + 1255325 * 2 ^ 59
def prefixEnd_1255325 : Nat := 4983230072969 + 3 ^ 40 * 1255325 * 2
def baseEnd_1255325 : Nat := 286482267824625008384165

theorem tailTrace_1255325 : CollatzResearch.WordTrace tailWord_1255325 prefixEnd_1255325 286482267824625008384165 := by
  unfold tailWord_1255325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45785464177179392286455429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30523642784786261524303619 45785464177179392286455429)
  ·
    refine ⟨8584774533221136053710393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45785464177179392286455429 8584774533221136053710393)
    ·
      refine ⟨6438580899915852040282795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8584774533221136053710393 6438580899915852040282795)
      ·
        refine ⟨9657871349873778060424193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6438580899915852040282795 9657871349873778060424193)
        ·
          refine ⟨7243403512405333545318145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9657871349873778060424193 7243403512405333545318145)
          ·
            refine ⟨5432552634304000158988609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7243403512405333545318145 5432552634304000158988609)
            ·
              refine ⟨4074414475728000119241457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432552634304000158988609 4074414475728000119241457)
              ·
                refine ⟨3055810856796000089431093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074414475728000119241457 3055810856796000089431093)
                ·
                  refine ⟨286482267824625008384165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3055810856796000089431093 286482267824625008384165)
                  ·
                    rfl

theorem cell21_1255325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1255325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255325 prefixEnd_1255325 := by exact prefixLift 1255325
  have htrace : WordTrace (prefixWord ++ tailWord_1255325) baseStart_1255325 baseEnd_1255325 := by
    simpa [prefixWord, tailWord_1255325, baseEnd_1255325] using wordTrace_append hprefix tailTrace_1255325
  have hstable : (prefixWord ++ tailWord_1255325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255325).length < 2 ^ (prefixWord ++ tailWord_1255325).sum := by decide
  have hdescent : baseEnd_1255325 < baseStart_1255325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255384 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_1255384 : Nat := 118140960795 + 1255384 * 2 ^ 59
def prefixEnd_1255384 : Nat := 4983230072969 + 3 ^ 40 * 1255384 * 2
def baseEnd_1255384 : Nat := 286495732428454016900711

theorem tailTrace_1255384 : CollatzResearch.WordTrace tailWord_1255384 prefixEnd_1255384 286495732428454016900711 := by
  unfold tailWord_1255384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893808041982822681426603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30525077389310430241902137 22893808041982822681426603)
  ·
    refine ⟨34340712062974234022139905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893808041982822681426603 34340712062974234022139905)
    ·
      refine ⟨25755534047230675516604929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34340712062974234022139905 25755534047230675516604929)
      ·
        refine ⟨19316650535423006637453697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25755534047230675516604929 19316650535423006637453697)
        ·
          refine ⟨14487487901567254978090273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19316650535423006637453697 14487487901567254978090273)
          ·
            refine ⟨10865615926175441233567705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14487487901567254978090273 10865615926175441233567705)
            ·
              refine ⟨8149211944631580925175779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10865615926175441233567705 8149211944631580925175779)
              ·
                refine ⟨12223817916947371387763669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149211944631580925175779 12223817916947371387763669)
                ·
                  refine ⟨286495732428454016900711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12223817916947371387763669 286495732428454016900711)
                  ·
                    rfl

theorem cell21_1255384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_1255384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255384 prefixEnd_1255384 := by exact prefixLift 1255384
  have htrace : WordTrace (prefixWord ++ tailWord_1255384) baseStart_1255384 baseEnd_1255384 := by
    simpa [prefixWord, tailWord_1255384, baseEnd_1255384] using wordTrace_append hprefix tailTrace_1255384
  have hstable : (prefixWord ++ tailWord_1255384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255384).length < 2 ^ (prefixWord ++ tailWord_1255384).sum := by decide
  have hdescent : baseEnd_1255384 < baseStart_1255384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255463 : List Nat := [1, 1, 7, 1, 2, 1, 8]
def baseStart_1255463 : Nat := 118140960795 + 1255463 * 2 ^ 59
def prefixEnd_1255463 : Nat := 4983230072969 + 3 ^ 40 * 1255463 * 2
def baseEnd_1255463 : Nat := 31834862367196381675987

theorem tailTrace_1255463 : CollatzResearch.WordTrace tailWord_1255463 prefixEnd_1255463 31834862367196381675987 := by
  unfold tailWord_1255463
  simp only [CollatzResearch.WordTrace]
  refine ⟨45790497450679441854979043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30526998300452961236652695 45790497450679441854979043)
  ·
    refine ⟨68685746176019162782468565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45790497450679441854979043 68685746176019162782468565)
    ·
      refine ⟨1609822176000449127714107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 68685746176019162782468565 1609822176000449127714107)
      ·
        refine ⟨2414733264000673691571161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609822176000449127714107 2414733264000673691571161)
        ·
          refine ⟨1811049948000505268678371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414733264000673691571161 1811049948000505268678371)
          ·
            refine ⟨2716574922000757903017557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811049948000505268678371 2716574922000757903017557)
            ·
              refine ⟨31834862367196381675987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2716574922000757903017557 31834862367196381675987)
              ·
                rfl

theorem cell21_1255463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 8].length) (baseStart_1255463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255463 prefixEnd_1255463 := by exact prefixLift 1255463
  have htrace : WordTrace (prefixWord ++ tailWord_1255463) baseStart_1255463 baseEnd_1255463 := by
    simpa [prefixWord, tailWord_1255463, baseEnd_1255463] using wordTrace_append hprefix tailTrace_1255463
  have hstable : (prefixWord ++ tailWord_1255463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255463).length < 2 ^ (prefixWord ++ tailWord_1255463).sum := by decide
  have hdescent : baseEnd_1255463 < baseStart_1255463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255494 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1255494 : Nat := 118140960795 + 1255494 * 2 ^ 59
def prefixEnd_1255494 : Nat := 4983230072969 + 3 ^ 40 * 1255494 * 2
def baseEnd_1255494 : Nat := 286520835927118270067153

theorem tailTrace_1255494 : CollatzResearch.WordTrace tailWord_1255494 prefixEnd_1255494 286520835927118270067153 := by
  unfold tailWord_1255494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430988378548972942167423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30527752075711422766238357 1430988378548972942167423)
  ·
    refine ⟨2146482567823459413251135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430988378548972942167423 2146482567823459413251135)
    ·
      refine ⟨3219723851735189119876703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146482567823459413251135 3219723851735189119876703)
      ·
        refine ⟨4829585777602783679815055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219723851735189119876703 4829585777602783679815055)
        ·
          refine ⟨7244378666404175519722583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829585777602783679815055 7244378666404175519722583)
          ·
            refine ⟨10866567999606263279583875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244378666404175519722583 10866567999606263279583875)
            ·
              refine ⟨16299851999409394919375813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866567999606263279583875 16299851999409394919375813)
              ·
                refine ⟨3056222249889261547382965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16299851999409394919375813 3056222249889261547382965)
                ·
                  refine ⟨286520835927118270067153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056222249889261547382965 286520835927118270067153)
                  ·
                    rfl

theorem cell21_1255494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1255494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255494 prefixEnd_1255494 := by exact prefixLift 1255494
  have htrace : WordTrace (prefixWord ++ tailWord_1255494) baseStart_1255494 baseEnd_1255494 := by
    simpa [prefixWord, tailWord_1255494, baseEnd_1255494] using wordTrace_append hprefix tailTrace_1255494
  have hstable : (prefixWord ++ tailWord_1255494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255494).length < 2 ^ (prefixWord ++ tailWord_1255494).sum := by decide
  have hdescent : baseEnd_1255494 < baseStart_1255494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255542 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1255542 : Nat := 118140960795 + 1255542 * 2 ^ 59
def prefixEnd_1255542 : Nat := 4983230072969 + 3 ^ 40 * 1255542 * 2
def baseEnd_1255542 : Nat := 286531790181080853267055

theorem tailTrace_1255542 : CollatzResearch.WordTrace tailWord_1255542 prefixEnd_1255542 286531790181080853267055 := by
  unfold tailWord_1255542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862086176087077396694055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30528919211595492231403253 2862086176087077396694055)
  ·
    refine ⟨4293129264130616095041083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2862086176087077396694055 4293129264130616095041083)
    ·
      refine ⟨6439693896195924142561625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293129264130616095041083 6439693896195924142561625)
      ·
        refine ⟨4829770422146943106921219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6439693896195924142561625 4829770422146943106921219)
        ·
          refine ⟨7244655633220414660381829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829770422146943106921219 7244655633220414660381829)
          ·
            refine ⟨1358372931228827748821593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7244655633220414660381829 1358372931228827748821593)
            ·
              refine ⟨1018779698421620811616195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358372931228827748821593 1018779698421620811616195)
              ·
                refine ⟨1528169547632431217424293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018779698421620811616195 1528169547632431217424293)
                ·
                  refine ⟨286531790181080853267055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528169547632431217424293 286531790181080853267055)
                  ·
                    rfl

theorem cell21_1255542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1255542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255542 prefixEnd_1255542 := by exact prefixLift 1255542
  have htrace : WordTrace (prefixWord ++ tailWord_1255542) baseStart_1255542 baseEnd_1255542 := by
    simpa [prefixWord, tailWord_1255542, baseEnd_1255542] using wordTrace_append hprefix tailTrace_1255542
  have hstable : (prefixWord ++ tailWord_1255542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255542).length < 2 ^ (prefixWord ++ tailWord_1255542).sum := by decide
  have hdescent : baseEnd_1255542 < baseStart_1255542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255570 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1255570 : Nat := 118140960795 + 1255570 * 2 ^ 59
def prefixEnd_1255570 : Nat := 4983230072969 + 3 ^ 40 * 1255570 * 2
def baseEnd_1255570 : Nat := 286538180162559026800331

theorem tailTrace_1255570 : CollatzResearch.WordTrace tailWord_1255570 prefixEnd_1255570 286538180162559026800331 := by
  unfold tailWord_1255570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448600015322949782281041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30529600040861199419416109 11448600015322949782281041)
  ·
    refine ⟨8586450011492212336710781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11448600015322949782281041 8586450011492212336710781)
    ·
      refine ⟨3219918754309579626266543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8586450011492212336710781 3219918754309579626266543)
      ·
        refine ⟨4829878131464369439399815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219918754309579626266543 4829878131464369439399815)
        ·
          refine ⟨7244817197196554159099723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829878131464369439399815 7244817197196554159099723)
          ·
            refine ⟨10867225795794831238649585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244817197196554159099723 10867225795794831238649585)
            ·
              refine ⟨8150419346846123428987189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10867225795794831238649585 8150419346846123428987189)
              ·
                refine ⟨764101813766824071467549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8150419346846123428987189 764101813766824071467549)
                ·
                  refine ⟨286538180162559026800331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764101813766824071467549 286538180162559026800331)
                  ·
                    rfl

theorem cell21_1255570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1255570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255570 prefixEnd_1255570 := by exact prefixLift 1255570
  have htrace : WordTrace (prefixWord ++ tailWord_1255570) baseStart_1255570 baseEnd_1255570 := by
    simpa [prefixWord, tailWord_1255570, baseEnd_1255570] using wordTrace_append hprefix tailTrace_1255570
  have hstable : (prefixWord ++ tailWord_1255570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255570).length < 2 ^ (prefixWord ++ tailWord_1255570).sum := by decide
  have hdescent : baseEnd_1255570 < baseStart_1255570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255581 : List Nat := [1, 4, 2, 1, 1, 12]
def baseStart_1255581 : Nat := 118140960795 + 1255581 * 2 ^ 59
def prefixEnd_1255581 : Nat := 4983230072969 + 3 ^ 40 * 1255581 * 2
def baseEnd_1255581 : Nat := 10612618167126868596925

theorem tailTrace_1255581 : CollatzResearch.WordTrace tailWord_1255581 prefixEnd_1255581 10612618167126868596925 := by
  unfold tailWord_1255581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45794801264251948007774597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30529867509501298671849731 45794801264251948007774597)
  ·
    refine ⟨8586525237047240251457737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45794801264251948007774597 8586525237047240251457737)
    ·
      refine ⟨6439893927785430188593303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8586525237047240251457737 6439893927785430188593303)
      ·
        refine ⟨9659840891678145282889955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6439893927785430188593303 9659840891678145282889955)
        ·
          refine ⟨14489761337517217924334933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659840891678145282889955 14489761337517217924334933)
          ·
            refine ⟨10612618167126868596925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14489761337517217924334933 10612618167126868596925)
            ·
              rfl

theorem cell21_1255581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 12].length) (baseStart_1255581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255581 prefixEnd_1255581 := by exact prefixLift 1255581
  have htrace : WordTrace (prefixWord ++ tailWord_1255581) baseStart_1255581 baseEnd_1255581 := by
    simpa [prefixWord, tailWord_1255581, baseEnd_1255581] using wordTrace_append hprefix tailTrace_1255581
  have hstable : (prefixWord ++ tailWord_1255581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255581).length < 2 ^ (prefixWord ++ tailWord_1255581).sum := by decide
  have hdescent : baseEnd_1255581 < baseStart_1255581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255584 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1255584 : Nat := 118140960795 + 1255584 * 2 ^ 59
def prefixEnd_1255584 : Nat := 4983230072969 + 3 ^ 40 * 1255584 * 2
def baseEnd_1255584 : Nat := 286541375153298113566969

theorem tailTrace_1255584 : CollatzResearch.WordTrace tailWord_1255584 prefixEnd_1255584 286541375153298113566969 := by
  unfold tailWord_1255584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897455341620539760066903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30529940455494053013422537 22897455341620539760066903)
  ·
    refine ⟨34346183012430809640100355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22897455341620539760066903 34346183012430809640100355)
    ·
      refine ⟨51519274518646214460150533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34346183012430809640100355 51519274518646214460150533)
      ·
        refine ⟨9659863972246165211278225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51519274518646214460150533 9659863972246165211278225)
        ·
          refine ⟨7244897979184623908458669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9659863972246165211278225 7244897979184623908458669)
          ·
            refine ⟨2716836742194233965672001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7244897979184623908458669 2716836742194233965672001)
            ·
              refine ⟨2037627556645675474254001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716836742194233965672001 2037627556645675474254001)
              ·
                refine ⟨1528220667484256605690501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037627556645675474254001 1528220667484256605690501)
                ·
                  refine ⟨286541375153298113566969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528220667484256605690501 286541375153298113566969)
                  ·
                    rfl

theorem cell21_1255584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1255584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255584 prefixEnd_1255584 := by exact prefixLift 1255584
  have htrace : WordTrace (prefixWord ++ tailWord_1255584) baseStart_1255584 baseEnd_1255584 := by
    simpa [prefixWord, tailWord_1255584, baseEnd_1255584] using wordTrace_append hprefix tailTrace_1255584
  have hstable : (prefixWord ++ tailWord_1255584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255584).length < 2 ^ (prefixWord ++ tailWord_1255584).sum := by decide
  have hdescent : baseEnd_1255584 < baseStart_1255584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255604 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1255604 : Nat := 118140960795 + 1255604 * 2 ^ 59
def prefixEnd_1255604 : Nat := 4983230072969 + 3 ^ 40 * 1255604 * 2
def baseEnd_1255604 : Nat := 286545939425782523233595

theorem tailTrace_1255604 : CollatzResearch.WordTrace tailWord_1255604 prefixEnd_1255604 286545939425782523233595 := by
  unfold tailWord_1255604
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897820071584311467930933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30530426762112415290574577 22897820071584311467930933)
  ·
    refine ⟨2146670631711029200118525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22897820071584311467930933 2146670631711029200118525)
    ·
      refine ⟨805001486891635950044447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2146670631711029200118525 805001486891635950044447)
      ·
        refine ⟨1207502230337453925066671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805001486891635950044447 1207502230337453925066671)
        ·
          refine ⟨1811253345506180887600007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207502230337453925066671 1811253345506180887600007)
          ·
            refine ⟨2716880018259271331400011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811253345506180887600007 2716880018259271331400011)
            ·
              refine ⟨4075320027388906997100017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716880018259271331400011 4075320027388906997100017)
              ·
                refine ⟨3056490020541680247825013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075320027388906997100017 3056490020541680247825013)
                ·
                  refine ⟨286545939425782523233595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056490020541680247825013 286545939425782523233595)
                  ·
                    rfl

theorem cell21_1255604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1255604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255604 prefixEnd_1255604 := by exact prefixLift 1255604
  have htrace : WordTrace (prefixWord ++ tailWord_1255604) baseStart_1255604 baseEnd_1255604 := by
    simpa [prefixWord, tailWord_1255604, baseEnd_1255604] using wordTrace_append hprefix tailTrace_1255604
  have hstable : (prefixWord ++ tailWord_1255604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255604).length < 2 ^ (prefixWord ++ tailWord_1255604).sum := by decide
  have hdescent : baseEnd_1255604 < baseStart_1255604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255660 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1255660 : Nat := 118140960795 + 1255660 * 2 ^ 59
def prefixEnd_1255660 : Nat := 4983230072969 + 3 ^ 40 * 1255660 * 2
def baseEnd_1255660 : Nat := 286558719388738870300147

theorem tailTrace_1255660 : CollatzResearch.WordTrace tailWord_1255660 prefixEnd_1255660 286558719388738870300147 := by
  unfold tailWord_1255660
  simp only [CollatzResearch.WordTrace]
  refine ⟨22898841315482872249950217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30531788420643829666600289 22898841315482872249950217)
  ·
    refine ⟨17174130986612154187462663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22898841315482872249950217 17174130986612154187462663)
    ·
      refine ⟨25761196479918231281193995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17174130986612154187462663 25761196479918231281193995)
      ·
        refine ⟨38641794719877346921790993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25761196479918231281193995 38641794719877346921790993)
        ·
          refine ⟨28981346039908010191343245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38641794719877346921790993 28981346039908010191343245)
          ·
            refine ⟨10868004764965503821753717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28981346039908010191343245 10868004764965503821753717)
            ·
              refine ⟨1018875446715515983289411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10868004764965503821753717 1018875446715515983289411)
              ·
                refine ⟨1528313170073273974934117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018875446715515983289411 1528313170073273974934117)
                ·
                  refine ⟨286558719388738870300147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528313170073273974934117 286558719388738870300147)
                  ·
                    rfl

theorem cell21_1255660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1255660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255660 prefixEnd_1255660 := by exact prefixLift 1255660
  have htrace : WordTrace (prefixWord ++ tailWord_1255660) baseStart_1255660 baseEnd_1255660 := by
    simpa [prefixWord, tailWord_1255660, baseEnd_1255660] using wordTrace_append hprefix tailTrace_1255660
  have hstable : (prefixWord ++ tailWord_1255660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255660).length < 2 ^ (prefixWord ++ tailWord_1255660).sum := by decide
  have hdescent : baseEnd_1255660 < baseStart_1255660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255674 : List Nat := [3, 1, 1, 1, 1, 5, 4, 5]
def baseStart_1255674 : Nat := 118140960795 + 1255674 * 2 ^ 59
def prefixEnd_1255674 : Nat := 4983230072969 + 3 ^ 40 * 1255674 * 2
def baseEnd_1255674 : Nat := 95520638126492652355595

theorem tailTrace_1255674 : CollatzResearch.WordTrace tailWord_1255674 prefixEnd_1255674 95520638126492652355595 := by
  unfold tailWord_1255674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449548313228756222727519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30532128835276683260606717 11449548313228756222727519)
  ·
    refine ⟨17174322469843134334091279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11449548313228756222727519 17174322469843134334091279)
    ·
      refine ⟨25761483704764701501136919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17174322469843134334091279 25761483704764701501136919)
      ·
        refine ⟨38642225557147052251705379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25761483704764701501136919 38642225557147052251705379)
        ·
          refine ⟨57963338335720578377558069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38642225557147052251705379 57963338335720578377558069)
          ·
            refine ⟨5434062968973804222896069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57963338335720578377558069 5434062968973804222896069)
            ·
              refine ⟨1018886806682588291793013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5434062968973804222896069 1018886806682588291793013)
              ·
                refine ⟨95520638126492652355595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018886806682588291793013 95520638126492652355595)
                ·
                  rfl

theorem cell21_1255674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_1255674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255674 prefixEnd_1255674 := by exact prefixLift 1255674
  have htrace : WordTrace (prefixWord ++ tailWord_1255674) baseStart_1255674 baseEnd_1255674 := by
    simpa [prefixWord, tailWord_1255674, baseEnd_1255674] using wordTrace_append hprefix tailTrace_1255674
  have hstable : (prefixWord ++ tailWord_1255674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255674).length < 2 ^ (prefixWord ++ tailWord_1255674).sum := by decide
  have hdescent : baseEnd_1255674 < baseStart_1255674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255733 : List Nat := [1, 3, 3, 1, 2, 1, 1, 9]
def baseStart_1255733 : Nat := 118140960795 + 1255733 * 2 ^ 59
def prefixEnd_1255733 : Nat := 4983230072969 + 3 ^ 40 * 1255733 * 2
def baseEnd_1255733 : Nat := 95525126327768988527777

theorem tailTrace_1255733 : CollatzResearch.WordTrace tailWord_1255733 prefixEnd_1255733 95525126327768988527777 := by
  unfold tailWord_1255733
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800345159701277967307853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30533563439800851978205235 45800345159701277967307853)
  ·
    refine ⟨17175129434887979237740445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45800345159701277967307853 17175129434887979237740445)
    ·
      refine ⟨6440673538082992214152667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17175129434887979237740445 6440673538082992214152667)
      ·
        refine ⟨9661010307124488321229001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440673538082992214152667 9661010307124488321229001)
        ·
          refine ⟨7245757730343366240921751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9661010307124488321229001 7245757730343366240921751)
          ·
            refine ⟨10868636595515049361382627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245757730343366240921751 10868636595515049361382627)
            ·
              refine ⟨16302954893272574042073941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868636595515049361382627 16302954893272574042073941)
              ·
                refine ⟨95525126327768988527777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16302954893272574042073941 95525126327768988527777)
                ·
                  rfl

theorem cell21_1255733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_1255733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255733 prefixEnd_1255733 := by exact prefixLift 1255733
  have htrace : WordTrace (prefixWord ++ tailWord_1255733) baseStart_1255733 baseEnd_1255733 := by
    simpa [prefixWord, tailWord_1255733, baseEnd_1255733] using wordTrace_append hprefix tailTrace_1255733
  have hstable : (prefixWord ++ tailWord_1255733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255733).length < 2 ^ (prefixWord ++ tailWord_1255733).sum := by decide
  have hdescent : baseEnd_1255733 < baseStart_1255733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255750 : List Nat := [6, 1, 1, 13]
def baseStart_1255750 : Nat := 118140960795 + 1255750 * 2 ^ 59
def prefixEnd_1255750 : Nat := 4983230072969 + 3 ^ 40 * 1255750 * 2
def baseEnd_1255750 : Nat := 1179338512818595530041

theorem tailTrace_1255750 : CollatzResearch.WordTrace tailWord_1255750 prefixEnd_1255750 1179338512818595530041 := by
  unfold tailWord_1255750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431280162519990308458647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30533976800426459913784469 1431280162519990308458647)
  ·
    refine ⟨2146920243779985462687971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431280162519990308458647 2146920243779985462687971)
    ·
      refine ⟨3220380365669978194031957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146920243779985462687971 3220380365669978194031957)
      ·
        refine ⟨1179338512818595530041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3220380365669978194031957 1179338512818595530041)
        ·
          rfl

theorem cell21_1255750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 13].length) (baseStart_1255750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255750 prefixEnd_1255750 := by exact prefixLift 1255750
  have htrace : WordTrace (prefixWord ++ tailWord_1255750) baseStart_1255750 baseEnd_1255750 := by
    simpa [prefixWord, tailWord_1255750, baseEnd_1255750] using wordTrace_append hprefix tailTrace_1255750
  have hstable : (prefixWord ++ tailWord_1255750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255750).length < 2 ^ (prefixWord ++ tailWord_1255750).sum := by decide
  have hdescent : baseEnd_1255750 < baseStart_1255750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255840 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_1255840 : Nat := 118140960795 + 1255840 * 2 ^ 59
def prefixEnd_1255840 : Nat := 4983230072969 + 3 ^ 40 * 1255840 * 2
def baseEnd_1255840 : Nat := 286599797841098557299779

theorem tailTrace_1255840 : CollatzResearch.WordTrace tailWord_1255840 prefixEnd_1255840 286599797841098557299779 := by
  unfold tailWord_1255840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902123885156817620726487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30536165180209090160968649 22902123885156817620726487)
  ·
    refine ⟨34353185827735226431089731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22902123885156817620726487 34353185827735226431089731)
    ·
      refine ⟨51529778741602839646634597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34353185827735226431089731 51529778741602839646634597)
      ·
        refine ⟨9661833514050532433743987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51529778741602839646634597 9661833514050532433743987)
        ·
          refine ⟨14492750271075798650615981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9661833514050532433743987 14492750271075798650615981)
          ·
            refine ⟨5434781351653424493980993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14492750271075798650615981 5434781351653424493980993)
            ·
              refine ⟨4076086013740068370485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434781351653424493980993 4076086013740068370485745)
              ·
                refine ⟨3057064510305051277864309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4076086013740068370485745 3057064510305051277864309)
                ·
                  refine ⟨286599797841098557299779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057064510305051277864309 286599797841098557299779)
                  ·
                    rfl

theorem cell21_1255840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_1255840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255840 prefixEnd_1255840 := by exact prefixLift 1255840
  have htrace : WordTrace (prefixWord ++ tailWord_1255840) baseStart_1255840 baseEnd_1255840 := by
    simpa [prefixWord, tailWord_1255840, baseEnd_1255840] using wordTrace_append hprefix tailTrace_1255840
  have hstable : (prefixWord ++ tailWord_1255840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255840).length < 2 ^ (prefixWord ++ tailWord_1255840).sum := by decide
  have hdescent : baseEnd_1255840 < baseStart_1255840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255860 : List Nat := [2, 5, 2, 2, 1, 2, 7]
def baseStart_1255860 : Nat := 118140960795 + 1255860 * 2 ^ 59
def prefixEnd_1255860 : Nat := 4983230072969 + 3 ^ 40 * 1255860 * 2
def baseEnd_1255860 : Nat := 31844929123731440774045

theorem tailTrace_1255860 : CollatzResearch.WordTrace tailWord_1255860 prefixEnd_1255860 31844929123731440774045 := by
  unfold tailWord_1255860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902488615120589328590517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30536651486827452438120689 22902488615120589328590517)
  ·
    refine ⟨2147108307667555249555361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22902488615120589328590517 2147108307667555249555361)
    ·
      refine ⟨1610331230750666437166521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2147108307667555249555361 1610331230750666437166521)
      ·
        refine ⟨1207748423062999827874891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1610331230750666437166521 1207748423062999827874891)
        ·
          refine ⟨1811622634594499741812337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207748423062999827874891 1811622634594499741812337)
          ·
            refine ⟨1358716975945874806359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1811622634594499741812337 1358716975945874806359253)
            ·
              refine ⟨31844929123731440774045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1358716975945874806359253 31844929123731440774045)
              ·
                rfl

theorem cell21_1255860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 7].length) (baseStart_1255860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255860 prefixEnd_1255860 := by exact prefixLift 1255860
  have htrace : WordTrace (prefixWord ++ tailWord_1255860) baseStart_1255860 baseEnd_1255860 := by
    simpa [prefixWord, tailWord_1255860, baseEnd_1255860] using wordTrace_append hprefix tailTrace_1255860
  have hstable : (prefixWord ++ tailWord_1255860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255860).length < 2 ^ (prefixWord ++ tailWord_1255860).sum := by decide
  have hdescent : baseEnd_1255860 < baseStart_1255860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255925 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 3]
def baseStart_1255925 : Nat := 118140960795 + 1255925 * 2 ^ 59
def prefixEnd_1255925 : Nat := 4983230072969 + 3 ^ 40 * 1255925 * 2
def baseEnd_1255925 : Nat := 286619195999157298382939

theorem tailTrace_1255925 : CollatzResearch.WordTrace tailWord_1255925 prefixEnd_1255925 286619195999157298382939 := by
  unfold tailWord_1255925
  simp only [CollatzResearch.WordTrace]
  refine ⟨45807347975005694758297229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30538231983337129838864819 45807347975005694758297229)
  ·
    refine ⟨17177755490627135534361461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45807347975005694758297229 17177755490627135534361461)
    ·
      refine ⟨1610414577246293956346387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17177755490627135534361461 1610414577246293956346387)
      ·
        refine ⟨2415621865869440934519581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610414577246293956346387 2415621865869440934519581)
        ·
          refine ⟨905858199701040350444843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2415621865869440934519581 905858199701040350444843)
          ·
            refine ⟨1358787299551560525667265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905858199701040350444843 1358787299551560525667265)
            ·
              refine ⟨1019090474663670394250449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358787299551560525667265 1019090474663670394250449)
              ·
                refine ⟨764317855997752795687837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019090474663670394250449 764317855997752795687837)
                ·
                  refine ⟨286619195999157298382939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764317855997752795687837 286619195999157298382939)
                  ·
                    rfl

theorem cell21_1255925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_1255925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255925 prefixEnd_1255925 := by exact prefixLift 1255925
  have htrace : WordTrace (prefixWord ++ tailWord_1255925) baseStart_1255925 baseEnd_1255925 := by
    simpa [prefixWord, tailWord_1255925, baseEnd_1255925] using wordTrace_append hprefix tailTrace_1255925
  have hstable : (prefixWord ++ tailWord_1255925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255925).length < 2 ^ (prefixWord ++ tailWord_1255925).sum := by decide
  have hdescent : baseEnd_1255925 < baseStart_1255925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255933 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1255933 : Nat := 118140960795 + 1255933 * 2 ^ 59
def prefixEnd_1255933 : Nat := 4983230072969 + 3 ^ 40 * 1255933 * 2
def baseEnd_1255933 : Nat := 286621021708151062249589

theorem tailTrace_1255933 : CollatzResearch.WordTrace tailWord_1255933 prefixEnd_1255933 286621021708151062249589 := by
  unfold tailWord_1255933
  simp only [CollatzResearch.WordTrace]
  refine ⟨45807639758976712124588453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30538426505984474749725635 45807639758976712124588453)
  ·
    refine ⟨8588932454808133523360335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45807639758976712124588453 8588932454808133523360335)
    ·
      refine ⟨12883398682212200285040503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8588932454808133523360335 12883398682212200285040503)
      ·
        refine ⟨19325098023318300427560755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12883398682212200285040503 19325098023318300427560755)
        ·
          refine ⟨28987647034977450641341133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19325098023318300427560755 28987647034977450641341133)
          ·
            refine ⟨10870367638116543990502925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28987647034977450641341133 10870367638116543990502925)
            ·
              refine ⟨4076387864293703996438597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10870367638116543990502925 4076387864293703996438597)
              ·
                refine ⟨764322724555069499332237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4076387864293703996438597 764322724555069499332237)
                ·
                  refine ⟨286621021708151062249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764322724555069499332237 286621021708151062249589)
                  ·
                    rfl

theorem cell21_1255933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1255933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255933 prefixEnd_1255933 := by exact prefixLift 1255933
  have htrace : WordTrace (prefixWord ++ tailWord_1255933) baseStart_1255933 baseEnd_1255933 := by
    simpa [prefixWord, tailWord_1255933, baseEnd_1255933] using wordTrace_append hprefix tailTrace_1255933
  have hstable : (prefixWord ++ tailWord_1255933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255933).length < 2 ^ (prefixWord ++ tailWord_1255933).sum := by decide
  have hdescent : baseEnd_1255933 < baseStart_1255933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255947 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_1255947 : Nat := 118140960795 + 1255947 * 2 ^ 59
def prefixEnd_1255947 : Nat := 4983230072969 + 3 ^ 40 * 1255947 * 2
def baseEnd_1255947 : Nat := 286624216698890149016227

theorem tailTrace_1255947 : CollatzResearch.WordTrace tailWord_1255947 prefixEnd_1255947 286624216698890149016227 := by
  unfold tailWord_1255947
  simp only [CollatzResearch.WordTrace]
  refine ⟨45808150380925992515598095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30538766920617328343732063 45808150380925992515598095)
  ·
    refine ⟨68712225571388988773397143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45808150380925992515598095 68712225571388988773397143)
    ·
      refine ⟨103068338357083483160095715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68712225571388988773397143 103068338357083483160095715)
      ·
        refine ⟨154602507535625224740143573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103068338357083483160095715 154602507535625224740143573)
        ·
          refine ⟨3623496270366216204847115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 154602507535625224740143573 3623496270366216204847115)
          ·
            refine ⟨5435244405549324307270673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623496270366216204847115 5435244405549324307270673)
            ·
              refine ⟨4076433304161993230453005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5435244405549324307270673 4076433304161993230453005)
              ·
                refine ⟨1528662489060747461419877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4076433304161993230453005 1528662489060747461419877)
                ·
                  refine ⟨286624216698890149016227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528662489060747461419877 286624216698890149016227)
                  ·
                    rfl

theorem cell21_1255947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_1255947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255947 prefixEnd_1255947 := by exact prefixLift 1255947
  have htrace : WordTrace (prefixWord ++ tailWord_1255947) baseStart_1255947 baseEnd_1255947 := by
    simpa [prefixWord, tailWord_1255947, baseEnd_1255947] using wordTrace_append hprefix tailTrace_1255947
  have hstable : (prefixWord ++ tailWord_1255947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255947).length < 2 ^ (prefixWord ++ tailWord_1255947).sum := by decide
  have hdescent : baseEnd_1255947 < baseStart_1255947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255992 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1255992 : Nat := 118140960795 + 1255992 * 2 ^ 59
def prefixEnd_1255992 : Nat := 4983230072969 + 3 ^ 40 * 1255992 * 2
def baseEnd_1255992 : Nat := 286634486311980070766135

theorem tailTrace_1255992 : CollatzResearch.WordTrace tailWord_1255992 prefixEnd_1255992 286634486311980070766135 := by
  unfold tailWord_1255992
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904895832881482600493115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30539861110508643467324153 22904895832881482600493115)
  ·
    refine ⟨34357343749322223900739673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22904895832881482600493115 34357343749322223900739673)
    ·
      refine ⟨25768007811991667925554755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34357343749322223900739673 25768007811991667925554755)
      ·
        refine ⟨38652011717987501888332133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25768007811991667925554755 38652011717987501888332133)
        ·
          refine ⟨7247252197122656604062275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38652011717987501888332133 7247252197122656604062275)
          ·
            refine ⟨10870878295683984906093413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247252197122656604062275 10870878295683984906093413)
            ·
              refine ⟨2038289680440747169892515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10870878295683984906093413 2038289680440747169892515)
              ·
                refine ⟨3057434520661120754838773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038289680440747169892515 3057434520661120754838773)
                ·
                  refine ⟨286634486311980070766135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057434520661120754838773 286634486311980070766135)
                  ·
                    rfl

theorem cell21_1255992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1255992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255992 prefixEnd_1255992 := by exact prefixLift 1255992
  have htrace : WordTrace (prefixWord ++ tailWord_1255992) baseStart_1255992 baseEnd_1255992 := by
    simpa [prefixWord, tailWord_1255992, baseEnd_1255992] using wordTrace_append hprefix tailTrace_1255992
  have hstable : (prefixWord ++ tailWord_1255992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255992).length < 2 ^ (prefixWord ++ tailWord_1255992).sum := by decide
  have hdescent : baseEnd_1255992 < baseStart_1255992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1255998 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1255998 : Nat := 118140960795 + 1255998 * 2 ^ 59
def prefixEnd_1255998 : Nat := 4983230072969 + 3 ^ 40 * 1255998 * 2
def baseEnd_1255998 : Nat := 286635855593725393666123

theorem tailTrace_1255998 : CollatzResearch.WordTrace tailWord_1255998 prefixEnd_1255998 286635855593725393666123 := by
  unfold tailWord_1255998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726251312967653528213081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30540007002494152150469765 5726251312967653528213081)
  ·
    refine ⟨4294688484725740146159811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5726251312967653528213081 4294688484725740146159811)
    ·
      refine ⟨6442032727088610219239717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294688484725740146159811 6442032727088610219239717)
      ·
        refine ⟨1207881136329114416107447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6442032727088610219239717 1207881136329114416107447)
        ·
          refine ⟨1811821704493671624161171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207881136329114416107447 1811821704493671624161171)
          ·
            refine ⟨2717732556740507436241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811821704493671624161171 2717732556740507436241757)
            ·
              refine ⟨1019149708777690288590659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2717732556740507436241757 1019149708777690288590659)
              ·
                refine ⟨1528724563166535432885989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019149708777690288590659 1528724563166535432885989)
                ·
                  refine ⟨286635855593725393666123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528724563166535432885989 286635855593725393666123)
                  ·
                    rfl

theorem cell21_1255998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1255998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1255998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1255998 prefixEnd_1255998 := by exact prefixLift 1255998
  have htrace : WordTrace (prefixWord ++ tailWord_1255998) baseStart_1255998 baseEnd_1255998 := by
    simpa [prefixWord, tailWord_1255998, baseEnd_1255998] using wordTrace_append hprefix tailTrace_1255998
  have hstable : (prefixWord ++ tailWord_1255998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1255998).length < 2 ^ (prefixWord ++ tailWord_1255998).sum := by decide
  have hdescent : baseEnd_1255998 < baseStart_1255998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1255998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256051 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_1256051 : Nat := 118140960795 + 1256051 * 2 ^ 59
def prefixEnd_1256051 : Nat := 4983230072969 + 3 ^ 40 * 1256051 * 2
def baseEnd_1256051 : Nat := 286647950915809079282681

theorem tailTrace_1256051 : CollatzResearch.WordTrace tailWord_1256051 prefixEnd_1256051 286647950915809079282681 := by
  unfold tailWord_1256051
  simp only [CollatzResearch.WordTrace]
  refine ⟨45811943572549218277384007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30541295715032812184922671 45811943572549218277384007)
  ·
    refine ⟨68717915358823827416076011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45811943572549218277384007 68717915358823827416076011)
    ·
      refine ⟨103076873038235741124114017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68717915358823827416076011 103076873038235741124114017)
      ·
        refine ⟨77307654778676805843085513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103076873038235741124114017 77307654778676805843085513)
        ·
          refine ⟨57980741084007604382314135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77307654778676805843085513 57980741084007604382314135)
          ·
            refine ⟨86971111626011406573471203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57980741084007604382314135 86971111626011406573471203)
            ·
              refine ⟨130456667439017109860206805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86971111626011406573471203 130456667439017109860206805)
              ·
                refine ⟨3057578143101963512348597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130456667439017109860206805 3057578143101963512348597)
                ·
                  refine ⟨286647950915809079282681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057578143101963512348597 286647950915809079282681)
                  ·
                    rfl

theorem cell21_1256051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_1256051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256051 prefixEnd_1256051 := by exact prefixLift 1256051
  have htrace : WordTrace (prefixWord ++ tailWord_1256051) baseStart_1256051 baseEnd_1256051 := by
    simpa [prefixWord, tailWord_1256051, baseEnd_1256051] using wordTrace_append hprefix tailTrace_1256051
  have hstable : (prefixWord ++ tailWord_1256051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256051).length < 2 ^ (prefixWord ++ tailWord_1256051).sum := by decide
  have hdescent : baseEnd_1256051 < baseStart_1256051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256096 : List Nat := [2, 1, 1, 4, 13]
def baseStart_1256096 : Nat := 118140960795 + 1256096 * 2 ^ 59
def prefixEnd_1256096 : Nat := 4983230072969 + 3 ^ 40 * 1256096 * 2
def baseEnd_1256096 : Nat := 3538990376899987667069

theorem tailTrace_1256096 : CollatzResearch.WordTrace tailWord_1256096 prefixEnd_1256096 3538990376899987667069 := by
  unfold tailWord_1256096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22906792428693095481386071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30542389904924127308514761 22906792428693095481386071)
  ·
    refine ⟨34360188643039643222079107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22906792428693095481386071 34360188643039643222079107)
    ·
      refine ⟨51540282964559464833118661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34360188643039643222079107 51540282964559464833118661)
      ·
        refine ⟨9663803055854899656209749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51540282964559464833118661 9663803055854899656209749)
        ·
          refine ⟨3538990376899987667069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9663803055854899656209749 3538990376899987667069)
          ·
            rfl

theorem cell21_1256096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 13].length) (baseStart_1256096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256096 prefixEnd_1256096 := by exact prefixLift 1256096
  have htrace : WordTrace (prefixWord ++ tailWord_1256096) baseStart_1256096 baseEnd_1256096 := by
    simpa [prefixWord, tailWord_1256096, baseEnd_1256096] using wordTrace_append hprefix tailTrace_1256096
  have hstable : (prefixWord ++ tailWord_1256096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256096).length < 2 ^ (prefixWord ++ tailWord_1256096).sum := by decide
  have hdescent : baseEnd_1256096 < baseStart_1256096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256127 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_1256127 : Nat := 118140960795 + 1256127 * 2 ^ 59
def prefixEnd_1256127 : Nat := 4983230072969 + 3 ^ 40 * 1256127 * 2
def baseEnd_1256127 : Nat := 286665295151249836015859

theorem tailTrace_1256127 : CollatzResearch.WordTrace tailWord_1256127 prefixEnd_1256127 286665295151249836015859 := by
  unfold tailWord_1256127
  simp only [CollatzResearch.WordTrace]
  refine ⟨45814715520273883257150635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30543143680182588838100423 45814715520273883257150635)
  ·
    refine ⟨68722073280410824885725953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45814715520273883257150635 68722073280410824885725953)
    ·
      refine ⟨51541554960308118664294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68722073280410824885725953 51541554960308118664294465)
      ·
        refine ⟨38656166220231088998220849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51541554960308118664294465 38656166220231088998220849)
        ·
          refine ⟨28992124665173316748665637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38656166220231088998220849 28992124665173316748665637)
          ·
            refine ⟨5436023374719996890374807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28992124665173316748665637 5436023374719996890374807)
            ·
              refine ⟨8154035062079995335562211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436023374719996890374807 8154035062079995335562211)
              ·
                refine ⟨12231052593119993003343317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154035062079995335562211 12231052593119993003343317)
                ·
                  refine ⟨286665295151249836015859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12231052593119993003343317 286665295151249836015859)
                  ·
                    rfl

theorem cell21_1256127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_1256127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256127 prefixEnd_1256127 := by exact prefixLift 1256127
  have htrace : WordTrace (prefixWord ++ tailWord_1256127) baseStart_1256127 baseEnd_1256127 := by
    simpa [prefixWord, tailWord_1256127, baseEnd_1256127] using wordTrace_append hprefix tailTrace_1256127
  have hstable : (prefixWord ++ tailWord_1256127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256127).length < 2 ^ (prefixWord ++ tailWord_1256127).sum := by decide
  have hdescent : baseEnd_1256127 < baseStart_1256127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256161 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 3]
def baseStart_1256161 : Nat := 118140960795 + 1256161 * 2 ^ 59
def prefixEnd_1256161 : Nat := 4983230072969 + 3 ^ 40 * 1256161 * 2
def baseEnd_1256161 : Nat := 286673054414473332449123

theorem tailTrace_1256161 : CollatzResearch.WordTrace tailWord_1256161 prefixEnd_1256161 286673054414473332449123 := by
  unfold tailWord_1256161
  simp only [CollatzResearch.WordTrace]
  refine ⟨45815955602150707063888337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30543970401433804709258891 45815955602150707063888337)
  ·
    refine ⟨34361966701613030297916253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45815955602150707063888337 34361966701613030297916253)
    ·
      refine ⟨12885737513104886361718595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34361966701613030297916253 12885737513104886361718595)
      ·
        refine ⟨19328606269657329542577893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12885737513104886361718595 19328606269657329542577893)
        ·
          refine ⟨3624113675560749289233355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19328606269657329542577893 3624113675560749289233355)
          ·
            refine ⟨5436170513341123933850033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624113675560749289233355 5436170513341123933850033)
            ·
              refine ⟨4077127885005842950387525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5436170513341123933850033 4077127885005842950387525)
              ·
                refine ⟨764461478438595553197661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4077127885005842950387525 764461478438595553197661)
                ·
                  refine ⟨286673054414473332449123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764461478438595553197661 286673054414473332449123)
                  ·
                    rfl

theorem cell21_1256161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_1256161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256161 prefixEnd_1256161 := by exact prefixLift 1256161
  have htrace : WordTrace (prefixWord ++ tailWord_1256161) baseStart_1256161 baseEnd_1256161 := by
    simpa [prefixWord, tailWord_1256161, baseEnd_1256161] using wordTrace_append hprefix tailTrace_1256161
  have hstable : (prefixWord ++ tailWord_1256161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256161).length < 2 ^ (prefixWord ++ tailWord_1256161).sum := by decide
  have hdescent : baseEnd_1256161 < baseStart_1256161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256172 : List Nat := [2, 2, 1, 1, 2, 2, 1, 10]
def baseStart_1256172 : Nat := 118140960795 + 1256172 * 2 ^ 59
def prefixEnd_1256172 : Nat := 4983230072969 + 3 ^ 40 * 1256172 * 2
def baseEnd_1256172 : Nat := 95558521588113252588589

theorem tailTrace_1256172 : CollatzResearch.WordTrace tailWord_1256172 prefixEnd_1256172 95558521588113252588589 := by
  unfold tailWord_1256172
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908178402555427971269385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30544237870073903961692513 22908178402555427971269385)
  ·
    refine ⟨17181133801916570978452039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22908178402555427971269385 17181133801916570978452039)
    ·
      refine ⟨25771700702874856467678059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17181133801916570978452039 25771700702874856467678059)
      ·
        refine ⟨38657551054312284701517089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25771700702874856467678059 38657551054312284701517089)
        ·
          refine ⟨28993163290734213526137817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38657551054312284701517089 28993163290734213526137817)
          ·
            refine ⟨21744872468050660144603363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28993163290734213526137817 21744872468050660144603363)
            ·
              refine ⟨32617308702075990216905045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21744872468050660144603363 32617308702075990216905045)
              ·
                refine ⟨95558521588113252588589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32617308702075990216905045 95558521588113252588589)
                ·
                  rfl

theorem cell21_1256172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_1256172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256172 prefixEnd_1256172 := by exact prefixLift 1256172
  have htrace : WordTrace (prefixWord ++ tailWord_1256172) baseStart_1256172 baseEnd_1256172 := by
    simpa [prefixWord, tailWord_1256172, baseEnd_1256172] using wordTrace_append hprefix tailTrace_1256172
  have hstable : (prefixWord ++ tailWord_1256172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256172).length < 2 ^ (prefixWord ++ tailWord_1256172).sum := by decide
  have hdescent : baseEnd_1256172 < baseStart_1256172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256181 : List Nat := [1, 3, 6, 1, 1, 2, 2, 5]
def baseStart_1256181 : Nat := 118140960795 + 1256181 * 2 ^ 59
def prefixEnd_1256181 : Nat := 4983230072969 + 3 ^ 40 * 1256181 * 2
def baseEnd_1256181 : Nat := 95559206228985914038583

theorem tailTrace_1256181 : CollatzResearch.WordTrace tailWord_1256181 prefixEnd_1256181 95559206228985914038583 := by
  unfold tailWord_1256181
  simp only [CollatzResearch.WordTrace]
  refine ⟨45816685062078250479616397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30544456708052166986410931 45816685062078250479616397)
  ·
    refine ⟨17181256898279343929856149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45816685062078250479616397 17181256898279343929856149)
    ·
      refine ⟨805371417106844246712007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17181256898279343929856149 805371417106844246712007)
      ·
        refine ⟨1208057125660266370068011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805371417106844246712007 1208057125660266370068011)
        ·
          refine ⟨1812085688490399555102017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208057125660266370068011 1812085688490399555102017)
          ·
            refine ⟨1359064266367799666326513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812085688490399555102017 1359064266367799666326513)
            ·
              refine ⟨1019298199775849749744885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359064266367799666326513 1019298199775849749744885)
              ·
                refine ⟨95559206228985914038583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1019298199775849749744885 95559206228985914038583)
                ·
                  rfl

theorem cell21_1256181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].length) (baseStart_1256181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256181 prefixEnd_1256181 := by exact prefixLift 1256181
  have htrace : WordTrace (prefixWord ++ tailWord_1256181) baseStart_1256181 baseEnd_1256181 := by
    simpa [prefixWord, tailWord_1256181, baseEnd_1256181] using wordTrace_append hprefix tailTrace_1256181
  have hstable : (prefixWord ++ tailWord_1256181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256181).length < 2 ^ (prefixWord ++ tailWord_1256181).sum := by decide
  have hdescent : baseEnd_1256181 < baseStart_1256181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256220 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1256220 : Nat := 118140960795 + 1256220 * 2 ^ 59
def prefixEnd_1256220 : Nat := 4983230072969 + 3 ^ 40 * 1256220 * 2
def baseEnd_1256220 : Nat := 286686519018302340965669

theorem tailTrace_1256220 : CollatzResearch.WordTrace tailWord_1256220 prefixEnd_1256220 286686519018302340965669 := by
  unfold tailWord_1256220
  simp only [CollatzResearch.WordTrace]
  refine ⟨22909053754468480070143057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30545405005957973426857409 22909053754468480070143057)
  ·
    refine ⟨17181790315851360052607293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22909053754468480070143057 17181790315851360052607293)
    ·
      refine ⟨6443171368444260019727735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17181790315851360052607293 6443171368444260019727735)
      ·
        refine ⟨9664757052666390029591603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443171368444260019727735 9664757052666390029591603)
        ·
          refine ⟨14497135578999585044387405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664757052666390029591603 14497135578999585044387405)
          ·
            refine ⟨5436425842124844391645277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14497135578999585044387405 5436425842124844391645277)
            ·
              refine ⟨2038659690796816646866979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5436425842124844391645277 2038659690796816646866979)
              ·
                refine ⟨3057989536195224970300469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038659690796816646866979 3057989536195224970300469)
                ·
                  refine ⟨286686519018302340965669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057989536195224970300469 286686519018302340965669)
                  ·
                    rfl

theorem cell21_1256220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1256220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256220 prefixEnd_1256220 := by exact prefixLift 1256220
  have htrace : WordTrace (prefixWord ++ tailWord_1256220) baseStart_1256220 baseEnd_1256220 := by
    simpa [prefixWord, tailWord_1256220, baseEnd_1256220] using wordTrace_append hprefix tailTrace_1256220
  have hstable : (prefixWord ++ tailWord_1256220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256220).length < 2 ^ (prefixWord ++ tailWord_1256220).sum := by decide
  have hdescent : baseEnd_1256220 < baseStart_1256220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256248 : List Nat := [2, 1, 2, 1, 3, 2, 1, 9]
def baseStart_1256248 : Nat := 118140960795 + 1256248 * 2 ^ 59
def prefixEnd_1256248 : Nat := 4983230072969 + 3 ^ 40 * 1256248 * 2
def baseEnd_1256248 : Nat := 95564302999926838166315

theorem tailTrace_1256248 : CollatzResearch.WordTrace tailWord_1256248 prefixEnd_1256248 95564302999926838166315 := by
  unfold tailWord_1256248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22909564376417760461152699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30546085835223680614870265 22909564376417760461152699)
  ·
    refine ⟨34364346564626640691729049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22909564376417760461152699 34364346564626640691729049)
    ·
      refine ⟨25773259923469980518796787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34364346564626640691729049 25773259923469980518796787)
      ·
        refine ⟨38659889885204970778195181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25773259923469980518796787 38659889885204970778195181)
        ·
          refine ⟨14497458706951864041823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38659889885204970778195181 14497458706951864041823193)
          ·
            refine ⟨10873094030213898031367395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14497458706951864041823193 10873094030213898031367395)
            ·
              refine ⟨16309641045320847047051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10873094030213898031367395 16309641045320847047051093)
              ·
                refine ⟨95564302999926838166315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16309641045320847047051093 95564302999926838166315)
                ·
                  rfl

theorem cell21_1256248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_1256248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256248 prefixEnd_1256248 := by exact prefixLift 1256248
  have htrace : WordTrace (prefixWord ++ tailWord_1256248) baseStart_1256248 baseEnd_1256248 := by
    simpa [prefixWord, tailWord_1256248, baseEnd_1256248] using wordTrace_append hprefix tailTrace_1256248
  have hstable : (prefixWord ++ tailWord_1256248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256248).length < 2 ^ (prefixWord ++ tailWord_1256248).sum := by decide
  have hdescent : baseEnd_1256248 < baseStart_1256248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256296 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_1256296 : Nat := 118140960795 + 1256296 * 2 ^ 59
def prefixEnd_1256296 : Nat := 4983230072969 + 3 ^ 40 * 1256296 * 2
def baseEnd_1256296 : Nat := 286703863253743097698847

theorem tailTrace_1256296 : CollatzResearch.WordTrace tailWord_1256296 prefixEnd_1256296 286703863253743097698847 := by
  unfold tailWord_1256296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22910439728330812560026371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30547252971107750080035161 22910439728330812560026371)
  ·
    refine ⟨34365659592496218840039557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22910439728330812560026371 34365659592496218840039557)
    ·
      refine ⟨6443561173593041032507417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34365659592496218840039557 6443561173593041032507417)
      ·
        refine ⟨4832670880194780774380563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443561173593041032507417 4832670880194780774380563)
        ·
          refine ⟨7249006320292171161570845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832670880194780774380563 7249006320292171161570845)
          ·
            refine ⟨2718377370109564185589067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7249006320292171161570845 2718377370109564185589067)
            ·
              refine ⟨4077566055164346278383601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718377370109564185589067 4077566055164346278383601)
              ·
                refine ⟨3058174541373259708787701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077566055164346278383601 3058174541373259708787701)
                ·
                  refine ⟨286703863253743097698847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3058174541373259708787701 286703863253743097698847)
                  ·
                    rfl

theorem cell21_1256296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_1256296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256296 prefixEnd_1256296 := by exact prefixLift 1256296
  have htrace : WordTrace (prefixWord ++ tailWord_1256296) baseStart_1256296 baseEnd_1256296 := by
    simpa [prefixWord, tailWord_1256296, baseEnd_1256296] using wordTrace_append hprefix tailTrace_1256296
  have hstable : (prefixWord ++ tailWord_1256296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256296).length < 2 ^ (prefixWord ++ tailWord_1256296).sum := by decide
  have hdescent : baseEnd_1256296 < baseStart_1256296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256313 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 3]
def baseStart_1256313 : Nat := 118140960795 + 1256313 * 2 ^ 59
def prefixEnd_1256313 : Nat := 4983230072969 + 3 ^ 40 * 1256313 * 2
def baseEnd_1256313 : Nat := 286707742885354845915479

theorem tailTrace_1256313 : CollatzResearch.WordTrace tailWord_1256313 prefixEnd_1256313 286707742885354845915479 := by
  unfold tailWord_1256313
  simp only [CollatzResearch.WordTrace]
  refine ⟨45821499497600037023421593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30547666331733358015614395 45821499497600037023421593)
  ·
    refine ⟨34366124623200027767566195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45821499497600037023421593 34366124623200027767566195)
    ·
      refine ⟨51549186934800041651349293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34366124623200027767566195 51549186934800041651349293)
      ·
        refine ⟨19330945100550015619255985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51549186934800041651349293 19330945100550015619255985)
        ·
          refine ⟨14498208825412511714441989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19330945100550015619255985 14498208825412511714441989)
          ·
            refine ⟨2718414154764845946457873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14498208825412511714441989 2718414154764845946457873)
            ·
              refine ⟨2038810616073634459843405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718414154764845946457873 2038810616073634459843405)
              ·
                refine ⟨764553981027612922441277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2038810616073634459843405 764553981027612922441277)
                ·
                  refine ⟨286707742885354845915479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764553981027612922441277 286707742885354845915479)
                  ·
                    rfl

theorem cell21_1256313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_1256313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256313 prefixEnd_1256313 := by exact prefixLift 1256313
  have htrace : WordTrace (prefixWord ++ tailWord_1256313) baseStart_1256313 baseEnd_1256313 := by
    simpa [prefixWord, tailWord_1256313, baseEnd_1256313] using wordTrace_append hprefix tailTrace_1256313
  have hstable : (prefixWord ++ tailWord_1256313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256313).length < 2 ^ (prefixWord ++ tailWord_1256313).sum := by decide
  have hdescent : baseEnd_1256313 < baseStart_1256313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256327 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_1256327 : Nat := 118140960795 + 1256327 * 2 ^ 59
def prefixEnd_1256327 : Nat := 4983230072969 + 3 ^ 40 * 1256327 * 2
def baseEnd_1256327 : Nat := 286710937876093932682117

theorem tailTrace_1256327 : CollatzResearch.WordTrace tailWord_1256327 prefixEnd_1256327 286710937876093932682117 := by
  unfold tailWord_1256327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45822010119549317414431235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30548006746366211609620823 45822010119549317414431235)
  ·
    refine ⟨68733015179323976121646853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45822010119549317414431235 68733015179323976121646853)
    ·
      refine ⟨12887440346123245522808785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68733015179323976121646853 12887440346123245522808785)
      ·
        refine ⟨9665580259592434142106589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12887440346123245522808785 9665580259592434142106589)
        ·
          refine ⟨3624592597347162803289971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9665580259592434142106589 3624592597347162803289971)
          ·
            refine ⟨5436888896020744204934957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624592597347162803289971 5436888896020744204934957)
            ·
              refine ⟨2038833336007779076850609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5436888896020744204934957 2038833336007779076850609)
              ·
                refine ⟨1529125002005834307637957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038833336007779076850609 1529125002005834307637957)
                ·
                  refine ⟨286710937876093932682117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529125002005834307637957 286710937876093932682117)
                  ·
                    rfl

theorem cell21_1256327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_1256327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256327 prefixEnd_1256327 := by exact prefixLift 1256327
  have htrace : WordTrace (prefixWord ++ tailWord_1256327) baseStart_1256327 baseEnd_1256327 := by
    simpa [prefixWord, tailWord_1256327, baseEnd_1256327] using wordTrace_append hprefix tailTrace_1256327
  have hstable : (prefixWord ++ tailWord_1256327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256327).length < 2 ^ (prefixWord ++ tailWord_1256327).sum := by decide
  have hdescent : baseEnd_1256327 < baseStart_1256327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256355 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_1256355 : Nat := 118140960795 + 1256355 * 2 ^ 59
def prefixEnd_1256355 : Nat := 4983230072969 + 3 ^ 40 * 1256355 * 2
def baseEnd_1256355 : Nat := 286717327857572106215393

theorem tailTrace_1256355 : CollatzResearch.WordTrace tailWord_1256355 prefixEnd_1256355 286717327857572106215393 := by
  unfold tailWord_1256355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45823031363447878196450519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30548687575631918797633679 45823031363447878196450519)
  ·
    refine ⟨68734547045171817294675779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45823031363447878196450519 68734547045171817294675779)
    ·
      refine ⟨103101820567757725942013669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68734547045171817294675779 103101820567757725942013669)
      ·
        refine ⟨19331591356454573614127563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103101820567757725942013669 19331591356454573614127563)
        ·
          refine ⟨28997387034681860421191345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19331591356454573614127563 28997387034681860421191345)
          ·
            refine ⟨21748040276011395315893509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28997387034681860421191345 21748040276011395315893509)
            ·
              refine ⟨4077757551752136621730033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21748040276011395315893509 4077757551752136621730033)
              ·
                refine ⟨3058318163814102466297525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077757551752136621730033 3058318163814102466297525)
                ·
                  refine ⟨286717327857572106215393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3058318163814102466297525 286717327857572106215393)
                  ·
                    rfl

theorem cell21_1256355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_1256355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256355 prefixEnd_1256355 := by exact prefixLift 1256355
  have htrace : WordTrace (prefixWord ++ tailWord_1256355) baseStart_1256355 baseEnd_1256355 := by
    simpa [prefixWord, tailWord_1256355, baseEnd_1256355] using wordTrace_append hprefix tailTrace_1256355
  have hstable : (prefixWord ++ tailWord_1256355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256355).length < 2 ^ (prefixWord ++ tailWord_1256355).sum := by decide
  have hdescent : baseEnd_1256355 < baseStart_1256355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256434 : List Nat := [3, 2, 1, 5, 2, 8]
def baseStart_1256434 : Nat := 118140960795 + 1256434 * 2 ^ 59
def prefixEnd_1256434 : Nat := 4983230072969 + 3 ^ 40 * 1256434 * 2
def baseEnd_1256434 : Nat := 10619828027180945348095

theorem tailTrace_1256434 : CollatzResearch.WordTrace tailWord_1256434 prefixEnd_1256434 10619828027180945348095 := by
  unfold tailWord_1256434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456478182540418672144089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30550608486774449792384237 11456478182540418672144089)
  ·
    refine ⟨8592358636905314004108067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11456478182540418672144089 8592358636905314004108067)
    ·
      refine ⟨12888537955357971006162101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8592358636905314004108067 12888537955357971006162101)
      ·
        refine ⟨1208300433314809781827697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12888537955357971006162101 1208300433314809781827697)
        ·
          refine ⟨906225324986107336370773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208300433314809781827697 906225324986107336370773)
          ·
            refine ⟨10619828027180945348095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 906225324986107336370773 10619828027180945348095)
            ·
              rfl

theorem cell21_1256434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 8].length) (baseStart_1256434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256434 prefixEnd_1256434 := by exact prefixLift 1256434
  have htrace : WordTrace (prefixWord ++ tailWord_1256434) baseStart_1256434 baseEnd_1256434 := by
    simpa [prefixWord, tailWord_1256434, baseEnd_1256434] using wordTrace_append hprefix tailTrace_1256434
  have hstable : (prefixWord ++ tailWord_1256434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256434).length < 2 ^ (prefixWord ++ tailWord_1256434).sum := by decide
  have hdescent : baseEnd_1256434 < baseStart_1256434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256437 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1256437 : Nat := 118140960795 + 1256437 * 2 ^ 59
def prefixEnd_1256437 : Nat := 4983230072969 + 3 ^ 40 * 1256437 * 2
def baseEnd_1256437 : Nat := 286736041374758185848559

theorem tailTrace_1256437 : CollatzResearch.WordTrace tailWord_1256437 prefixEnd_1256437 286736041374758185848559 := by
  unfold tailWord_1256437
  simp only [CollatzResearch.WordTrace]
  refine ⟨45826022149150806200935565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30550681432767204133957043 45826022149150806200935565)
  ·
    refine ⟨17184758305931552325350837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45826022149150806200935565 17184758305931552325350837)
    ·
      refine ⟨1611071091181083030501641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17184758305931552325350837 1611071091181083030501641)
      ·
        refine ⟨1208303318385812272876231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611071091181083030501641 1208303318385812272876231)
        ·
          refine ⟨1812454977578718409314347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208303318385812272876231 1812454977578718409314347)
          ·
            refine ⟨2718682466368077613971521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812454977578718409314347 2718682466368077613971521)
            ·
              refine ⟨2039011849776058210478641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718682466368077613971521 2039011849776058210478641)
              ·
                refine ⟨1529258887332043657858981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039011849776058210478641 1529258887332043657858981)
                ·
                  refine ⟨286736041374758185848559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529258887332043657858981 286736041374758185848559)
                  ·
                    rfl

theorem cell21_1256437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1256437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256437 prefixEnd_1256437 := by exact prefixLift 1256437
  have htrace : WordTrace (prefixWord ++ tailWord_1256437) baseStart_1256437 baseEnd_1256437 := by
    simpa [prefixWord, tailWord_1256437, baseEnd_1256437] using wordTrace_append hprefix tailTrace_1256437
  have hstable : (prefixWord ++ tailWord_1256437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256437).length < 2 ^ (prefixWord ++ tailWord_1256437).sum := by decide
  have hdescent : baseEnd_1256437 < baseStart_1256437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256558 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_1256558 : Nat := 118140960795 + 1256558 * 2 ^ 59
def prefixEnd_1256558 : Nat := 4983230072969 + 3 ^ 40 * 1256558 * 2
def baseEnd_1256558 : Nat := 286763655223288864331645

theorem tailTrace_1256558 : CollatzResearch.WordTrace tailWord_1256558 prefixEnd_1256558 286763655223288864331645 := by
  unfold tailWord_1256558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728804422714055483261291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30553623587808295910726885 5728804422714055483261291)
  ·
    refine ⟨8593206634071083224891937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5728804422714055483261291 8593206634071083224891937)
    ·
      refine ⟨6444904975553312418668953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8593206634071083224891937 6444904975553312418668953)
      ·
        refine ⟨4833678731664984314001715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6444904975553312418668953 4833678731664984314001715)
        ·
          refine ⟨7250518097497476471002573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833678731664984314001715 7250518097497476471002573)
          ·
            refine ⟨2718944286561553676625965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7250518097497476471002573 2718944286561553676625965)
            ·
              refine ⟨1019604107460582628734737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2718944286561553676625965 1019604107460582628734737)
              ·
                refine ⟨764703080595436971551053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019604107460582628734737 764703080595436971551053)
                ·
                  refine ⟨286763655223288864331645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764703080595436971551053 286763655223288864331645)
                  ·
                    rfl

theorem cell21_1256558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_1256558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256558 prefixEnd_1256558 := by exact prefixLift 1256558
  have htrace : WordTrace (prefixWord ++ tailWord_1256558) baseStart_1256558 baseEnd_1256558 := by
    simpa [prefixWord, tailWord_1256558, baseEnd_1256558] using wordTrace_append hprefix tailTrace_1256558
  have hstable : (prefixWord ++ tailWord_1256558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256558).length < 2 ^ (prefixWord ++ tailWord_1256558).sum := by decide
  have hdescent : baseEnd_1256558 < baseStart_1256558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256569 : List Nat := [1, 2, 1, 3, 5, 1, 2, 6]
def baseStart_1256569 : Nat := 118140960795 + 1256569 * 2 ^ 59
def prefixEnd_1256569 : Nat := 4983230072969 + 3 ^ 40 * 1256569 * 2
def baseEnd_1256569 : Nat := 95588721857718429882763

theorem tailTrace_1256569 : CollatzResearch.WordTrace tailWord_1256569 prefixEnd_1256569 95588721857718429882763 := by
  unfold tailWord_1256569
  simp only [CollatzResearch.WordTrace]
  refine ⟨45830836584672592744740761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30553891056448395163160507 45830836584672592744740761)
  ·
    refine ⟨34373127438504444558555571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45830836584672592744740761 34373127438504444558555571)
    ·
      refine ⟨51559691157756666837833357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34373127438504444558555571 51559691157756666837833357)
      ·
        refine ⟨19334884184158750064187509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51559691157756666837833357 19334884184158750064187509)
        ·
          refine ⟨1812645392264882818517579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19334884184158750064187509 1812645392264882818517579)
          ·
            refine ⟨2718968088397324227776369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812645392264882818517579 2718968088397324227776369)
            ·
              refine ⟨2039226066297993170832277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718968088397324227776369 2039226066297993170832277)
              ·
                refine ⟨95588721857718429882763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2039226066297993170832277 95588721857718429882763)
                ·
                  rfl

theorem cell21_1256569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_1256569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256569 prefixEnd_1256569 := by exact prefixLift 1256569
  have htrace : WordTrace (prefixWord ++ tailWord_1256569) baseStart_1256569 baseEnd_1256569 := by
    simpa [prefixWord, tailWord_1256569, baseEnd_1256569] using wordTrace_append hprefix tailTrace_1256569
  have hstable : (prefixWord ++ tailWord_1256569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256569).length < 2 ^ (prefixWord ++ tailWord_1256569).sum := by decide
  have hdescent : baseEnd_1256569 < baseStart_1256569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256597 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1256597 : Nat := 118140960795 + 1256597 * 2 ^ 59
def prefixEnd_1256597 : Nat := 4983230072969 + 3 ^ 40 * 1256597 * 2
def baseEnd_1256597 : Nat := 286772555554633463181565

theorem tailTrace_1256597 : CollatzResearch.WordTrace tailWord_1256597 prefixEnd_1256597 286772555554633463181565 := by
  unfold tailWord_1256597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45831857828571153526760045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30554571885714102351173363 45831857828571153526760045)
  ·
    refine ⟨17186946685714182572535017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45831857828571153526760045 17186946685714182572535017)
    ·
      refine ⟨12890210014285636929401263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17186946685714182572535017 12890210014285636929401263)
      ·
        refine ⟨19335315021428455394101895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12890210014285636929401263 19335315021428455394101895)
        ·
          refine ⟨29002972532142683091152843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19335315021428455394101895 29002972532142683091152843)
          ·
            refine ⟨43504458798214024636729265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29002972532142683091152843 43504458798214024636729265)
            ·
              refine ⟨32628344098660518477546949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43504458798214024636729265 32628344098660518477546949)
              ·
                refine ⟨6117814518498847214540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32628344098660518477546949 6117814518498847214540053)
                ·
                  refine ⟨286772555554633463181565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6117814518498847214540053 286772555554633463181565)
                  ·
                    rfl

theorem cell21_1256597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1256597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256597 prefixEnd_1256597 := by exact prefixLift 1256597
  have htrace : WordTrace (prefixWord ++ tailWord_1256597) baseStart_1256597 baseEnd_1256597 := by
    simpa [prefixWord, tailWord_1256597, baseEnd_1256597] using wordTrace_append hprefix tailTrace_1256597
  have hstable : (prefixWord ++ tailWord_1256597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256597).length < 2 ^ (prefixWord ++ tailWord_1256597).sum := by decide
  have hdescent : baseEnd_1256597 < baseStart_1256597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256662 : List Nat := [5, 2, 1, 2, 2, 1, 8]
def baseStart_1256662 : Nat := 118140960795 + 1256662 * 2 ^ 59
def prefixEnd_1256662 : Nat := 4983230072969 + 3 ^ 40 * 1256662 * 2
def baseEnd_1256662 : Nat := 31865265493356421622011

theorem tailTrace_1256662 : CollatzResearch.WordTrace tailWord_1256662 prefixEnd_1256662 31865265493356421622011 := by
  unfold tailWord_1256662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864639285833479351742265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30556152382223779751917493 2864639285833479351742265)
  ·
    refine ⟨2148479464375109513806699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2864639285833479351742265 2148479464375109513806699)
    ·
      refine ⟨3222719196562664270710049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148479464375109513806699 3222719196562664270710049)
      ·
        refine ⟨2417039397421998203032537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222719196562664270710049 2417039397421998203032537)
        ·
          refine ⟨1812779548066498652274403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417039397421998203032537 1812779548066498652274403)
          ·
            refine ⟨2719169322099747978411605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812779548066498652274403 2719169322099747978411605)
            ·
              refine ⟨31865265493356421622011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2719169322099747978411605 31865265493356421622011)
              ·
                rfl

theorem cell21_1256662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 8].length) (baseStart_1256662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256662 prefixEnd_1256662 := by exact prefixLift 1256662
  have htrace : WordTrace (prefixWord ++ tailWord_1256662) baseStart_1256662 baseEnd_1256662 := by
    simpa [prefixWord, tailWord_1256662, baseEnd_1256662] using wordTrace_append hprefix tailTrace_1256662
  have hstable : (prefixWord ++ tailWord_1256662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256662).length < 2 ^ (prefixWord ++ tailWord_1256662).sum := by decide
  have hdescent : baseEnd_1256662 < baseStart_1256662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256676 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1256676 : Nat := 118140960795 + 1256676 * 2 ^ 59
def prefixEnd_1256676 : Nat := 4983230072969 + 3 ^ 40 * 1256676 * 2
def baseEnd_1256676 : Nat := 286790584430946881364737

theorem tailTrace_1256676 : CollatzResearch.WordTrace tailWord_1256676 prefixEnd_1256676 286790584430946881364737 := by
  unfold tailWord_1256676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22917369597642475009442941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30556492796856633345923921 22917369597642475009442941)
  ·
    refine ⟨8594013599115928128541103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22917369597642475009442941 8594013599115928128541103)
    ·
      refine ⟨12891020398673892192811655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8594013599115928128541103 12891020398673892192811655)
      ·
        refine ⟨19336530598010838289217483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12891020398673892192811655 19336530598010838289217483)
        ·
          refine ⟨29004795897016257433826225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19336530598010838289217483 29004795897016257433826225)
          ·
            refine ⟨21753596922762193075369669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29004795897016257433826225 21753596922762193075369669)
            ·
              refine ⟨4078799423017911201631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21753596922762193075369669 4078799423017911201631813)
              ·
                refine ⟨764774891815858350305965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4078799423017911201631813 764774891815858350305965)
                ·
                  refine ⟨286790584430946881364737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764774891815858350305965 286790584430946881364737)
                  ·
                    rfl

theorem cell21_1256676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1256676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256676 prefixEnd_1256676 := by exact prefixLift 1256676
  have htrace : WordTrace (prefixWord ++ tailWord_1256676) baseStart_1256676 baseEnd_1256676 := by
    simpa [prefixWord, tailWord_1256676, baseEnd_1256676] using wordTrace_append hprefix tailTrace_1256676
  have hstable : (prefixWord ++ tailWord_1256676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256676).length < 2 ^ (prefixWord ++ tailWord_1256676).sum := by decide
  have hdescent : baseEnd_1256676 < baseStart_1256676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256828 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_1256828 : Nat := 118140960795 + 1256828 * 2 ^ 59
def prefixEnd_1256828 : Nat := 4983230072969 + 3 ^ 40 * 1256828 * 2
def baseEnd_1256828 : Nat := 286825272901828394831093

theorem tailTrace_1256828 : CollatzResearch.WordTrace tailWord_1256828 prefixEnd_1256828 286825272901828394831093 := by
  unfold tailWord_1256828
  simp only [CollatzResearch.WordTrace]
  refine ⟨22920141545367139989209569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30560188727156186652279425 22920141545367139989209569)
  ·
    refine ⟨17190106159025354991907177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22920141545367139989209569 17190106159025354991907177)
    ·
      refine ⟨12892579619269016243930383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17190106159025354991907177 12892579619269016243930383)
      ·
        refine ⟨19338869428903524365895575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12892579619269016243930383 19338869428903524365895575)
        ·
          refine ⟨29008304143355286548843363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19338869428903524365895575 29008304143355286548843363)
          ·
            refine ⟨43512456215032929823265045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29008304143355286548843363 43512456215032929823265045)
            ·
              refine ⟨2039646385079668585465549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43512456215032929823265045 2039646385079668585465549)
              ·
                refine ⟨764867394404875719549581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2039646385079668585465549 764867394404875719549581)
                ·
                  refine ⟨286825272901828394831093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764867394404875719549581 286825272901828394831093)
                  ·
                    rfl

theorem cell21_1256828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_1256828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256828 prefixEnd_1256828 := by exact prefixLift 1256828
  have htrace : WordTrace (prefixWord ++ tailWord_1256828) baseStart_1256828 baseEnd_1256828 := by
    simpa [prefixWord, tailWord_1256828, baseEnd_1256828] using wordTrace_append hprefix tailTrace_1256828
  have hstable : (prefixWord ++ tailWord_1256828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256828).length < 2 ^ (prefixWord ++ tailWord_1256828).sum := by decide
  have hdescent : baseEnd_1256828 < baseStart_1256828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256977 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_1256977 : Nat := 118140960795 + 1256977 * 2 ^ 59
def prefixEnd_1256977 : Nat := 4983230072969 + 3 ^ 40 * 1256977 * 2
def baseEnd_1256977 : Nat := 286859276731837246847455

theorem tailTrace_1256977 : CollatzResearch.WordTrace tailWord_1256977 prefixEnd_1256977 286859276731837246847455 := by
  unfold tailWord_1256977
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845717567194478425593185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30563811711462985617062123 45845717567194478425593185)
  ·
    refine ⟨34384288175395858819194889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45845717567194478425593185 34384288175395858819194889)
    ·
      refine ⟨25788216131546894114396167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34384288175395858819194889 25788216131546894114396167)
      ·
        refine ⟨38682324197320341171594251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25788216131546894114396167 38682324197320341171594251)
        ·
          refine ⟨58023486295980511757391377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38682324197320341171594251 58023486295980511757391377)
          ·
            refine ⟨43517614721985383818043533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58023486295980511757391377 43517614721985383818043533)
            ·
              refine ⟨16319105520744518931766325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43517614721985383818043533 16319105520744518931766325)
              ·
                refine ⟨1529916142569798649853093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16319105520744518931766325 1529916142569798649853093)
                ·
                  refine ⟨286859276731837246847455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529916142569798649853093 286859276731837246847455)
                  ·
                    rfl

theorem cell21_1256977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_1256977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256977 prefixEnd_1256977 := by exact prefixLift 1256977
  have htrace : WordTrace (prefixWord ++ tailWord_1256977) baseStart_1256977 baseEnd_1256977 := by
    simpa [prefixWord, tailWord_1256977, baseEnd_1256977] using wordTrace_append hprefix tailTrace_1256977
  have hstable : (prefixWord ++ tailWord_1256977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256977).length < 2 ^ (prefixWord ++ tailWord_1256977).sum := by decide
  have hdescent : baseEnd_1256977 < baseStart_1256977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1256991 : List Nat := [1, 1, 2, 4, 1, 1, 2, 9]
def baseStart_1256991 : Nat := 118140960795 + 1256991 * 2 ^ 59
def prefixEnd_1256991 : Nat := 4983230072969 + 3 ^ 40 * 1256991 * 2
def baseEnd_1256991 : Nat := 95620823907525444538031

theorem tailTrace_1256991 : CollatzResearch.WordTrace tailWord_1256991 prefixEnd_1256991 95620823907525444538031 := by
  unfold tailWord_1256991
  simp only [CollatzResearch.WordTrace]
  refine ⟨45846228189143758816602827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30564152126095839211068551 45846228189143758816602827)
  ·
    refine ⟨68769342283715638224904241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45846228189143758816602827 68769342283715638224904241)
    ·
      refine ⟨51577006712786728668678181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68769342283715638224904241 51577006712786728668678181)
      ·
        refine ⟨9670688758647511625377159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51577006712786728668678181 9670688758647511625377159)
        ·
          refine ⟨14506033137971267438065739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670688758647511625377159 14506033137971267438065739)
          ·
            refine ⟨21759049706956901157098609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14506033137971267438065739 21759049706956901157098609)
            ·
              refine ⟨16319287280217675867823957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21759049706956901157098609 16319287280217675867823957)
              ·
                refine ⟨95620823907525444538031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16319287280217675867823957 95620823907525444538031)
                ·
                  rfl

theorem cell21_1256991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_1256991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1256991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1256991 prefixEnd_1256991 := by exact prefixLift 1256991
  have htrace : WordTrace (prefixWord ++ tailWord_1256991) baseStart_1256991 baseEnd_1256991 := by
    simpa [prefixWord, tailWord_1256991, baseEnd_1256991] using wordTrace_append hprefix tailTrace_1256991
  have hstable : (prefixWord ++ tailWord_1256991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1256991).length < 2 ^ (prefixWord ++ tailWord_1256991).sum := by decide
  have hdescent : baseEnd_1256991 < baseStart_1256991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1256991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257160 : List Nat := [2, 1, 3, 1, 2, 2, 5, 5]
def baseStart_1257160 : Nat := 118140960795 + 1257160 * 2 ^ 59
def prefixEnd_1257160 : Nat := 4983230072969 + 3 ^ 40 * 1257160 * 2
def baseEnd_1257160 : Nat := 95633679941689865099027

theorem tailTrace_1257160 : CollatzResearch.WordTrace tailWord_1257160 prefixEnd_1257160 95633679941689865099027 := by
  unfold tailWord_1257160
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926196062765750339752467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30568261417021000453003289 22926196062765750339752467)
  ·
    refine ⟨34389294094148625509628701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22926196062765750339752467 34389294094148625509628701)
    ·
      refine ⟨12895985285305734566110763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34389294094148625509628701 12895985285305734566110763)
      ·
        refine ⟨19343977927958601849166145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12895985285305734566110763 19343977927958601849166145)
        ·
          refine ⟨14507983445968951386874609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19343977927958601849166145 14507983445968951386874609)
          ·
            refine ⟨10880987584476713540155957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14507983445968951386874609 10880987584476713540155957)
            ·
              refine ⟨1020092586044691894389621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10880987584476713540155957 1020092586044691894389621)
              ·
                refine ⟨95633679941689865099027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020092586044691894389621 95633679941689865099027)
                ·
                  rfl

theorem cell21_1257160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_1257160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257160 prefixEnd_1257160 := by exact prefixLift 1257160
  have htrace : WordTrace (prefixWord ++ tailWord_1257160) baseStart_1257160 baseEnd_1257160 := by
    simpa [prefixWord, tailWord_1257160, baseEnd_1257160] using wordTrace_append hprefix tailTrace_1257160
  have hstable : (prefixWord ++ tailWord_1257160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257160).length < 2 ^ (prefixWord ++ tailWord_1257160).sum := by decide
  have hdescent : baseEnd_1257160 < baseStart_1257160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257180 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1257180 : Nat := 118140960795 + 1257180 * 2 ^ 59
def prefixEnd_1257180 : Nat := 4983230072969 + 3 ^ 40 * 1257180 * 2
def baseEnd_1257180 : Nat := 286905604097554004963707

theorem tailTrace_1257180 : CollatzResearch.WordTrace tailWord_1257180 prefixEnd_1257180 286905604097554004963707 := by
  unfold tailWord_1257180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926560792729522047616497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30568747723639362730155329 22926560792729522047616497)
  ·
    refine ⟨17194920594547141535712373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22926560792729522047616497 17194920594547141535712373)
    ·
      refine ⟨1612023805738794518973035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17194920594547141535712373 1612023805738794518973035)
      ·
        refine ⟨2418035708608191778459553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612023805738794518973035 2418035708608191778459553)
        ·
          refine ⟨1813526781456143833844665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418035708608191778459553 1813526781456143833844665)
          ·
            refine ⟨1360145086092107875383499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813526781456143833844665 1360145086092107875383499)
            ·
              refine ⟨2040217629138161813075249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360145086092107875383499 2040217629138161813075249)
              ·
                refine ⟨1530163221853621359806437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040217629138161813075249 1530163221853621359806437)
                ·
                  refine ⟨286905604097554004963707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530163221853621359806437 286905604097554004963707)
                  ·
                    rfl

theorem cell21_1257180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1257180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257180 prefixEnd_1257180 := by exact prefixLift 1257180
  have htrace : WordTrace (prefixWord ++ tailWord_1257180) baseStart_1257180 baseEnd_1257180 := by
    simpa [prefixWord, tailWord_1257180, baseEnd_1257180] using wordTrace_append hprefix tailTrace_1257180
  have hstable : (prefixWord ++ tailWord_1257180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257180).length < 2 ^ (prefixWord ++ tailWord_1257180).sum := by decide
  have hdescent : baseEnd_1257180 < baseStart_1257180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257298 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1257298 : Nat := 118140960795 + 1257298 * 2 ^ 59
def prefixEnd_1257298 : Nat := 4983230072969 + 3 ^ 40 * 1257298 * 2
def baseEnd_1257298 : Nat := 286932533305212021996799

theorem tailTrace_1257298 : CollatzResearch.WordTrace tailWord_1257298 prefixEnd_1257298 286932533305212021996799 := by
  unfold tailWord_1257298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464356349757887562007137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30571616932687700165352365 11464356349757887562007137)
  ·
    refine ⟨8598267262318415671505353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11464356349757887562007137 8598267262318415671505353)
    ·
      refine ⟨6448700446738811753629015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8598267262318415671505353 6448700446738811753629015)
      ·
        refine ⟨9673050670108217630443523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448700446738811753629015 9673050670108217630443523)
        ·
          refine ⟨14509576005162326445665285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9673050670108217630443523 14509576005162326445665285)
          ·
            refine ⟨2720545500967936208562241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14509576005162326445665285 2720545500967936208562241)
            ·
              refine ⟨2040409125725952156421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720545500967936208562241 2040409125725952156421681)
              ·
                refine ⟨1530306844294464117316261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040409125725952156421681 1530306844294464117316261)
                ·
                  refine ⟨286932533305212021996799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530306844294464117316261 286932533305212021996799)
                  ·
                    rfl

theorem cell21_1257298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1257298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257298 prefixEnd_1257298 := by exact prefixLift 1257298
  have htrace : WordTrace (prefixWord ++ tailWord_1257298) baseStart_1257298 baseEnd_1257298 := by
    simpa [prefixWord, tailWord_1257298, baseEnd_1257298] using wordTrace_append hprefix tailTrace_1257298
  have hstable : (prefixWord ++ tailWord_1257298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257298).length < 2 ^ (prefixWord ++ tailWord_1257298).sum := by decide
  have hdescent : baseEnd_1257298 < baseStart_1257298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257301 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1257301 : Nat := 118140960795 + 1257301 * 2 ^ 59
def prefixEnd_1257301 : Nat := 4983230072969 + 3 ^ 40 * 1257301 * 2
def baseEnd_1257301 : Nat := 286933217946084683446793

theorem tailTrace_1257301 : CollatzResearch.WordTrace tailWord_1257301 prefixEnd_1257301 286933217946084683446793 := by
  unfold tailWord_1257301
  simp only [CollatzResearch.WordTrace]
  refine ⟨45857534818020681760387757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30571689878680454506925171 45857534818020681760387757)
  ·
    refine ⟨17196575556757755660145409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45857534818020681760387757 17196575556757755660145409)
    ·
      refine ⟨12897431667568316745109057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17196575556757755660145409 12897431667568316745109057)
      ·
        refine ⟨9673073750676237558831793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12897431667568316745109057 9673073750676237558831793)
        ·
          refine ⟨7254805313007178169123845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9673073750676237558831793 7254805313007178169123845)
          ·
            refine ⟨1360275996188845906710721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7254805313007178169123845 1360275996188845906710721)
            ·
              refine ⟨1020206997141634430033041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360275996188845906710721 1020206997141634430033041)
              ·
                refine ⟨765155247856225822524781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020206997141634430033041 765155247856225822524781)
                ·
                  refine ⟨286933217946084683446793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765155247856225822524781 286933217946084683446793)
                  ·
                    rfl

theorem cell21_1257301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1257301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257301 prefixEnd_1257301 := by exact prefixLift 1257301
  have htrace : WordTrace (prefixWord ++ tailWord_1257301) baseStart_1257301 baseEnd_1257301 := by
    simpa [prefixWord, tailWord_1257301, baseEnd_1257301] using wordTrace_append hprefix tailTrace_1257301
  have hstable : (prefixWord ++ tailWord_1257301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257301).length < 2 ^ (prefixWord ++ tailWord_1257301).sum := by decide
  have hdescent : baseEnd_1257301 < baseStart_1257301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257312 : List Nat := [2, 1, 1, 3, 3, 4, 1, 6]
def baseStart_1257312 : Nat := 118140960795 + 1257312 * 2 ^ 59
def prefixEnd_1257312 : Nat := 4983230072969 + 3 ^ 40 * 1257312 * 2
def baseEnd_1257312 : Nat := 95645242765317036254479

theorem tailTrace_1257312 : CollatzResearch.WordTrace tailWord_1257312 prefixEnd_1257312 95645242765317036254479 := by
  unfold tailWord_1257312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22928968010490415319519095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30571957347320553759358793 22928968010490415319519095)
  ·
    refine ⟨34393452015735622979278643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22928968010490415319519095 34393452015735622979278643)
    ·
      refine ⟨51590178023603434468917965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34393452015735622979278643 51590178023603434468917965)
      ·
        refine ⟨19346316758851287925844237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51590178023603434468917965 19346316758851287925844237)
        ·
          refine ⟨7254868784569232972191589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19346316758851287925844237 7254868784569232972191589)
          ·
            refine ⟨1360287897106731182285923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7254868784569232972191589 1360287897106731182285923)
            ·
              refine ⟨2040431845660096773428885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360287897106731182285923 2040431845660096773428885)
              ·
                refine ⟨95645242765317036254479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2040431845660096773428885 95645242765317036254479)
                ·
                  rfl

theorem cell21_1257312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_1257312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257312 prefixEnd_1257312 := by exact prefixLift 1257312
  have htrace : WordTrace (prefixWord ++ tailWord_1257312) baseStart_1257312 baseEnd_1257312 := by
    simpa [prefixWord, tailWord_1257312, baseEnd_1257312] using wordTrace_append hprefix tailTrace_1257312
  have hstable : (prefixWord ++ tailWord_1257312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257312).length < 2 ^ (prefixWord ++ tailWord_1257312).sum := by decide
  have hdescent : baseEnd_1257312 < baseStart_1257312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257385 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_1257385 : Nat := 118140960795 + 1257385 * 2 ^ 59
def prefixEnd_1257385 : Nat := 4983230072969 + 3 ^ 40 * 1257385 * 2
def baseEnd_1257385 : Nat := 286952387890519204046621

theorem tailTrace_1257385 : CollatzResearch.WordTrace tailWord_1257385 prefixEnd_1257385 286952387890519204046621 := by
  unfold tailWord_1257385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45860598549716364106445609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30573732366477576070963739 45860598549716364106445609)
  ·
    refine ⟨34395448912287273079834207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45860598549716364106445609 34395448912287273079834207)
    ·
      refine ⟨51593173368430909619751311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34395448912287273079834207 51593173368430909619751311)
      ·
        refine ⟨77389760052646364429626967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51593173368430909619751311 77389760052646364429626967)
        ·
          refine ⟨116084640078969546644440451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77389760052646364429626967 116084640078969546644440451)
          ·
            refine ⟨174126960118454319966660677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116084640078969546644440451 174126960118454319966660677)
            ·
              refine ⟨32648805022210184993748877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174126960118454319966660677 32648805022210184993748877)
              ·
                refine ⟨12243301883328819372655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32648805022210184993748877 12243301883328819372655829)
                ·
                  refine ⟨286952387890519204046621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12243301883328819372655829 286952387890519204046621)
                  ·
                    rfl

theorem cell21_1257385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_1257385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257385 prefixEnd_1257385 := by exact prefixLift 1257385
  have htrace : WordTrace (prefixWord ++ tailWord_1257385) baseStart_1257385 baseEnd_1257385 := by
    simpa [prefixWord, tailWord_1257385, baseEnd_1257385] using wordTrace_append hprefix tailTrace_1257385
  have hstable : (prefixWord ++ tailWord_1257385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257385).length < 2 ^ (prefixWord ++ tailWord_1257385).sum := by decide
  have hdescent : baseEnd_1257385 < baseStart_1257385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257470 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1257470 : Nat := 118140960795 + 1257470 * 2 ^ 59
def prefixEnd_1257470 : Nat := 4983230072969 + 3 ^ 40 * 1257470 * 2
def baseEnd_1257470 : Nat := 286971786048577945129781

theorem tailTrace_1257470 : CollatzResearch.WordTrace tailWord_1257470 prefixEnd_1257470 286971786048577945129781 := by
  unfold tailWord_1257470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732962344301052952911233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30575799169605615748859909 5732962344301052952911233)
  ·
    refine ⟨4299721758225789714683425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5732962344301052952911233 4299721758225789714683425)
    ·
      refine ⟨3224791318669342286012569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4299721758225789714683425 3224791318669342286012569)
      ·
        refine ⟨2418593489002006714509427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3224791318669342286012569 2418593489002006714509427)
        ·
          refine ⟨3627890233503010071764141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418593489002006714509427 3627890233503010071764141)
          ·
            refine ⟨1360458837563628776911553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3627890233503010071764141 1360458837563628776911553)
            ·
              refine ⟨1020344128172721582683665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360458837563628776911553 1020344128172721582683665)
              ·
                refine ⟨765258096129541187012749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020344128172721582683665 765258096129541187012749)
                ·
                  refine ⟨286971786048577945129781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765258096129541187012749 286971786048577945129781)
                  ·
                    rfl

theorem cell21_1257470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1257470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257470 prefixEnd_1257470 := by exact prefixLift 1257470
  have htrace : WordTrace (prefixWord ++ tailWord_1257470) baseStart_1257470 baseEnd_1257470 := by
    simpa [prefixWord, tailWord_1257470, baseEnd_1257470] using wordTrace_append hprefix tailTrace_1257470
  have hstable : (prefixWord ++ tailWord_1257470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257470).length < 2 ^ (prefixWord ++ tailWord_1257470).sum := by decide
  have hdescent : baseEnd_1257470 < baseStart_1257470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257495 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_1257495 : Nat := 118140960795 + 1257495 * 2 ^ 59
def prefixEnd_1257495 : Nat := 4983230072969 + 3 ^ 40 * 1257495 * 2
def baseEnd_1257495 : Nat := 286977491389183457213063

theorem tailTrace_1257495 : CollatzResearch.WordTrace tailWord_1257495 prefixEnd_1257495 286977491389183457213063 := by
  unfold tailWord_1257495
  simp only [CollatzResearch.WordTrace]
  refine ⟨45864610579317852892949939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30576407052878568595299959 45864610579317852892949939)
  ·
    refine ⟨68796915868976779339424909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45864610579317852892949939 68796915868976779339424909)
    ·
      refine ⟨25798843450866292252284341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68796915868976779339424909 25798843450866292252284341)
      ·
        refine ⟨2418641573518714898651657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25798843450866292252284341 2418641573518714898651657)
        ·
          refine ⟨1813981180139036173988743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418641573518714898651657 1813981180139036173988743)
          ·
            refine ⟨2720971770208554260983115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813981180139036173988743 2720971770208554260983115)
            ·
              refine ⟨4081457655312831391474673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720971770208554260983115 4081457655312831391474673)
              ·
                refine ⟨3061093241484623543606005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081457655312831391474673 3061093241484623543606005)
                ·
                  refine ⟨286977491389183457213063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061093241484623543606005 286977491389183457213063)
                  ·
                    rfl

theorem cell21_1257495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_1257495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257495 prefixEnd_1257495 := by exact prefixLift 1257495
  have htrace : WordTrace (prefixWord ++ tailWord_1257495) baseStart_1257495 baseEnd_1257495 := by
    simpa [prefixWord, tailWord_1257495, baseEnd_1257495] using wordTrace_append hprefix tailTrace_1257495
  have hstable : (prefixWord ++ tailWord_1257495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257495).length < 2 ^ (prefixWord ++ tailWord_1257495).sum := by decide
  have hdescent : baseEnd_1257495 < baseStart_1257495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257568 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_1257568 : Nat := 118140960795 + 1257568 * 2 ^ 59
def prefixEnd_1257568 : Nat := 4983230072969 + 3 ^ 40 * 1257568 * 2
def baseEnd_1257568 : Nat := 286994150983751552496247

theorem tailTrace_1257568 : CollatzResearch.WordTrace tailWord_1257568 prefixEnd_1257568 286994150983751552496247 := by
  unfold tailWord_1257568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933636554026693180178679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30578182072035590906904905 22933636554026693180178679)
  ·
    refine ⟨34400454831040039770268019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22933636554026693180178679 34400454831040039770268019)
    ·
      refine ⟨51600682246560059655402029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34400454831040039770268019 51600682246560059655402029)
      ·
        refine ⟨19350255842460022370775761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51600682246560059655402029 19350255842460022370775761)
        ·
          refine ⟨14512691881845016778081821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19350255842460022370775761 14512691881845016778081821)
          ·
            refine ⟨5442259455691881291780683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14512691881845016778081821 5442259455691881291780683)
            ·
              refine ⟨8163389183537821937671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442259455691881291780683 8163389183537821937671025)
              ·
                refine ⟨6122541887653366453253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8163389183537821937671025 6122541887653366453253269)
                ·
                  refine ⟨286994150983751552496247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6122541887653366453253269 286994150983751552496247)
                  ·
                    rfl

theorem cell21_1257568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_1257568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257568 prefixEnd_1257568 := by exact prefixLift 1257568
  have htrace : WordTrace (prefixWord ++ tailWord_1257568) baseStart_1257568 baseEnd_1257568 := by
    simpa [prefixWord, tailWord_1257568, baseEnd_1257568] using wordTrace_append hprefix tailTrace_1257568
  have hstable : (prefixWord ++ tailWord_1257568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257568).length < 2 ^ (prefixWord ++ tailWord_1257568).sum := by decide
  have hdescent : baseEnd_1257568 < baseStart_1257568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257571 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 3]
def baseStart_1257571 : Nat := 118140960795 + 1257571 * 2 ^ 59
def prefixEnd_1257571 : Nat := 4983230072969 + 3 ^ 40 * 1257571 * 2
def baseEnd_1257571 : Nat := 286994835624624213946241

theorem tailTrace_1257571 : CollatzResearch.WordTrace tailWord_1257571 prefixEnd_1257571 286994835624624213946241 := by
  unfold tailWord_1257571
  simp only [CollatzResearch.WordTrace]
  refine ⟨45867382527042517872716567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30578255018028345248477711 45867382527042517872716567)
  ·
    refine ⟨68801073790563776809074851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45867382527042517872716567 68801073790563776809074851)
    ·
      refine ⟨103201610685845665213612277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68801073790563776809074851 103201610685845665213612277)
      ·
        refine ⟨9675151001798031113776151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103201610685845665213612277 9675151001798031113776151)
        ·
          refine ⟨14512726502697046670664227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675151001798031113776151 14512726502697046670664227)
          ·
            refine ⟨21769089754045570005996341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512726502697046670664227 21769089754045570005996341)
            ·
              refine ⟨2040852164441772188062157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21769089754045570005996341 2040852164441772188062157)
              ·
                refine ⟨765319561665664570523309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2040852164441772188062157 765319561665664570523309)
                ·
                  refine ⟨286994835624624213946241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765319561665664570523309 286994835624624213946241)
                  ·
                    rfl

theorem cell21_1257571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].length) (baseStart_1257571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257571 prefixEnd_1257571 := by exact prefixLift 1257571
  have htrace : WordTrace (prefixWord ++ tailWord_1257571) baseStart_1257571 baseEnd_1257571 := by
    simpa [prefixWord, tailWord_1257571, baseEnd_1257571] using wordTrace_append hprefix tailTrace_1257571
  have hstable : (prefixWord ++ tailWord_1257571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257571).length < 2 ^ (prefixWord ++ tailWord_1257571).sum := by decide
  have hdescent : baseEnd_1257571 < baseStart_1257571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257675 : List Nat := [1, 1, 1, 1, 3, 2, 7, 5]
def baseStart_1257675 : Nat := 118140960795 + 1257675 * 2 ^ 59
def prefixEnd_1257675 : Nat := 4983230072969 + 3 ^ 40 * 1257675 * 2
def baseEnd_1257675 : Nat := 95672856613847714737565

theorem tailTrace_1257675 : CollatzResearch.WordTrace tailWord_1257675 prefixEnd_1257675 95672856613847714737565 := by
  unfold tailWord_1257675
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871175718665743634502479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30580783812443829089668319 45871175718665743634502479)
  ·
    refine ⟨68806763577998615451753719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45871175718665743634502479 68806763577998615451753719)
    ·
      refine ⟨103210145366997923177630579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68806763577998615451753719 103210145366997923177630579)
      ·
        refine ⟨154815218050496884766445869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103210145366997923177630579 154815218050496884766445869)
        ·
          refine ⟨58055706768936331787417201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154815218050496884766445869 58055706768936331787417201)
          ·
            refine ⟨43541780076702248840562901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58055706768936331787417201 43541780076702248840562901)
            ·
              refine ⟨1020510470547708957200693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43541780076702248840562901 1020510470547708957200693)
              ·
                refine ⟨95672856613847714737565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020510470547708957200693 95672856613847714737565)
                ·
                  rfl

theorem cell21_1257675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].length) (baseStart_1257675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257675 prefixEnd_1257675 := by exact prefixLift 1257675
  have htrace : WordTrace (prefixWord ++ tailWord_1257675) baseStart_1257675 baseEnd_1257675 := by
    simpa [prefixWord, tailWord_1257675, baseEnd_1257675] using wordTrace_append hprefix tailTrace_1257675
  have hstable : (prefixWord ++ tailWord_1257675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257675).length < 2 ^ (prefixWord ++ tailWord_1257675).sum := by decide
  have hdescent : baseEnd_1257675 < baseStart_1257675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257706 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1257706 : Nat := 118140960795 + 1257706 * 2 ^ 59
def prefixEnd_1257706 : Nat := 4983230072969 + 3 ^ 40 * 1257706 * 2
def baseEnd_1257706 : Nat := 287025644463893979195965

theorem tailTrace_1257706 : CollatzResearch.WordTrace tailWord_1257706 prefixEnd_1257706 287025644463893979195965 := by
  unfold tailWord_1257706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468076595388358982220243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30581537587702290619253981 11468076595388358982220243)
  ·
    refine ⟨17202114893082538473330365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11468076595388358982220243 17202114893082538473330365)
    ·
      refine ⟨6450793084905951927498887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17202114893082538473330365 6450793084905951927498887)
      ·
        refine ⟨9676189627358927891248331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450793084905951927498887 9676189627358927891248331)
        ·
          refine ⟨14514284441038391836872497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676189627358927891248331 14514284441038391836872497)
          ·
            refine ⟨10885713330778793877654373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14514284441038391836872497 10885713330778793877654373)
            ·
              refine ⟨2041071249521023852060195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10885713330778793877654373 2041071249521023852060195)
              ·
                refine ⟨3061606874281535778090293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041071249521023852060195 3061606874281535778090293)
                ·
                  refine ⟨287025644463893979195965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061606874281535778090293 287025644463893979195965)
                  ·
                    rfl

theorem cell21_1257706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1257706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257706 prefixEnd_1257706 := by exact prefixLift 1257706
  have htrace : WordTrace (prefixWord ++ tailWord_1257706) baseStart_1257706 baseEnd_1257706 := by
    simpa [prefixWord, tailWord_1257706, baseEnd_1257706] using wordTrace_append hprefix tailTrace_1257706
  have hstable : (prefixWord ++ tailWord_1257706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257706).length < 2 ^ (prefixWord ++ tailWord_1257706).sum := by decide
  have hdescent : baseEnd_1257706 < baseStart_1257706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257720 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1257720 : Nat := 118140960795 + 1257720 * 2 ^ 59
def prefixEnd_1257720 : Nat := 4983230072969 + 3 ^ 40 * 1257720 * 2
def baseEnd_1257720 : Nat := 287028839454633065962603

theorem tailTrace_1257720 : CollatzResearch.WordTrace tailWord_1257720 prefixEnd_1257720 287028839454633065962603 := by
  unfold tailWord_1257720
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936408501751358159945307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30581878002335144213260409 22936408501751358159945307)
  ·
    refine ⟨34404612752627037239917961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22936408501751358159945307 34404612752627037239917961)
    ·
      refine ⟨25803459564470277929938471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34404612752627037239917961 25803459564470277929938471)
      ·
        refine ⟨38705189346705416894907707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25803459564470277929938471 38705189346705416894907707)
        ·
          refine ⟨58057784020058125342361561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38705189346705416894907707 58057784020058125342361561)
          ·
            refine ⟨43543338015043594006771171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58057784020058125342361561 43543338015043594006771171)
            ·
              refine ⟨65315007022565391010156757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43543338015043594006771171 65315007022565391010156757)
              ·
                refine ⟨1530820477091376351800549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65315007022565391010156757 1530820477091376351800549)
                ·
                  refine ⟨287028839454633065962603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530820477091376351800549 287028839454633065962603)
                  ·
                    rfl

theorem cell21_1257720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1257720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257720 prefixEnd_1257720 := by exact prefixLift 1257720
  have htrace : WordTrace (prefixWord ++ tailWord_1257720) baseStart_1257720 baseEnd_1257720 := by
    simpa [prefixWord, tailWord_1257720, baseEnd_1257720] using wordTrace_append hprefix tailTrace_1257720
  have hstable : (prefixWord ++ tailWord_1257720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257720).length < 2 ^ (prefixWord ++ tailWord_1257720).sum := by decide
  have hdescent : baseEnd_1257720 < baseStart_1257720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257751 : List Nat := [1, 1, 3, 4, 1, 4, 7]
def baseStart_1257751 : Nat := 118140960795 + 1257751 * 2 ^ 59
def prefixEnd_1257751 : Nat := 4983230072969 + 3 ^ 40 * 1257751 * 2
def baseEnd_1257751 : Nat := 31892879341887100105097

theorem tailTrace_1257751 : CollatzResearch.WordTrace tailWord_1257751 prefixEnd_1257751 31892879341887100105097 := by
  unfold tailWord_1257751
  simp only [CollatzResearch.WordTrace]
  refine ⟨45873947666390408614269107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30582631777593605742846071 45873947666390408614269107)
  ·
    refine ⟨68810921499585612921403661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45873947666390408614269107 68810921499585612921403661)
    ·
      refine ⟨25804095562344604845526373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68810921499585612921403661 25804095562344604845526373)
      ·
        refine ⟨4838267917939613408536195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25804095562344604845526373 4838267917939613408536195)
        ·
          refine ⟨7257401876909420112804293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838267917939613408536195 7257401876909420112804293)
          ·
            refine ⟨1360762851920516271150805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7257401876909420112804293 1360762851920516271150805)
            ·
              refine ⟨31892879341887100105097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1360762851920516271150805 31892879341887100105097)
              ·
                rfl

theorem cell21_1257751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 7].length) (baseStart_1257751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257751 prefixEnd_1257751 := by exact prefixLift 1257751
  have htrace : WordTrace (prefixWord ++ tailWord_1257751) baseStart_1257751 baseEnd_1257751 := by
    simpa [prefixWord, tailWord_1257751, baseEnd_1257751] using wordTrace_append hprefix tailTrace_1257751
  have hstable : (prefixWord ++ tailWord_1257751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257751).length < 2 ^ (prefixWord ++ tailWord_1257751).sum := by decide
  have hdescent : baseEnd_1257751 < baseStart_1257751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257757 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1257757 : Nat := 118140960795 + 1257757 * 2 ^ 59
def prefixEnd_1257757 : Nat := 4983230072969 + 3 ^ 40 * 1257757 * 2
def baseEnd_1257757 : Nat := 287037283358729223845861

theorem tailTrace_1257757 : CollatzResearch.WordTrace tailWord_1257757 prefixEnd_1257757 287037283358729223845861 := by
  unfold tailWord_1257757
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874166504368671638987525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30582777669579114425991683 45874166504368671638987525)
  ·
    refine ⟨8601406219569125932310161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45874166504368671638987525 8601406219569125932310161)
    ·
      refine ⟨6451054664676844449232621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8601406219569125932310161 6451054664676844449232621)
      ·
        refine ⟨2419145499253816668462233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6451054664676844449232621 2419145499253816668462233)
        ·
          refine ⟨1814359124440362501346675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419145499253816668462233 1814359124440362501346675)
          ·
            refine ⟨2721538686660543752020013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814359124440362501346675 2721538686660543752020013)
            ·
              refine ⟨1020577007497703907007505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2721538686660543752020013 1020577007497703907007505)
              ·
                refine ⟨765432755623277930255629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020577007497703907007505 765432755623277930255629)
                ·
                  refine ⟨287037283358729223845861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765432755623277930255629 287037283358729223845861)
                  ·
                    rfl

theorem cell21_1257757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1257757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257757 prefixEnd_1257757 := by exact prefixLift 1257757
  have htrace : WordTrace (prefixWord ++ tailWord_1257757) baseStart_1257757 baseEnd_1257757 := by
    simpa [prefixWord, tailWord_1257757, baseEnd_1257757] using wordTrace_append hprefix tailTrace_1257757
  have hstable : (prefixWord ++ tailWord_1257757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257757).length < 2 ^ (prefixWord ++ tailWord_1257757).sum := by decide
  have hdescent : baseEnd_1257757 < baseStart_1257757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257768 : List Nat := [2, 1, 5, 1, 3, 1, 2, 6]
def baseStart_1257768 : Nat := 118140960795 + 1257768 * 2 ^ 59
def prefixEnd_1257768 : Nat := 4983230072969 + 3 ^ 40 * 1257768 * 2
def baseEnd_1257768 : Nat := 95679931236198549720835

theorem tailTrace_1257768 : CollatzResearch.WordTrace tailWord_1257768 prefixEnd_1257768 95679931236198549720835 := by
  unfold tailWord_1257768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22937283853664410258818979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30583045138219213678425305 22937283853664410258818979)
  ·
    refine ⟨34405925780496615388228469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22937283853664410258818979 34405925780496615388228469)
    ·
      refine ⟨3225555541921557692646419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34405925780496615388228469 3225555541921557692646419)
      ·
        refine ⟨4838333312882336538969629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225555541921557692646419 4838333312882336538969629)
        ·
          refine ⟨1814374992330876202113611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4838333312882336538969629 1814374992330876202113611)
          ·
            refine ⟨2721562488496314303170417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814374992330876202113611 2721562488496314303170417)
            ·
              refine ⟨2041171866372235727377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721562488496314303170417 2041171866372235727377813)
              ·
                refine ⟨95679931236198549720835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2041171866372235727377813 95679931236198549720835)
                ·
                  rfl

theorem cell21_1257768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_1257768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257768 prefixEnd_1257768 := by exact prefixLift 1257768
  have htrace : WordTrace (prefixWord ++ tailWord_1257768) baseStart_1257768 baseEnd_1257768 := by
    simpa [prefixWord, tailWord_1257768, baseEnd_1257768] using wordTrace_append hprefix tailTrace_1257768
  have hstable : (prefixWord ++ tailWord_1257768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257768).length < 2 ^ (prefixWord ++ tailWord_1257768).sum := by decide
  have hdescent : baseEnd_1257768 < baseStart_1257768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257855 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_1257855 : Nat := 118140960795 + 1257855 * 2 ^ 59
def prefixEnd_1257855 : Nat := 4983230072969 + 3 ^ 40 * 1257855 * 2
def baseEnd_1257855 : Nat := 287059648293902831212327

theorem tailTrace_1257855 : CollatzResearch.WordTrace tailWord_1257855 prefixEnd_1257855 287059648293902831212327 := by
  unfold tailWord_1257855
  simp only [CollatzResearch.WordTrace]
  refine ⟨45877740858013634376055019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30585160572009089584036679 45877740858013634376055019)
  ·
    refine ⟨68816611287020451564082529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45877740858013634376055019 68816611287020451564082529)
    ·
      refine ⟨51612458465265338673061897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68816611287020451564082529 51612458465265338673061897)
      ·
        refine ⟨38709343848949004004796423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51612458465265338673061897 38709343848949004004796423)
        ·
          refine ⟨58064015773423506007194635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38709343848949004004796423 58064015773423506007194635)
          ·
            refine ⟨87096023660135259010791953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58064015773423506007194635 87096023660135259010791953)
            ·
              refine ⟨65322017745101444258093965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87096023660135259010791953 65322017745101444258093965)
              ·
                refine ⟨24495756654413041596785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65322017745101444258093965 24495756654413041596785237)
                ·
                  refine ⟨287059648293902831212327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24495756654413041596785237 287059648293902831212327)
                  ·
                    rfl

theorem cell21_1257855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_1257855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257855 prefixEnd_1257855 := by exact prefixLift 1257855
  have htrace : WordTrace (prefixWord ++ tailWord_1257855) baseStart_1257855 baseEnd_1257855 := by
    simpa [prefixWord, tailWord_1257855, baseEnd_1257855] using wordTrace_append hprefix tailTrace_1257855
  have hstable : (prefixWord ++ tailWord_1257855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257855).length < 2 ^ (prefixWord ++ tailWord_1257855).sum := by decide
  have hdescent : baseEnd_1257855 < baseStart_1257855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1257909 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1257909 : Nat := 118140960795 + 1257909 * 2 ^ 59
def prefixEnd_1257909 : Nat := 4983230072969 + 3 ^ 40 * 1257909 * 2
def baseEnd_1257909 : Nat := 287071971829610737312217

theorem tailTrace_1257909 : CollatzResearch.WordTrace tailWord_1257909 prefixEnd_1257909 287071971829610737312217 := by
  unfold tailWord_1257909
  simp only [CollatzResearch.WordTrace]
  refine ⟨45879710399818001598520781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30586473599878667732347187 45879710399818001598520781)
  ·
    refine ⟨17204891399931750599445293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45879710399818001598520781 17204891399931750599445293)
    ·
      refine ⟨6451834274974406474791985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17204891399931750599445293 6451834274974406474791985)
      ·
        refine ⟨4838875706230804856093989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6451834274974406474791985 4838875706230804856093989)
        ·
          refine ⟨907289194918275910517623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4838875706230804856093989 907289194918275910517623)
          ·
            refine ⟨1360933792377413865776435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907289194918275910517623 1360933792377413865776435)
            ·
              refine ⟨2041400688566120798664653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360933792377413865776435 2041400688566120798664653)
              ·
                refine ⟨765525258212295299499245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041400688566120798664653 765525258212295299499245)
                ·
                  refine ⟨287071971829610737312217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765525258212295299499245 287071971829610737312217)
                  ·
                    rfl

theorem cell21_1257909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1257909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1257909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1257909 prefixEnd_1257909 := by exact prefixLift 1257909
  have htrace : WordTrace (prefixWord ++ tailWord_1257909) baseStart_1257909 baseEnd_1257909 := by
    simpa [prefixWord, tailWord_1257909, baseEnd_1257909] using wordTrace_append hprefix tailTrace_1257909
  have hstable : (prefixWord ++ tailWord_1257909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1257909).length < 2 ^ (prefixWord ++ tailWord_1257909).sum := by decide
  have hdescent : baseEnd_1257909 < baseStart_1257909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1257909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258069 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1258069 : Nat := 118140960795 + 1258069 * 2 ^ 59
def prefixEnd_1258069 : Nat := 4983230072969 + 3 ^ 40 * 1258069 * 2
def baseEnd_1258069 : Nat := 287108486009486014645223

theorem tailTrace_1258069 : CollatzResearch.WordTrace tailWord_1258069 prefixEnd_1258069 287108486009486014645223 := by
  unfold tailWord_1258069
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885546079238348924345261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590364052825565949563507 45885546079238348924345261)
  ·
    refine ⟨17207079779714380846629473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45885546079238348924345261 17207079779714380846629473)
    ·
      refine ⟨12905309834785785634972105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17207079779714380846629473 12905309834785785634972105)
      ·
        refine ⟨9678982376089339226229079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12905309834785785634972105 9678982376089339226229079)
        ·
          refine ⟨14518473564134008839343619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9678982376089339226229079 14518473564134008839343619)
          ·
            refine ⟨21777710346201013259015429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14518473564134008839343619 21777710346201013259015429)
            ·
              refine ⟨4083320689912689986065393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21777710346201013259015429 4083320689912689986065393)
              ·
                refine ⟨3062490517434517489549045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083320689912689986065393 3062490517434517489549045)
                ·
                  refine ⟨287108486009486014645223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3062490517434517489549045 287108486009486014645223)
                  ·
                    rfl

theorem cell21_1258069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1258069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258069 prefixEnd_1258069 := by exact prefixLift 1258069
  have htrace : WordTrace (prefixWord ++ tailWord_1258069) baseStart_1258069 baseEnd_1258069 := by
    simpa [prefixWord, tailWord_1258069, baseEnd_1258069] using wordTrace_append hprefix tailTrace_1258069
  have hstable : (prefixWord ++ tailWord_1258069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258069).length < 2 ^ (prefixWord ++ tailWord_1258069).sum := by decide
  have hdescent : baseEnd_1258069 < baseStart_1258069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258083 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_1258083 : Nat := 118140960795 + 1258083 * 2 ^ 59
def prefixEnd_1258083 : Nat := 4983230072969 + 3 ^ 40 * 1258083 * 2
def baseEnd_1258083 : Nat := 287111681000225101411861

theorem tailTrace_1258083 : CollatzResearch.WordTrace tailWord_1258083 prefixEnd_1258083 287111681000225101411861 := by
  unfold tailWord_1258083
  simp only [CollatzResearch.WordTrace]
  refine ⟨45886056701187629315354903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30590704467458419543569935 45886056701187629315354903)
  ·
    refine ⟨68829085051781443973032355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45886056701187629315354903 68829085051781443973032355)
    ·
      refine ⟨103243627577672165959548533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68829085051781443973032355 103243627577672165959548533)
      ·
        refine ⟨9679090085406765558707675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103243627577672165959548533 9679090085406765558707675)
        ·
          refine ⟨14518635128110148338061513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679090085406765558707675 14518635128110148338061513)
          ·
            refine ⟨10888976346082611253546135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14518635128110148338061513 10888976346082611253546135)
            ·
              refine ⟨16333464519123916880319203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888976346082611253546135 16333464519123916880319203)
              ·
                refine ⟨24500196778685875320478805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16333464519123916880319203 24500196778685875320478805)
                ·
                  refine ⟨287111681000225101411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24500196778685875320478805 287111681000225101411861)
                  ·
                    rfl

theorem cell21_1258083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_1258083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258083 prefixEnd_1258083 := by exact prefixLift 1258083
  have htrace : WordTrace (prefixWord ++ tailWord_1258083) baseStart_1258083 baseEnd_1258083 := by
    simpa [prefixWord, tailWord_1258083, baseEnd_1258083] using wordTrace_append hprefix tailTrace_1258083
  have hstable : (prefixWord ++ tailWord_1258083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258083).length < 2 ^ (prefixWord ++ tailWord_1258083).sum := by decide
  have hdescent : baseEnd_1258083 < baseStart_1258083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258117 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1258117 : Nat := 118140960795 + 1258117 * 2 ^ 59
def prefixEnd_1258117 : Nat := 4983230072969 + 3 ^ 40 * 1258117 * 2
def baseEnd_1258117 : Nat := 287119440263448597845125

theorem tailTrace_1258117 : CollatzResearch.WordTrace tailWord_1258117 prefixEnd_1258117 287119440263448597845125 := by
  unfold tailWord_1258117
  simp only [CollatzResearch.WordTrace]
  refine ⟨45887296783064453122092605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30591531188709635414728403 45887296783064453122092605)
  ·
    refine ⟨17207736293649169920784727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45887296783064453122092605 17207736293649169920784727)
    ·
      refine ⟨25811604440473754881177091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207736293649169920784727 25811604440473754881177091)
      ·
        refine ⟨38717406660710632321765637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25811604440473754881177091 38717406660710632321765637)
        ·
          refine ⟨7259513748883243560331057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38717406660710632321765637 7259513748883243560331057)
          ·
            refine ⟨5444635311662432670248293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259513748883243560331057 5444635311662432670248293)
            ·
              refine ⟨1020869120936706125671555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5444635311662432670248293 1020869120936706125671555)
              ·
                refine ⟨1531303681405059188507333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020869120936706125671555 1531303681405059188507333)
                ·
                  refine ⟨287119440263448597845125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531303681405059188507333 287119440263448597845125)
                  ·
                    rfl

theorem cell21_1258117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1258117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258117 prefixEnd_1258117 := by exact prefixLift 1258117
  have htrace : WordTrace (prefixWord ++ tailWord_1258117) baseStart_1258117 baseEnd_1258117 := by
    simpa [prefixWord, tailWord_1258117, baseEnd_1258117] using wordTrace_append hprefix tailTrace_1258117
  have hstable : (prefixWord ++ tailWord_1258117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258117).length < 2 ^ (prefixWord ++ tailWord_1258117).sum := by decide
  have hdescent : baseEnd_1258117 < baseStart_1258117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258154 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_1258154 : Nat := 118140960795 + 1258154 * 2 ^ 59
def prefixEnd_1258154 : Nat := 4983230072969 + 3 ^ 40 * 1258154 * 2
def baseEnd_1258154 : Nat := 287127884167544755728383

theorem tailTrace_1258154 : CollatzResearch.WordTrace tailWord_1258154 prefixEnd_1258154 287127884167544755728383 := by
  unfold tailWord_1258154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11472161570982602110297379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30592430855953605627459677 11472161570982602110297379)
  ·
    refine ⟨17208242356473903165446069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11472161570982602110297379 17208242356473903165446069)
    ·
      refine ⟨1613272720919428421760569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17208242356473903165446069 1613272720919428421760569)
      ·
        refine ⟨1209954540689571316320427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613272720919428421760569 1209954540689571316320427)
        ·
          refine ⟨1814931811034356974480641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209954540689571316320427 1814931811034356974480641)
          ·
            refine ⟨1361198858275767730860481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814931811034356974480641 1361198858275767730860481)
            ·
              refine ⟨1020899143706825798145361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361198858275767730860481 1020899143706825798145361)
              ·
                refine ⟨765674357780119348609021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020899143706825798145361 765674357780119348609021)
                ·
                  refine ⟨287127884167544755728383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765674357780119348609021 287127884167544755728383)
                  ·
                    rfl

theorem cell21_1258154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_1258154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258154 prefixEnd_1258154 := by exact prefixLift 1258154
  have htrace : WordTrace (prefixWord ++ tailWord_1258154) baseStart_1258154 baseEnd_1258154 := by
    simpa [prefixWord, tailWord_1258154, baseEnd_1258154] using wordTrace_append hprefix tailTrace_1258154
  have hstable : (prefixWord ++ tailWord_1258154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258154).length < 2 ^ (prefixWord ++ tailWord_1258154).sum := by decide
  have hdescent : baseEnd_1258154 < baseStart_1258154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258176 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1258176 : Nat := 118140960795 + 1258176 * 2 ^ 59
def prefixEnd_1258176 : Nat := 4983230072969 + 3 ^ 40 * 1258176 * 2
def baseEnd_1258176 : Nat := 287132904867277606361671

theorem tailTrace_1258176 : CollatzResearch.WordTrace tailWord_1258176 prefixEnd_1258176 287132904867277606361671 := by
  unfold tailWord_1258176
  simp only [CollatzResearch.WordTrace]
  refine ⟨22944724344925353099245191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30592965793233804132326921 22944724344925353099245191)
  ·
    refine ⟨34417086517388029648867787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22944724344925353099245191 34417086517388029648867787)
    ·
      refine ⟨51625629776082044473301681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34417086517388029648867787 51625629776082044473301681)
      ·
        refine ⟨38719222332061533354976261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51625629776082044473301681 38719222332061533354976261)
        ·
          refine ⟨7259854187261537504058049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38719222332061533354976261 7259854187261537504058049)
          ·
            refine ⟨5444890640446153128043537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259854187261537504058049 5444890640446153128043537)
            ·
              refine ⟨4083667980334614846032653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444890640446153128043537 4083667980334614846032653)
              ·
                refine ⟨1531375492625480567262245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4083667980334614846032653 1531375492625480567262245)
                ·
                  refine ⟨287132904867277606361671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531375492625480567262245 287132904867277606361671)
                  ·
                    rfl

theorem cell21_1258176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1258176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258176 prefixEnd_1258176 := by exact prefixLift 1258176
  have htrace : WordTrace (prefixWord ++ tailWord_1258176) baseStart_1258176 baseEnd_1258176 := by
    simpa [prefixWord, tailWord_1258176, baseEnd_1258176] using wordTrace_append hprefix tailTrace_1258176
  have hstable : (prefixWord ++ tailWord_1258176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258176).length < 2 ^ (prefixWord ++ tailWord_1258176).sum := by decide
  have hdescent : baseEnd_1258176 < baseStart_1258176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258182 : List Nat := [6, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1258182 : Nat := 118140960795 + 1258182 * 2 ^ 59
def prefixEnd_1258182 : Nat := 4983230072969 + 3 ^ 40 * 1258182 * 2
def baseEnd_1258182 : Nat := 95711424716340976420553

theorem tailTrace_1258182 : CollatzResearch.WordTrace tailWord_1258182 prefixEnd_1258182 95711424716340976420553 := by
  unfold tailWord_1258182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434052110244655288225275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30593111685219312815472533 1434052110244655288225275)
  ·
    refine ⟨2151078165366982932337913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434052110244655288225275 2151078165366982932337913)
    ·
      refine ⟨1613308624025237199253435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151078165366982932337913 1613308624025237199253435)
      ·
        refine ⟨2419962936037855798880153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613308624025237199253435 2419962936037855798880153)
        ·
          refine ⟨1814972202028391849160115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419962936037855798880153 1814972202028391849160115)
          ·
            refine ⟨2722458303042587773740173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814972202028391849160115 2722458303042587773740173)
            ·
              refine ⟨1020921863640970415152565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2722458303042587773740173 1020921863640970415152565)
              ·
                refine ⟨95711424716340976420553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020921863640970415152565 95711424716340976420553)
                ·
                  rfl

theorem cell21_1258182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1258182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258182 prefixEnd_1258182 := by exact prefixLift 1258182
  have htrace : WordTrace (prefixWord ++ tailWord_1258182) baseStart_1258182 baseEnd_1258182 := by
    simpa [prefixWord, tailWord_1258182, baseEnd_1258182] using wordTrace_append hprefix tailTrace_1258182
  have hstable : (prefixWord ++ tailWord_1258182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258182).length < 2 ^ (prefixWord ++ tailWord_1258182).sum := by decide
  have hdescent : baseEnd_1258182 < baseStart_1258182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258196 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1258196 : Nat := 118140960795 + 1258196 * 2 ^ 59
def prefixEnd_1258196 : Nat := 4983230072969 + 3 ^ 40 * 1258196 * 2
def baseEnd_1258196 : Nat := 287137469139762016028297

theorem tailTrace_1258196 : CollatzResearch.WordTrace tailWord_1258196 prefixEnd_1258196 287137469139762016028297 := by
  unfold tailWord_1258196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945089074889124807109221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30593452099852166409478961 22945089074889124807109221)
  ·
    refine ⟨4302204201541710901332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22945089074889124807109221 4302204201541710901332979)
    ·
      refine ⟨6453306302312566351999469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302204201541710901332979 6453306302312566351999469)
      ·
        refine ⟨2419989863367212381999801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6453306302312566351999469 2419989863367212381999801)
        ·
          refine ⟨1814992397525409286499851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419989863367212381999801 1814992397525409286499851)
          ·
            refine ⟨2722488596288113929749777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814992397525409286499851 2722488596288113929749777)
            ·
              refine ⟨2041866447216085447312333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722488596288113929749777 2041866447216085447312333)
              ·
                refine ⟨765699917706032042742125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041866447216085447312333 765699917706032042742125)
                ·
                  refine ⟨287137469139762016028297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765699917706032042742125 287137469139762016028297)
                  ·
                    rfl

theorem cell21_1258196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1258196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258196 prefixEnd_1258196 := by exact prefixLift 1258196
  have htrace : WordTrace (prefixWord ++ tailWord_1258196) baseStart_1258196 baseEnd_1258196 := by
    simpa [prefixWord, tailWord_1258196, baseEnd_1258196] using wordTrace_append hprefix tailTrace_1258196
  have hstable : (prefixWord ++ tailWord_1258196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258196).length < 2 ^ (prefixWord ++ tailWord_1258196).sum := by decide
  have hdescent : baseEnd_1258196 < baseStart_1258196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258238 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1258238 : Nat := 118140960795 + 1258238 * 2 ^ 59
def prefixEnd_1258238 : Nat := 4983230072969 + 3 ^ 40 * 1258238 * 2
def baseEnd_1258238 : Nat := 287147054111979276328211

theorem tailTrace_1258238 : CollatzResearch.WordTrace tailWord_1258238 prefixEnd_1258238 287147054111979276328211 := by
  unfold tailWord_1258238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736463751953261348405921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30594473343750727191498245 5736463751953261348405921)
  ·
    refine ⟨4302347813964946011304441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5736463751953261348405921 4302347813964946011304441)
    ·
      refine ⟨3226760860473709508478331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4302347813964946011304441 3226760860473709508478331)
      ·
        refine ⟨4840141290710564262717497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226760860473709508478331 4840141290710564262717497)
        ·
          refine ⟨3630105968032923197038123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4840141290710564262717497 3630105968032923197038123)
          ·
            refine ⟨5445158952049384795557185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630105968032923197038123 5445158952049384795557185)
            ·
              refine ⟨4083869214037038596667889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5445158952049384795557185 4083869214037038596667889)
              ·
                refine ⟨3062901910527778947500917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083869214037038596667889 3062901910527778947500917)
                ·
                  refine ⟨287147054111979276328211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3062901910527778947500917 287147054111979276328211)
                  ·
                    rfl

theorem cell21_1258238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1258238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258238 prefixEnd_1258238 := by exact prefixLift 1258238
  have htrace : WordTrace (prefixWord ++ tailWord_1258238) baseStart_1258238 baseEnd_1258238 := by
    simpa [prefixWord, tailWord_1258238, baseEnd_1258238] using wordTrace_append hprefix tailTrace_1258238
  have hstable : (prefixWord ++ tailWord_1258238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258238).length < 2 ^ (prefixWord ++ tailWord_1258238).sum := by decide
  have hdescent : baseEnd_1258238 < baseStart_1258238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258286 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_1258286 : Nat := 118140960795 + 1258286 * 2 ^ 59
def prefixEnd_1258286 : Nat := 4983230072969 + 3 ^ 40 * 1258286 * 2
def baseEnd_1258286 : Nat := 287158008365941859528113

theorem tailTrace_1258286 : CollatzResearch.WordTrace tailWord_1258286 prefixEnd_1258286 287158008365941859528113 := by
  unfold tailWord_1258286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736682589931524373124339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30595640479634796656663141 5736682589931524373124339)
  ·
    refine ⟨8605023884897286559686509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5736682589931524373124339 8605023884897286559686509)
    ·
      refine ⟨3226883956836482459882441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8605023884897286559686509 3226883956836482459882441)
      ·
        refine ⟨2420162967627361844911831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3226883956836482459882441 2420162967627361844911831)
        ·
          refine ⟨3630244451441042767367747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420162967627361844911831 3630244451441042767367747)
          ·
            refine ⟨5445366677161564151051621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630244451441042767367747 5445366677161564151051621)
            ·
              refine ⟨1021006251967793278322179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5445366677161564151051621 1021006251967793278322179)
              ·
                refine ⟨1531509377951689917483269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021006251967793278322179 1531509377951689917483269)
                ·
                  refine ⟨287158008365941859528113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531509377951689917483269 287158008365941859528113)
                  ·
                    rfl

theorem cell21_1258286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_1258286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258286 prefixEnd_1258286 := by exact prefixLift 1258286
  have htrace : WordTrace (prefixWord ++ tailWord_1258286) baseStart_1258286 baseEnd_1258286 := by
    simpa [prefixWord, tailWord_1258286, baseEnd_1258286] using wordTrace_append hprefix tailTrace_1258286
  have hstable : (prefixWord ++ tailWord_1258286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258286).length < 2 ^ (prefixWord ++ tailWord_1258286).sum := by decide
  have hdescent : baseEnd_1258286 < baseStart_1258286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258387 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_1258387 : Nat := 118140960795 + 1258387 * 2 ^ 59
def prefixEnd_1258387 : Nat := 4983230072969 + 3 ^ 40 * 1258387 * 2
def baseEnd_1258387 : Nat := 287181057941988128344573

theorem tailTrace_1258387 : CollatzResearch.WordTrace tailWord_1258387 prefixEnd_1258387 287181057941988128344573 := by
  unfold tailWord_1258387
  simp only [CollatzResearch.WordTrace]
  refine ⟨45897144492086289234421415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30598096328057526156280943 45897144492086289234421415)
  ·
    refine ⟨68845716738129433851632123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45897144492086289234421415 68845716738129433851632123)
    ·
      refine ⟨103268575107194150777448185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68845716738129433851632123 103268575107194150777448185)
      ·
        refine ⟨77451431330395613083086139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103268575107194150777448185 77451431330395613083086139)
        ·
          refine ⟨116177146995593419624629209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77451431330395613083086139 116177146995593419624629209)
          ·
            refine ⟨87132860246695064718471907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116177146995593419624629209 87132860246695064718471907)
            ·
              refine ⟨130699290370042597077707861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87132860246695064718471907 130699290370042597077707861)
              ·
                refine ⟨1531632309023936684504389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 130699290370042597077707861 1531632309023936684504389)
                ·
                  refine ⟨287181057941988128344573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531632309023936684504389 287181057941988128344573)
                  ·
                    rfl

theorem cell21_1258387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_1258387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258387 prefixEnd_1258387 := by exact prefixLift 1258387
  have htrace : WordTrace (prefixWord ++ tailWord_1258387) baseStart_1258387 baseEnd_1258387 := by
    simpa [prefixWord, tailWord_1258387, baseEnd_1258387] using wordTrace_append hprefix tailTrace_1258387
  have hstable : (prefixWord ++ tailWord_1258387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258387).length < 2 ^ (prefixWord ++ tailWord_1258387).sum := by decide
  have hdescent : baseEnd_1258387 < baseStart_1258387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258494 : List Nat := [4, 2, 2, 2, 11]
def baseStart_1258494 : Nat := 118140960795 + 1258494 * 2 ^ 59
def prefixEnd_1258494 : Nat := 4983230072969 + 3 ^ 40 * 1258494 * 2
def baseEnd_1258494 : Nat := 3545746627157774321741

theorem tailTrace_1258494 : CollatzResearch.WordTrace tailWord_1258494 prefixEnd_1258494 3545746627157774321741 := by
  unfold tailWord_1258494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737630887837330813570817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30600698068465764339044357 5737630887837330813570817)
  ·
    refine ⟨4303223165877998110178113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5737630887837330813570817 4303223165877998110178113)
    ·
      refine ⟨3227417374408498582633585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4303223165877998110178113 3227417374408498582633585)
      ·
        refine ⟨2420563030806373936975189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3227417374408498582633585 2420563030806373936975189)
        ·
          refine ⟨3545746627157774321741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2420563030806373936975189 3545746627157774321741)
          ·
            rfl

theorem cell21_1258494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 11].length) (baseStart_1258494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258494 prefixEnd_1258494 := by exact prefixLift 1258494
  have htrace : WordTrace (prefixWord ++ tailWord_1258494) baseStart_1258494 baseEnd_1258494 := by
    simpa [prefixWord, tailWord_1258494, baseEnd_1258494] using wordTrace_append hprefix tailTrace_1258494
  have hstable : (prefixWord ++ tailWord_1258494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258494).length < 2 ^ (prefixWord ++ tailWord_1258494).sum := by decide
  have hdescent : baseEnd_1258494 < baseStart_1258494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258528 : List Nat := [2, 1, 1, 7, 1, 1, 3, 5]
def baseStart_1258528 : Nat := 118140960795 + 1258528 * 2 ^ 59
def prefixEnd_1258528 : Nat := 4983230072969 + 3 ^ 40 * 1258528 * 2
def baseEnd_1258528 : Nat := 95737745354334405498095

theorem tailTrace_1258528 : CollatzResearch.WordTrace tailWord_1258528 prefixEnd_1258528 95737745354334405498095 := by
  unfold tailWord_1258528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22951143592287735157652119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30601524789716980210202825 22951143592287735157652119)
  ·
    refine ⟨34426715388431602736478179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22951143592287735157652119 34426715388431602736478179)
    ·
      refine ⟨51640073082647404104717269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34426715388431602736478179 51640073082647404104717269)
      ·
        refine ⟨1210314212874548533704311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 51640073082647404104717269 1210314212874548533704311)
        ·
          refine ⟨1815471319311822800556467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210314212874548533704311 1815471319311822800556467)
          ·
            refine ⟨2723206978967734200834701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815471319311822800556467 2723206978967734200834701)
            ·
              refine ⟨1021202617112900325313013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2723206978967734200834701 1021202617112900325313013)
              ·
                refine ⟨95737745354334405498095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021202617112900325313013 95737745354334405498095)
                ·
                  rfl

theorem cell21_1258528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_1258528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258528 prefixEnd_1258528 := by exact prefixLift 1258528
  have htrace : WordTrace (prefixWord ++ tailWord_1258528) baseStart_1258528 baseEnd_1258528 := by
    simpa [prefixWord, tailWord_1258528, baseEnd_1258528] using wordTrace_append hprefix tailTrace_1258528
  have hstable : (prefixWord ++ tailWord_1258528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258528).length < 2 ^ (prefixWord ++ tailWord_1258528).sum := by decide
  have hdescent : baseEnd_1258528 < baseStart_1258528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258556 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_1258556 : Nat := 118140960795 + 1258556 * 2 ^ 59
def prefixEnd_1258556 : Nat := 4983230072969 + 3 ^ 40 * 1258556 * 2
def baseEnd_1258556 : Nat := 287219626044481390027561

theorem tailTrace_1258556 : CollatzResearch.WordTrace tailWord_1258556 prefixEnd_1258556 287219626044481390027561 := by
  unfold tailWord_1258556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22951654214237015548661761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30602205618982687398215681 22951654214237015548661761)
  ·
    refine ⟨17213740660677761661496321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22951654214237015548661761 17213740660677761661496321)
    ·
      refine ⟨12910305495508321246122241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17213740660677761661496321 12910305495508321246122241)
      ·
        refine ⟨9682729121631240934591681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12910305495508321246122241 9682729121631240934591681)
        ·
          refine ⟨7262046841223430700943761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9682729121631240934591681 7262046841223430700943761)
          ·
            refine ⟨5446535130917573025707821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7262046841223430700943761 5446535130917573025707821)
            ·
              refine ⟨2042450674094089884640433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5446535130917573025707821 2042450674094089884640433)
              ·
                refine ⟨1531838005570567413480325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042450674094089884640433 1531838005570567413480325)
                ·
                  refine ⟨287219626044481390027561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531838005570567413480325 287219626044481390027561)
                  ·
                    rfl

theorem cell21_1258556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_1258556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258556 prefixEnd_1258556 := by exact prefixLift 1258556
  have htrace : WordTrace (prefixWord ++ tailWord_1258556) baseStart_1258556 baseEnd_1258556 := by
    simpa [prefixWord, tailWord_1258556, baseEnd_1258556] using wordTrace_append hprefix tailTrace_1258556
  have hstable : (prefixWord ++ tailWord_1258556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258556).length < 2 ^ (prefixWord ++ tailWord_1258556).sum := by decide
  have hdescent : baseEnd_1258556 < baseStart_1258556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258584 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1258584 : Nat := 118140960795 + 1258584 * 2 ^ 59
def prefixEnd_1258584 : Nat := 4983230072969 + 3 ^ 40 * 1258584 * 2
def baseEnd_1258584 : Nat := 287226016025959563560837

theorem tailTrace_1258584 : CollatzResearch.WordTrace tailWord_1258584 prefixEnd_1258584 287226016025959563560837 := by
  unfold tailWord_1258584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952164836186295939671403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30602886448248394586228537 22952164836186295939671403)
  ·
    refine ⟨34428247254279443909507105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952164836186295939671403 34428247254279443909507105)
    ·
      refine ⟨25821185440709582932130329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34428247254279443909507105 25821185440709582932130329)
      ·
        refine ⟨19365889080532187199097747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25821185440709582932130329 19365889080532187199097747)
        ·
          refine ⟨29048833620798280798646621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365889080532187199097747 29048833620798280798646621)
          ·
            refine ⟨10893312607799355299492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29048833620798280798646621 10893312607799355299492483)
            ·
              refine ⟨16339968911699032949238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10893312607799355299492483 16339968911699032949238725)
              ·
                refine ⟨3063744170943568677982261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16339968911699032949238725 3063744170943568677982261)
                ·
                  refine ⟨287226016025959563560837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3063744170943568677982261 287226016025959563560837)
                  ·
                    rfl

theorem cell21_1258584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1258584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258584 prefixEnd_1258584 := by exact prefixLift 1258584
  have htrace : WordTrace (prefixWord ++ tailWord_1258584) baseStart_1258584 baseEnd_1258584 := by
    simpa [prefixWord, tailWord_1258584, baseEnd_1258584] using wordTrace_append hprefix tailTrace_1258584
  have hstable : (prefixWord ++ tailWord_1258584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258584).length < 2 ^ (prefixWord ++ tailWord_1258584).sum := by decide
  have hdescent : baseEnd_1258584 < baseStart_1258584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258615 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_1258615 : Nat := 118140960795 + 1258615 * 2 ^ 59
def prefixEnd_1258615 : Nat := 4983230072969 + 3 ^ 40 * 1258615 * 2
def baseEnd_1258615 : Nat := 287233090648310398544107

theorem tailTrace_1258615 : CollatzResearch.WordTrace tailWord_1258615 prefixEnd_1258615 287233090648310398544107 := by
  unfold tailWord_1258615
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905460335260284173721299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30603640223506856115814199 45905460335260284173721299)
  ·
    refine ⟨68858190502890426260581949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45905460335260284173721299 68858190502890426260581949)
    ·
      refine ⟨25821821438583909847718231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68858190502890426260581949 25821821438583909847718231)
      ·
        refine ⟨38732732157875864771577347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25821821438583909847718231 38732732157875864771577347)
        ·
          refine ⟨58099098236813797157366021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38732732157875864771577347 58099098236813797157366021)
          ·
            refine ⟨10893580919402586967006129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58099098236813797157366021 10893580919402586967006129)
            ·
              refine ⟨8170185689551940225254597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10893580919402586967006129 8170185689551940225254597)
              ·
                refine ⟨1531909816790988792235237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8170185689551940225254597 1531909816790988792235237)
                ·
                  refine ⟨287233090648310398544107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531909816790988792235237 287233090648310398544107)
                  ·
                    rfl

theorem cell21_1258615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_1258615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258615 prefixEnd_1258615 := by exact prefixLift 1258615
  have htrace : WordTrace (prefixWord ++ tailWord_1258615) baseStart_1258615 baseEnd_1258615 := by
    simpa [prefixWord, tailWord_1258615, baseEnd_1258615] using wordTrace_append hprefix tailTrace_1258615
  have hstable : (prefixWord ++ tailWord_1258615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258615).length < 2 ^ (prefixWord ++ tailWord_1258615).sum := by decide
  have hdescent : baseEnd_1258615 < baseStart_1258615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258669 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1258669 : Nat := 118140960795 + 1258669 * 2 ^ 59
def prefixEnd_1258669 : Nat := 4983230072969 + 3 ^ 40 * 1258669 * 2
def baseEnd_1258669 : Nat := 287245414184018304643997

theorem tailTrace_1258669 : CollatzResearch.WordTrace tailWord_1258669 prefixEnd_1258669 287245414184018304643997 := by
  unfold tailWord_1258669
  simp only [CollatzResearch.WordTrace]
  refine ⟨45907429877064651396187061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30604953251376434264124707 45907429877064651396187061)
  ·
    refine ⟨4303821550974811068392537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45907429877064651396187061 4303821550974811068392537)
    ·
      refine ⟨3227866163231108301294403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4303821550974811068392537 3227866163231108301294403)
      ·
        refine ⟨4841799244846662451941605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227866163231108301294403 4841799244846662451941605)
        ·
          refine ⟨907837358408749209739051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4841799244846662451941605 907837358408749209739051)
          ·
            refine ⟨1361756037613123814608577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907837358408749209739051 1361756037613123814608577)
            ·
              refine ⟨1021317028209842860956433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361756037613123814608577 1021317028209842860956433)
              ·
                refine ⟨765987771157382145717325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021317028209842860956433 765987771157382145717325)
                ·
                  refine ⟨287245414184018304643997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765987771157382145717325 287245414184018304643997)
                  ·
                    rfl

theorem cell21_1258669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1258669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258669 prefixEnd_1258669 := by exact prefixLift 1258669
  have htrace : WordTrace (prefixWord ++ tailWord_1258669) baseStart_1258669 baseEnd_1258669 := by
    simpa [prefixWord, tailWord_1258669, baseEnd_1258669] using wordTrace_append hprefix tailTrace_1258669
  have hstable : (prefixWord ++ tailWord_1258669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258669).length < 2 ^ (prefixWord ++ tailWord_1258669).sum := by decide
  have hdescent : baseEnd_1258669 < baseStart_1258669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258725 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1258725 : Nat := 118140960795 + 1258725 * 2 ^ 59
def prefixEnd_1258725 : Nat := 4983230072969 + 3 ^ 40 * 1258725 * 2
def baseEnd_1258725 : Nat := 287258194146974651710549

theorem tailTrace_1258725 : CollatzResearch.WordTrace tailWord_1258725 prefixEnd_1258725 287258194146974651710549 := by
  unfold tailWord_1258725
  simp only [CollatzResearch.WordTrace]
  refine ⟨45909472364861772960225629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30606314909907848640150419 45909472364861772960225629)
  ·
    refine ⟨17216052136823164860084611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45909472364861772960225629 17216052136823164860084611)
    ·
      refine ⟨25824078205234747290126917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17216052136823164860084611 25824078205234747290126917)
      ·
        refine ⟨4842014663481515116898797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25824078205234747290126917 4842014663481515116898797)
        ·
          refine ⟨1815755498805568168837049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4842014663481515116898797 1815755498805568168837049)
          ·
            refine ⟨1361816624104176126627787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815755498805568168837049 1361816624104176126627787)
            ·
              refine ⟨2042724936156264189941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361816624104176126627787 2042724936156264189941681)
              ·
                refine ⟨1532043702117198142456261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042724936156264189941681 1532043702117198142456261)
                ·
                  refine ⟨287258194146974651710549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532043702117198142456261 287258194146974651710549)
                  ·
                    rfl

theorem cell21_1258725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1258725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258725 prefixEnd_1258725 := by exact prefixLift 1258725
  have htrace : WordTrace (prefixWord ++ tailWord_1258725) baseStart_1258725 baseEnd_1258725 := by
    simpa [prefixWord, tailWord_1258725, baseEnd_1258725] using wordTrace_append hprefix tailTrace_1258725
  have hstable : (prefixWord ++ tailWord_1258725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258725).length < 2 ^ (prefixWord ++ tailWord_1258725).sum := by decide
  have hdescent : baseEnd_1258725 < baseStart_1258725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258795 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_1258795 : Nat := 118140960795 + 1258795 * 2 ^ 59
def prefixEnd_1258795 : Nat := 4983230072969 + 3 ^ 40 * 1258795 * 2
def baseEnd_1258795 : Nat := 287274169100670085543739

theorem tailTrace_1258795 : CollatzResearch.WordTrace tailWord_1258795 prefixEnd_1258795 287274169100670085543739 := by
  unfold tailWord_1258795
  simp only [CollatzResearch.WordTrace]
  refine ⟨45912025474608174915273839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30608016983072116610182559 45912025474608174915273839)
  ·
    refine ⟨68868038211912262372910759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45912025474608174915273839 68868038211912262372910759)
    ·
      refine ⟨103302057317868393559366139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68868038211912262372910759 103302057317868393559366139)
      ·
        refine ⟨154953085976802590339049209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103302057317868393559366139 154953085976802590339049209)
        ·
          refine ⟨116214814482601942754286907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154953085976802590339049209 116214814482601942754286907)
          ·
            refine ⟨174322221723902914131430361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116214814482601942754286907 174322221723902914131430361)
            ·
              refine ⟨130741666292927185598572771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174322221723902914131430361 130741666292927185598572771)
              ·
                refine ⟨196112499439390778397859157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130741666292927185598572771 196112499439390778397859157)
                ·
                  refine ⟨287274169100670085543739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 196112499439390778397859157 287274169100670085543739)
                  ·
                    rfl

theorem cell21_1258795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_1258795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258795 prefixEnd_1258795 := by exact prefixLift 1258795
  have htrace : WordTrace (prefixWord ++ tailWord_1258795) baseStart_1258795 baseEnd_1258795 := by
    simpa [prefixWord, tailWord_1258795, baseEnd_1258795] using wordTrace_append hprefix tailTrace_1258795
  have hstable : (prefixWord ++ tailWord_1258795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258795).length < 2 ^ (prefixWord ++ tailWord_1258795).sum := by decide
  have hdescent : baseEnd_1258795 < baseStart_1258795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258801 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 4]
def baseStart_1258801 : Nat := 118140960795 + 1258801 * 2 ^ 59
def prefixEnd_1258801 : Nat := 4983230072969 + 3 ^ 40 * 1258801 * 2
def baseEnd_1258801 : Nat := 287275538382415408443727

theorem tailTrace_1258801 : CollatzResearch.WordTrace tailWord_1258801 prefixEnd_1258801 287275538382415408443727 := by
  unfold tailWord_1258801
  simp only [CollatzResearch.WordTrace]
  refine ⟨45912244312586437939992257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30608162875057625293328171 45912244312586437939992257)
  ·
    refine ⟨34434183234439828454994193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45912244312586437939992257 34434183234439828454994193)
    ·
      refine ⟨25825637425829871341245645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34434183234439828454994193 25825637425829871341245645)
      ·
        refine ⟨9684614034686201752967117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25825637425829871341245645 9684614034686201752967117)
        ·
          refine ⟨3631730263007325657362669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9684614034686201752967117 3631730263007325657362669)
          ·
            refine ⟨1361898848627747121511001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3631730263007325657362669 1361898848627747121511001)
            ·
              refine ⟨1021424136470810341133251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361898848627747121511001 1021424136470810341133251)
              ·
                refine ⟨1532136204706215511699877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021424136470810341133251 1532136204706215511699877)
                ·
                  refine ⟨287275538382415408443727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532136204706215511699877 287275538382415408443727)
                  ·
                    rfl

theorem cell21_1258801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_1258801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258801 prefixEnd_1258801 := by exact prefixLift 1258801
  have htrace : WordTrace (prefixWord ++ tailWord_1258801) baseStart_1258801 baseEnd_1258801 := by
    simpa [prefixWord, tailWord_1258801, baseEnd_1258801] using wordTrace_append hprefix tailTrace_1258801
  have hstable : (prefixWord ++ tailWord_1258801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258801).length < 2 ^ (prefixWord ++ tailWord_1258801).sum := by decide
  have hdescent : baseEnd_1258801 < baseStart_1258801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258826 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1258826 : Nat := 118140960795 + 1258826 * 2 ^ 59
def prefixEnd_1258826 : Nat := 4983230072969 + 3 ^ 40 * 1258826 * 2
def baseEnd_1258826 : Nat := 287281243723020920527009

theorem tailTrace_1258826 : CollatzResearch.WordTrace tailWord_1258826 prefixEnd_1258826 287281243723020920527009 := by
  unfold tailWord_1258826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478289034373966802413083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30608770758330578139768221 11478289034373966802413083)
  ·
    refine ⟨17217433551560950203619625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11478289034373966802413083 17217433551560950203619625)
    ·
      refine ⟨12913075163670712652714719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17217433551560950203619625 12913075163670712652714719)
      ·
        refine ⟨19369612745506068979072079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12913075163670712652714719 19369612745506068979072079)
        ·
          refine ⟨29054419118259103468608119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19369612745506068979072079 29054419118259103468608119)
          ·
            refine ⟨43581628677388655202912179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29054419118259103468608119 43581628677388655202912179)
            ·
              refine ⟨65372443016082982804368269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43581628677388655202912179 65372443016082982804368269)
              ·
                refine ⟨24514666131031118551638101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65372443016082982804368269 24514666131031118551638101)
                ·
                  refine ⟨287281243723020920527009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24514666131031118551638101 287281243723020920527009)
                  ·
                    rfl

theorem cell21_1258826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1258826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258826 prefixEnd_1258826 := by exact prefixLift 1258826
  have htrace : WordTrace (prefixWord ++ tailWord_1258826) baseStart_1258826 baseEnd_1258826 := by
    simpa [prefixWord, tailWord_1258826, baseEnd_1258826] using wordTrace_append hprefix tailTrace_1258826
  have hstable : (prefixWord ++ tailWord_1258826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258826).length < 2 ^ (prefixWord ++ tailWord_1258826).sum := by decide
  have hdescent : baseEnd_1258826 < baseStart_1258826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258894 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_1258894 : Nat := 118140960795 + 1258894 * 2 ^ 59
def prefixEnd_1258894 : Nat := 4983230072969 + 3 ^ 40 * 1258894 * 2
def baseEnd_1258894 : Nat := 287296762249467913393537

theorem tailTrace_1258894 : CollatzResearch.WordTrace tailWord_1258894 prefixEnd_1258894 287296762249467913393537 := by
  unfold tailWord_1258894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739454537656189352890967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30610424200833009882085157 5739454537656189352890967)
  ·
    refine ⟨8609181806484284029336451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5739454537656189352890967 8609181806484284029336451)
    ·
      refine ⟨12913772709726426044004677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609181806484284029336451 12913772709726426044004677)
      ·
        refine ⟨2421332383073704883250877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12913772709726426044004677 2421332383073704883250877)
        ·
          refine ⟨907999643652639331219079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2421332383073704883250877 907999643652639331219079)
          ·
            refine ⟨1361999465478958996828619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907999643652639331219079 1361999465478958996828619)
            ·
              refine ⟨2042999198218438495242929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361999465478958996828619 2042999198218438495242929)
              ·
                refine ⟨1532249398663828871432197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042999198218438495242929 1532249398663828871432197)
                ·
                  refine ⟨287296762249467913393537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532249398663828871432197 287296762249467913393537)
                  ·
                    rfl

theorem cell21_1258894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_1258894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258894 prefixEnd_1258894 := by exact prefixLift 1258894
  have htrace : WordTrace (prefixWord ++ tailWord_1258894) baseStart_1258894 baseEnd_1258894 := by
    simpa [prefixWord, tailWord_1258894, baseEnd_1258894] using wordTrace_append hprefix tailTrace_1258894
  have hstable : (prefixWord ++ tailWord_1258894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258894).length < 2 ^ (prefixWord ++ tailWord_1258894).sum := by decide
  have hdescent : baseEnd_1258894 < baseStart_1258894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258905 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1258905 : Nat := 118140960795 + 1258905 * 2 ^ 59
def prefixEnd_1258905 : Nat := 4983230072969 + 3 ^ 40 * 1258905 * 2
def baseEnd_1258905 : Nat := 287299272599334338710181

theorem tailTrace_1258905 : CollatzResearch.WordTrace tailWord_1258905 prefixEnd_1258905 287299272599334338710181 := by
  unfold tailWord_1258905
  simp only [CollatzResearch.WordTrace]
  refine ⟨45916037504209663701778169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30610691669473109134518779 45916037504209663701778169)
  ·
    refine ⟨34437028128157247776333627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45916037504209663701778169 34437028128157247776333627)
    ·
      refine ⟨51655542192235871664500441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34437028128157247776333627 51655542192235871664500441)
      ·
        refine ⟨38741656644176903748375331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51655542192235871664500441 38741656644176903748375331)
        ·
          refine ⟨58112484966265355622562997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38741656644176903748375331 58112484966265355622562997)
          ·
            refine ⟨5448045465587377089615281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58112484966265355622562997 5448045465587377089615281)
            ·
              refine ⟨4086034099190532817211461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5448045465587377089615281 4086034099190532817211461)
              ·
                refine ⟨766131393598224903227149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4086034099190532817211461 766131393598224903227149)
                ·
                  refine ⟨287299272599334338710181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766131393598224903227149 287299272599334338710181)
                  ·
                    rfl

theorem cell21_1258905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1258905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258905 prefixEnd_1258905 := by exact prefixLift 1258905
  have htrace : WordTrace (prefixWord ++ tailWord_1258905) baseStart_1258905 baseEnd_1258905 := by
    simpa [prefixWord, tailWord_1258905, baseEnd_1258905] using wordTrace_append hprefix tailTrace_1258905
  have hstable : (prefixWord ++ tailWord_1258905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258905).length < 2 ^ (prefixWord ++ tailWord_1258905).sum := by decide
  have hdescent : baseEnd_1258905 < baseStart_1258905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1258947 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_1258947 : Nat := 118140960795 + 1258947 * 2 ^ 59
def prefixEnd_1258947 : Nat := 4983230072969 + 3 ^ 40 * 1258947 * 2
def baseEnd_1258947 : Nat := 287308857571551599010095

theorem tailTrace_1258947 : CollatzResearch.WordTrace tailWord_1258947 prefixEnd_1258947 287308857571551599010095 := by
  unfold tailWord_1258947
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917569370057504874807095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30611712913371669916538063 45917569370057504874807095)
  ·
    refine ⟨68876354055086257312210643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45917569370057504874807095 68876354055086257312210643)
    ·
      refine ⟨103314531082629385968315965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68876354055086257312210643 103314531082629385968315965)
      ·
        refine ⟨38742949155986019738118487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103314531082629385968315965 38742949155986019738118487)
        ·
          refine ⟨58114423733979029607177731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38742949155986019738118487 58114423733979029607177731)
          ·
            refine ⟨87171635600968544410766597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58114423733979029607177731 87171635600968544410766597)
            ·
              refine ⟨16344681675181602077018737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87171635600968544410766597 16344681675181602077018737)
              ·
                refine ⟨12258511256386201557764053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16344681675181602077018737 12258511256386201557764053)
                ·
                  refine ⟨287308857571551599010095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12258511256386201557764053 287308857571551599010095)
                  ·
                    rfl

theorem cell21_1258947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_1258947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1258947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1258947 prefixEnd_1258947 := by exact prefixLift 1258947
  have htrace : WordTrace (prefixWord ++ tailWord_1258947) baseStart_1258947 baseEnd_1258947 := by
    simpa [prefixWord, tailWord_1258947, baseEnd_1258947] using wordTrace_append hprefix tailTrace_1258947
  have hstable : (prefixWord ++ tailWord_1258947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1258947).length < 2 ^ (prefixWord ++ tailWord_1258947).sum := by decide
  have hdescent : baseEnd_1258947 < baseStart_1258947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1258947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259009 : List Nat := [1, 2, 4, 1, 4, 9]
def baseStart_1259009 : Nat := 118140960795 + 1259009 * 2 ^ 59
def prefixEnd_1259009 : Nat := 4983230072969 + 3 ^ 40 * 1259009 * 2
def baseEnd_1259009 : Nat := 10641592845046417369505

theorem tailTrace_1259009 : CollatzResearch.WordTrace tailWord_1259009 prefixEnd_1259009 10641592845046417369505 := by
  unfold tailWord_1259009
  simp only [CollatzResearch.WordTrace]
  refine ⟨45919830695832889463564081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30613220463888592975709387 45919830695832889463564081)
  ·
    refine ⟨34439873021874667097673061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45919830695832889463564081 34439873021874667097673061)
    ·
      refine ⟨6457476191601500080813699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34439873021874667097673061 6457476191601500080813699)
      ·
        refine ⟨9686214287402250121220549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457476191601500080813699 9686214287402250121220549)
        ·
          refine ⟨1816165178887921897728853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9686214287402250121220549 1816165178887921897728853)
          ·
            refine ⟨10641592845046417369505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1816165178887921897728853 10641592845046417369505)
            ·
              rfl

theorem cell21_1259009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 9].length) (baseStart_1259009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259009 prefixEnd_1259009 := by exact prefixLift 1259009
  have htrace : WordTrace (prefixWord ++ tailWord_1259009) baseStart_1259009 baseEnd_1259009 := by
    simpa [prefixWord, tailWord_1259009, baseEnd_1259009] using wordTrace_append hprefix tailTrace_1259009
  have hstable : (prefixWord ++ tailWord_1259009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259009).length < 2 ^ (prefixWord ++ tailWord_1259009).sum := by decide
  have hdescent : baseEnd_1259009 < baseStart_1259009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259015 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 3]
def baseStart_1259015 : Nat := 118140960795 + 1259015 * 2 ^ 59
def prefixEnd_1259015 : Nat := 4983230072969 + 3 ^ 40 * 1259015 * 2
def baseEnd_1259015 : Nat := 287324376097998591876623

theorem tailTrace_1259015 : CollatzResearch.WordTrace tailWord_1259015 prefixEnd_1259015 287324376097998591876623 := by
  unfold tailWord_1259015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45920049533811152488282499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30613366355874101658854999 45920049533811152488282499)
  ·
    refine ⟨68880074300716728732423749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45920049533811152488282499 68880074300716728732423749)
    ·
      refine ⟨12915013931384386637329453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68880074300716728732423749 12915013931384386637329453)
      ·
        refine ⟨4843130224269144988998545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12915013931384386637329453 4843130224269144988998545)
        ·
          refine ⟨3632347668201858741748909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843130224269144988998545 3632347668201858741748909)
          ·
            refine ⟨1362130375575697028155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3632347668201858741748909 1362130375575697028155841)
            ·
              refine ⟨1021597781681772771116881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362130375575697028155841 1021597781681772771116881)
              ·
                refine ⟨766198336261329578337661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021597781681772771116881 766198336261329578337661)
                ·
                  refine ⟨287324376097998591876623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766198336261329578337661 287324376097998591876623)
                  ·
                    rfl

theorem cell21_1259015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].length) (baseStart_1259015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259015 prefixEnd_1259015 := by exact prefixLift 1259015
  have htrace : WordTrace (prefixWord ++ tailWord_1259015) baseStart_1259015 baseEnd_1259015 := by
    simpa [prefixWord, tailWord_1259015, baseEnd_1259015] using wordTrace_append hprefix tailTrace_1259015
  have hstable : (prefixWord ++ tailWord_1259015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259015).length < 2 ^ (prefixWord ++ tailWord_1259015).sum := by decide
  have hdescent : baseEnd_1259015 < baseStart_1259015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259040 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1259040 : Nat := 118140960795 + 1259040 * 2 ^ 59
def prefixEnd_1259040 : Nat := 4983230072969 + 3 ^ 40 * 1259040 * 2
def baseEnd_1259040 : Nat := 287330081438604103959905

theorem tailTrace_1259040 : CollatzResearch.WordTrace tailWord_1259040 prefixEnd_1259040 287330081438604103959905 := by
  unfold tailWord_1259040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960480679360290878971287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30613974239147054505295049 22960480679360290878971287)
  ·
    refine ⟨34440721019040436318456931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22960480679360290878971287 34440721019040436318456931)
    ·
      refine ⟨51661081528560654477685397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34440721019040436318456931 51661081528560654477685397)
      ·
        refine ⟨2421613196651280678641503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51661081528560654477685397 2421613196651280678641503)
        ·
          refine ⟨3632419794976921017962255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2421613196651280678641503 3632419794976921017962255)
          ·
            refine ⟨5448629692465381526943383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632419794976921017962255 5448629692465381526943383)
            ·
              refine ⟨8172944538698072290415075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448629692465381526943383 8172944538698072290415075)
              ·
                refine ⟨12259416808047108435622613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172944538698072290415075 12259416808047108435622613)
                ·
                  refine ⟨287330081438604103959905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12259416808047108435622613 287330081438604103959905)
                  ·
                    rfl

theorem cell21_1259040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1259040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259040 prefixEnd_1259040 := by exact prefixLift 1259040
  have htrace : WordTrace (prefixWord ++ tailWord_1259040) baseStart_1259040 baseEnd_1259040 := by
    simpa [prefixWord, tailWord_1259040, baseEnd_1259040] using wordTrace_append hprefix tailTrace_1259040
  have hstable : (prefixWord ++ tailWord_1259040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259040).length < 2 ^ (prefixWord ++ tailWord_1259040).sum := by decide
  have hdescent : baseEnd_1259040 < baseStart_1259040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259071 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_1259071 : Nat := 118140960795 + 1259071 * 2 ^ 59
def prefixEnd_1259071 : Nat := 4983230072969 + 3 ^ 40 * 1259071 * 2
def baseEnd_1259071 : Nat := 287337156060954938943175

theorem tailTrace_1259071 : CollatzResearch.WordTrace tailWord_1259071 prefixEnd_1259071 287337156060954938943175 := by
  unfold tailWord_1259071
  simp only [CollatzResearch.WordTrace]
  refine ⟨45922092021608274052321067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30614728014405516034880711 45922092021608274052321067)
  ·
    refine ⟨68883138032412411078481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45922092021608274052321067 68883138032412411078481601)
    ·
      refine ⟨51662353524309308308861201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68883138032412411078481601 51662353524309308308861201)
      ·
        refine ⟨38746765143231981231645901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51662353524309308308861201 38746765143231981231645901)
        ·
          refine ⟨14530036928711992961867213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38746765143231981231645901 14530036928711992961867213)
          ·
            refine ⟨5448763848266997360700205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14530036928711992961867213 5448763848266997360700205)
            ·
              refine ⟨2043286443100124010262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448763848266997360700205 2043286443100124010262577)
              ·
                refine ⟨1532464832325093007696933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043286443100124010262577 1532464832325093007696933)
                ·
                  refine ⟨287337156060954938943175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532464832325093007696933 287337156060954938943175)
                  ·
                    rfl

theorem cell21_1259071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_1259071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259071 prefixEnd_1259071 := by exact prefixLift 1259071
  have htrace : WordTrace (prefixWord ++ tailWord_1259071) baseStart_1259071 baseEnd_1259071 := by
    simpa [prefixWord, tailWord_1259071, baseEnd_1259071] using wordTrace_append hprefix tailTrace_1259071
  have hstable : (prefixWord ++ tailWord_1259071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259071).length < 2 ^ (prefixWord ++ tailWord_1259071).sum := by decide
  have hdescent : baseEnd_1259071 < baseStart_1259071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259094 : List Nat := [5, 2, 2, 2, 2, 1, 2, 5]
def baseStart_1259094 : Nat := 118140960795 + 1259094 * 2 ^ 59
def prefixEnd_1259094 : Nat := 4983230072969 + 3 ^ 40 * 1259094 * 2
def baseEnd_1259094 : Nat := 95780801658104003353265

theorem tailTrace_1259094 : CollatzResearch.WordTrace tailWord_1259094 prefixEnd_1259094 95780801658104003353265 := by
  unfold tailWord_1259094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870183181282809311275521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30615287267016632653605557 2870183181282809311275521)
  ·
    refine ⟨2152637385962106983456641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2870183181282809311275521 2152637385962106983456641)
    ·
      refine ⟨1614478039471580237592481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152637385962106983456641 1614478039471580237592481)
      ·
        refine ⟨1210858529603685178194361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614478039471580237592481 1210858529603685178194361)
        ·
          refine ⟨908143897202763883645771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210858529603685178194361 908143897202763883645771)
          ·
            refine ⟨1362215845804145825468657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908143897202763883645771 1362215845804145825468657)
            ·
              refine ⟨1021661884353109369101493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362215845804145825468657 1021661884353109369101493)
              ·
                refine ⟨95780801658104003353265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021661884353109369101493 95780801658104003353265)
                ·
                  rfl

theorem cell21_1259094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_1259094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259094 prefixEnd_1259094 := by exact prefixLift 1259094
  have htrace : WordTrace (prefixWord ++ tailWord_1259094) baseStart_1259094 baseEnd_1259094 := by
    simpa [prefixWord, tailWord_1259094, baseEnd_1259094] using wordTrace_append hprefix tailTrace_1259094
  have hstable : (prefixWord ++ tailWord_1259094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259094).length < 2 ^ (prefixWord ++ tailWord_1259094).sum := by decide
  have hdescent : baseEnd_1259094 < baseStart_1259094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259133 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1259133 : Nat := 118140960795 + 1259133 * 2 ^ 59
def prefixEnd_1259133 : Nat := 4983230072969 + 3 ^ 40 * 1259133 * 2
def baseEnd_1259133 : Nat := 287351305305656608909715

theorem tailTrace_1259133 : CollatzResearch.WordTrace tailWord_1259133 prefixEnd_1259133 287351305305656608909715 := by
  unfold tailWord_1259133
  simp only [CollatzResearch.WordTrace]
  refine ⟨45924353347383658641078053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30616235564922439094052035 45924353347383658641078053)
  ·
    refine ⟨8610816252634435995202135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45924353347383658641078053 8610816252634435995202135)
    ·
      refine ⟨12916224378951653992803203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8610816252634435995202135 12916224378951653992803203)
      ·
        refine ⟨19374336568427480989204805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916224378951653992803203 19374336568427480989204805)
        ·
          refine ⟨3632688106580152685475901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19374336568427480989204805 3632688106580152685475901)
          ·
            refine ⟨1362258039967557257053463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3632688106580152685475901 1362258039967557257053463)
            ·
              refine ⟨2043387059951335885580195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362258039967557257053463 2043387059951335885580195)
              ·
                refine ⟨3065080589927003828370293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043387059951335885580195 3065080589927003828370293)
                ·
                  refine ⟨287351305305656608909715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065080589927003828370293 287351305305656608909715)
                  ·
                    rfl

theorem cell21_1259133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1259133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259133 prefixEnd_1259133 := by exact prefixLift 1259133
  have htrace : WordTrace (prefixWord ++ tailWord_1259133) baseStart_1259133 baseEnd_1259133 := by
    simpa [prefixWord, tailWord_1259133, baseEnd_1259133] using wordTrace_append hprefix tailTrace_1259133
  have hstable : (prefixWord ++ tailWord_1259133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259133).length < 2 ^ (prefixWord ++ tailWord_1259133).sum := by decide
  have hdescent : baseEnd_1259133 < baseStart_1259133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259240 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_1259240 : Nat := 118140960795 + 1259240 * 2 ^ 59
def prefixEnd_1259240 : Nat := 4983230072969 + 3 ^ 40 * 1259240 * 2
def baseEnd_1259240 : Nat := 287375724163448200626163

theorem tailTrace_1259240 : CollatzResearch.WordTrace tailWord_1259240 prefixEnd_1259240 287375724163448200626163 := by
  unfold tailWord_1259240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964127978998007957611587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30618837305330677276815449 22964127978998007957611587)
  ·
    refine ⟨34446191968497011936417381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22964127978998007957611587 34446191968497011936417381)
    ·
      refine ⟨6458660994093189738078259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34446191968497011936417381 6458660994093189738078259)
      ·
        refine ⟨9687991491139784607117389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458660994093189738078259 9687991491139784607117389)
        ·
          refine ⟨3632996809177419227669021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9687991491139784607117389 3632996809177419227669021)
          ·
            refine ⟨1362373803441532210375883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3632996809177419227669021 1362373803441532210375883)
            ·
              refine ⟨2043560705162298315563825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362373803441532210375883 2043560705162298315563825)
              ·
                refine ⟨1532670528871723736672869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043560705162298315563825 1532670528871723736672869)
                ·
                  refine ⟨287375724163448200626163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532670528871723736672869 287375724163448200626163)
                  ·
                    rfl

theorem cell21_1259240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_1259240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259240 prefixEnd_1259240 := by exact prefixLift 1259240
  have htrace : WordTrace (prefixWord ++ tailWord_1259240) baseStart_1259240 baseEnd_1259240 := by
    simpa [prefixWord, tailWord_1259240, baseEnd_1259240] using wordTrace_append hprefix tailTrace_1259240
  have hstable : (prefixWord ++ tailWord_1259240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259240).length < 2 ^ (prefixWord ++ tailWord_1259240).sum := by decide
  have hdescent : baseEnd_1259240 < baseStart_1259240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259251 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_1259251 : Nat := 118140960795 + 1259251 * 2 ^ 59
def prefixEnd_1259251 : Nat := 4983230072969 + 3 ^ 40 * 1259251 * 2
def baseEnd_1259251 : Nat := 287378234513314625942807

theorem tailTrace_1259251 : CollatzResearch.WordTrace tailWord_1259251 prefixEnd_1259251 287378234513314625942807 := by
  unfold tailWord_1259251
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928657160956164793873607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619104773970776529249071 45928657160956164793873607)
  ·
    refine ⟨68892985741434247190810411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45928657160956164793873607 68892985741434247190810411)
    ·
      refine ⟨103339478612151370786215617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68892985741434247190810411 103339478612151370786215617)
      ·
        refine ⟨77504608959113528089661713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103339478612151370786215617 77504608959113528089661713)
        ·
          refine ⟨58128456719335146067246285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77504608959113528089661713 58128456719335146067246285)
          ·
            refine ⟨21798171269750679775217357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58128456719335146067246285 21798171269750679775217357)
            ·
              refine ⟨8174314226156504915706509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21798171269750679775217357 8174314226156504915706509)
              ·
                refine ⟨3065367834808689343389941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8174314226156504915706509 3065367834808689343389941)
                ·
                  refine ⟨287378234513314625942807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065367834808689343389941 287378234513314625942807)
                  ·
                    rfl

theorem cell21_1259251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_1259251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259251 prefixEnd_1259251 := by exact prefixLift 1259251
  have htrace : WordTrace (prefixWord ++ tailWord_1259251) baseStart_1259251 baseEnd_1259251 := by
    simpa [prefixWord, tailWord_1259251, baseEnd_1259251] using wordTrace_append hprefix tailTrace_1259251
  have hstable : (prefixWord ++ tailWord_1259251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259251).length < 2 ^ (prefixWord ++ tailWord_1259251).sum := by decide
  have hdescent : baseEnd_1259251 < baseStart_1259251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259268 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1259268 : Nat := 118140960795 + 1259268 * 2 ^ 59
def prefixEnd_1259268 : Nat := 4983230072969 + 3 ^ 40 * 1259268 * 2
def baseEnd_1259268 : Nat := 287382114144926374159439

theorem tailTrace_1259268 : CollatzResearch.WordTrace tailWord_1259268 prefixEnd_1259268 287382114144926374159439 := by
  unfold tailWord_1259268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964638600947288348621229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30619518134596384464828305 22964638600947288348621229)
  ·
    refine ⟨8611739475355233130732961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22964638600947288348621229 8611739475355233130732961)
    ·
      refine ⟨6458804606516424848049721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8611739475355233130732961 6458804606516424848049721)
      ·
        refine ⟨4844103454887318636037291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6458804606516424848049721 4844103454887318636037291)
        ·
          refine ⟨7266155182330977954055937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844103454887318636037291 7266155182330977954055937)
          ·
            refine ⟨5449616386748233465541953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7266155182330977954055937 5449616386748233465541953)
            ·
              refine ⟨4087212290061175099156465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449616386748233465541953 4087212290061175099156465)
              ·
                refine ⟨3065409217545881324367349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087212290061175099156465 3065409217545881324367349)
                ·
                  refine ⟨287382114144926374159439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065409217545881324367349 287382114144926374159439)
                  ·
                    rfl

theorem cell21_1259268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1259268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259268 prefixEnd_1259268 := by exact prefixLift 1259268
  have htrace : WordTrace (prefixWord ++ tailWord_1259268) baseStart_1259268 baseEnd_1259268 := by
    simpa [prefixWord, tailWord_1259268, baseEnd_1259268] using wordTrace_append hprefix tailTrace_1259268
  have hstable : (prefixWord ++ tailWord_1259268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259268).length < 2 ^ (prefixWord ++ tailWord_1259268).sum := by decide
  have hdescent : baseEnd_1259268 < baseStart_1259268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259271 : List Nat := [1, 1, 4, 4, 2, 2, 2, 5]
def baseStart_1259271 : Nat := 118140960795 + 1259271 * 2 ^ 59
def prefixEnd_1259271 : Nat := 4983230072969 + 3 ^ 40 * 1259271 * 2
def baseEnd_1259271 : Nat := 95794266261933011869811

theorem tailTrace_1259271 : CollatzResearch.WordTrace tailWord_1259271 prefixEnd_1259271 95794266261933011869811 := by
  unfold tailWord_1259271
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929386620883708209601667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619591080589138806401111 45929386620883708209601667)
  ·
    refine ⟨68894079931325562314402501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45929386620883708209601667 68894079931325562314402501)
    ·
      refine ⟨12917639987123542933950469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68894079931325562314402501 12917639987123542933950469)
      ·
        refine ⟨2422057497585664300115713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12917639987123542933950469 2422057497585664300115713)
        ·
          refine ⟨1816543123189248225086785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422057497585664300115713 1816543123189248225086785)
          ·
            refine ⟨1362407342391936168815089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816543123189248225086785 1362407342391936168815089)
            ·
              refine ⟨1021805506793952126611317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362407342391936168815089 1021805506793952126611317)
              ·
                refine ⟨95794266261933011869811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021805506793952126611317 95794266261933011869811)
                ·
                  rfl

theorem cell21_1259271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].length) (baseStart_1259271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259271 prefixEnd_1259271 := by exact prefixLift 1259271
  have htrace : WordTrace (prefixWord ++ tailWord_1259271) baseStart_1259271 baseEnd_1259271 := by
    simpa [prefixWord, tailWord_1259271, baseEnd_1259271] using wordTrace_append hprefix tailTrace_1259271
  have hstable : (prefixWord ++ tailWord_1259271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259271).length < 2 ^ (prefixWord ++ tailWord_1259271).sum := by decide
  have hdescent : baseEnd_1259271 < baseStart_1259271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259285 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1259285 : Nat := 118140960795 + 1259285 * 2 ^ 59
def prefixEnd_1259285 : Nat := 4983230072969 + 3 ^ 40 * 1259285 * 2
def baseEnd_1259285 : Nat := 287385993776538122376071

theorem tailTrace_1259285 : CollatzResearch.WordTrace tailWord_1259285 prefixEnd_1259285 287385993776538122376071 := by
  unfold tailWord_1259285
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929897242832988600611309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30619931495221992400407539 45929897242832988600611309)
  ·
    refine ⟨17223711466062370725229241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45929897242832988600611309 17223711466062370725229241)
    ·
      refine ⟨12917783599546778043921931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17223711466062370725229241 12917783599546778043921931)
      ·
        refine ⟨19376675399320167065882897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12917783599546778043921931 19376675399320167065882897)
        ·
          refine ⟨14532506549490125299412173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19376675399320167065882897 14532506549490125299412173)
          ·
            refine ⟨5449689956058796987279565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14532506549490125299412173 5449689956058796987279565)
            ·
              refine ⟨2043633733522048870229837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5449689956058796987279565 2043633733522048870229837)
              ·
                refine ⟨766362650070768326336189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2043633733522048870229837 766362650070768326336189)
                ·
                  refine ⟨287385993776538122376071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766362650070768326336189 287385993776538122376071)
                  ·
                    rfl

theorem cell21_1259285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1259285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259285 prefixEnd_1259285 := by exact prefixLift 1259285
  have htrace : WordTrace (prefixWord ++ tailWord_1259285) baseStart_1259285 baseEnd_1259285 := by
    simpa [prefixWord, tailWord_1259285, baseEnd_1259285] using wordTrace_append hprefix tailTrace_1259285
  have hstable : (prefixWord ++ tailWord_1259285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259285).length < 2 ^ (prefixWord ++ tailWord_1259285).sum := by decide
  have hdescent : baseEnd_1259285 < baseStart_1259285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259313 : List Nat := [1, 2, 2, 3, 2, 3, 2, 6]
def baseStart_1259313 : Nat := 118140960795 + 1259313 * 2 ^ 59
def prefixEnd_1259313 : Nat := 4983230072969 + 3 ^ 40 * 1259313 * 2
def baseEnd_1259313 : Nat := 95797461252672098636449

theorem tailTrace_1259313 : CollatzResearch.WordTrace tailWord_1259313 prefixEnd_1259313 95797461252672098636449 := by
  unfold tailWord_1259313
  simp only [CollatzResearch.WordTrace]
  refine ⟨45930918486731549382630593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30620612324487699588420395 45930918486731549382630593)
  ·
    refine ⟨34448188865048662036972945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45930918486731549382630593 34448188865048662036972945)
    ·
      refine ⟨25836141648786496527729709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34448188865048662036972945 25836141648786496527729709)
      ·
        refine ⟨9688553118294936197898641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25836141648786496527729709 9688553118294936197898641)
        ·
          refine ⟨7266414838721202148423981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9688553118294936197898641 7266414838721202148423981)
          ·
            refine ⟨2724905564520450805658993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7266414838721202148423981 2724905564520450805658993)
            ·
              refine ⟨2043679173390338104244245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724905564520450805658993 2043679173390338104244245)
              ·
                refine ⟨95797461252672098636449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2043679173390338104244245 95797461252672098636449)
                ·
                  rfl

theorem cell21_1259313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_1259313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259313 prefixEnd_1259313 := by exact prefixLift 1259313
  have htrace : WordTrace (prefixWord ++ tailWord_1259313) baseStart_1259313 baseEnd_1259313 := by
    simpa [prefixWord, tailWord_1259313, baseEnd_1259313] using wordTrace_append hprefix tailTrace_1259313
  have hstable : (prefixWord ++ tailWord_1259313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259313).length < 2 ^ (prefixWord ++ tailWord_1259313).sum := by decide
  have hdescent : baseEnd_1259313 < baseStart_1259313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259316 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1259316 : Nat := 118140960795 + 1259316 * 2 ^ 59
def prefixEnd_1259316 : Nat := 4983230072969 + 3 ^ 40 * 1259316 * 2
def baseEnd_1259316 : Nat := 287393068398888957359341

theorem tailTrace_1259316 : CollatzResearch.WordTrace tailWord_1259316 prefixEnd_1259316 287393068398888957359341 := by
  unfold tailWord_1259316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22965513952860340447494901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30620685270480453929993201 22965513952860340447494901)
  ·
    refine ⟨2153016933080656916952647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22965513952860340447494901 2153016933080656916952647)
    ·
      refine ⟨3229525399620985375428971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2153016933080656916952647 3229525399620985375428971)
      ·
        refine ⟨4844288099431478063143457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229525399620985375428971 4844288099431478063143457)
        ·
          refine ⟨3633216074573608547357593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844288099431478063143457 3633216074573608547357593)
          ·
            refine ⟨2724912055930206410518195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3633216074573608547357593 2724912055930206410518195)
            ·
              refine ⟨4087368083895309615777293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724912055930206410518195 4087368083895309615777293)
              ·
                refine ⟨1532763031460741105916485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4087368083895309615777293 1532763031460741105916485)
                ·
                  refine ⟨287393068398888957359341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532763031460741105916485 287393068398888957359341)
                  ·
                    rfl

theorem cell21_1259316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1259316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259316 prefixEnd_1259316 := by exact prefixLift 1259316
  have htrace : WordTrace (prefixWord ++ tailWord_1259316) baseStart_1259316 baseEnd_1259316 := by
    simpa [prefixWord, tailWord_1259316, baseEnd_1259316] using wordTrace_append hprefix tailTrace_1259316
  have hstable : (prefixWord ++ tailWord_1259316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259316).length < 2 ^ (prefixWord ++ tailWord_1259316).sum := by decide
  have hdescent : baseEnd_1259316 < baseStart_1259316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259344 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_1259344 : Nat := 118140960795 + 1259344 * 2 ^ 59
def prefixEnd_1259344 : Nat := 4983230072969 + 3 ^ 40 * 1259344 * 2
def baseEnd_1259344 : Nat := 287399458380367130892617

theorem tailTrace_1259344 : CollatzResearch.WordTrace tailWord_1259344 prefixEnd_1259344 287399458380367130892617 := by
  unfold tailWord_1259344
  simp only [CollatzResearch.WordTrace]
  refine ⟨22966024574809620838504543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30621366099746161118006057 22966024574809620838504543)
  ·
    refine ⟨34449036862214431257756815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22966024574809620838504543 34449036862214431257756815)
    ·
      refine ⟨51673555293321646886635223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34449036862214431257756815 51673555293321646886635223)
      ·
        refine ⟨77510332939982470329952835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51673555293321646886635223 77510332939982470329952835)
        ·
          refine ⟨116265499409973705494929253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77510332939982470329952835 116265499409973705494929253)
          ·
            refine ⟨21799781139370069780299235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116265499409973705494929253 21799781139370069780299235)
            ·
              refine ⟨32699671709055104670448853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21799781139370069780299235 32699671709055104670448853)
              ·
                refine ⟨766398555680979015713645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32699671709055104670448853 766398555680979015713645)
                ·
                  refine ⟨287399458380367130892617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766398555680979015713645 287399458380367130892617)
                  ·
                    rfl

theorem cell21_1259344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_1259344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259344 prefixEnd_1259344 := by exact prefixLift 1259344
  have htrace : WordTrace (prefixWord ++ tailWord_1259344) baseStart_1259344 baseEnd_1259344 := by
    simpa [prefixWord, tailWord_1259344, baseEnd_1259344] using wordTrace_append hprefix tailTrace_1259344
  have hstable : (prefixWord ++ tailWord_1259344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259344).length < 2 ^ (prefixWord ++ tailWord_1259344).sum := by decide
  have hdescent : baseEnd_1259344 < baseStart_1259344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259406 : List Nat := [4, 1, 1, 5, 1, 1, 8]
def baseStart_1259406 : Nat := 118140960795 + 1259406 * 2 ^ 59
def prefixEnd_1259406 : Nat := 4983230072969 + 3 ^ 40 * 1259406 * 2
def baseEnd_1259406 : Nat := 31934845291674311206573

theorem tailTrace_1259406 : CollatzResearch.WordTrace tailWord_1259406 prefixEnd_1259406 31934845291674311206573 := by
  unfold tailWord_1259406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741788809424328283220759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30622873650263084177177381 5741788809424328283220759)
  ·
    refine ⟨8612683214136492424831139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741788809424328283220759 8612683214136492424831139)
    ·
      refine ⟨12919024821204738637246709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8612683214136492424831139 12919024821204738637246709)
      ·
        refine ⟨1211158576987944247241879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12919024821204738637246709 1211158576987944247241879)
        ·
          refine ⟨1816737865481916370862819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211158576987944247241879 1816737865481916370862819)
          ·
            refine ⟨2725106798222874556294229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816737865481916370862819 2725106798222874556294229)
            ·
              refine ⟨31934845291674311206573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2725106798222874556294229 31934845291674311206573)
              ·
                rfl

theorem cell21_1259406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 8].length) (baseStart_1259406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259406 prefixEnd_1259406 := by exact prefixLift 1259406
  have htrace : WordTrace (prefixWord ++ tailWord_1259406) baseStart_1259406 baseEnd_1259406 := by
    simpa [prefixWord, tailWord_1259406, baseEnd_1259406] using wordTrace_append hprefix tailTrace_1259406
  have hstable : (prefixWord ++ tailWord_1259406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259406).length < 2 ^ (prefixWord ++ tailWord_1259406).sum := by decide
  have hdescent : baseEnd_1259406 < baseStart_1259406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259420 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_1259420 : Nat := 118140960795 + 1259420 * 2 ^ 59
def prefixEnd_1259420 : Nat := 4983230072969 + 3 ^ 40 * 1259420 * 2
def baseEnd_1259420 : Nat := 287416802615807887625795

theorem tailTrace_1259420 : CollatzResearch.WordTrace tailWord_1259420 prefixEnd_1259420 287416802615807887625795 := by
  unfold tailWord_1259420
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967410548671953328387857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30623214064895937771183809 22967410548671953328387857)
  ·
    refine ⟨17225557911503964996290893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22967410548671953328387857 17225557911503964996290893)
    ·
      refine ⟨6459584216813986873609085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17225557911503964996290893 6459584216813986873609085)
      ·
        refine ⟨2422344081305245077603407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6459584216813986873609085 2422344081305245077603407)
        ·
          refine ⟨3633516121957867616405111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422344081305245077603407 3633516121957867616405111)
          ·
            refine ⟨5450274182936801424607667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633516121957867616405111 5450274182936801424607667)
            ·
              refine ⟨8175411274405202136911501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450274182936801424607667 8175411274405202136911501)
              ·
                refine ⟨3065779227901950801341813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8175411274405202136911501 3065779227901950801341813)
                ·
                  refine ⟨287416802615807887625795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065779227901950801341813 287416802615807887625795)
                  ·
                    rfl

theorem cell21_1259420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_1259420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259420 prefixEnd_1259420 := by exact prefixLift 1259420
  have htrace : WordTrace (prefixWord ++ tailWord_1259420) baseStart_1259420 baseEnd_1259420 := by
    simpa [prefixWord, tailWord_1259420, baseEnd_1259420] using wordTrace_append hprefix tailTrace_1259420
  have hstable : (prefixWord ++ tailWord_1259420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259420).length < 2 ^ (prefixWord ++ tailWord_1259420).sum := by decide
  have hdescent : baseEnd_1259420 < baseStart_1259420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259448 : List Nat := [2, 1, 2, 1, 2, 3, 3, 7]
def baseStart_1259448 : Nat := 118140960795 + 1259448 * 2 ^ 59
def prefixEnd_1259448 : Nat := 4983230072969 + 3 ^ 40 * 1259448 * 2
def baseEnd_1259448 : Nat := 95807730865762020386357

theorem tailTrace_1259448 : CollatzResearch.WordTrace tailWord_1259448 prefixEnd_1259448 95807730865762020386357 := by
  unfold tailWord_1259448
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967921170621233719397499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30623894894161644959196665 22967921170621233719397499)
  ·
    refine ⟨34451881755931850579096249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22967921170621233719397499 34451881755931850579096249)
    ·
      refine ⟨25838911316948887934322187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34451881755931850579096249 25838911316948887934322187)
      ·
        refine ⟨38758366975423331901483281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25838911316948887934322187 38758366975423331901483281)
        ·
          refine ⟨29068775231567498926112461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38758366975423331901483281 29068775231567498926112461)
          ·
            refine ⟨10900790711837812097292173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29068775231567498926112461 10900790711837812097292173)
            ·
              refine ⟨4087796516939179536484565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10900790711837812097292173 4087796516939179536484565)
              ·
                refine ⟨95807730865762020386357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4087796516939179536484565 95807730865762020386357)
                ·
                  rfl

theorem cell21_1259448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_1259448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259448 prefixEnd_1259448 := by exact prefixLift 1259448
  have htrace : WordTrace (prefixWord ++ tailWord_1259448) baseStart_1259448 baseEnd_1259448 := by
    simpa [prefixWord, tailWord_1259448, baseEnd_1259448] using wordTrace_append hprefix tailTrace_1259448
  have hstable : (prefixWord ++ tailWord_1259448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259448).length < 2 ^ (prefixWord ++ tailWord_1259448).sum := by decide
  have hdescent : baseEnd_1259448 < baseStart_1259448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259454 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1259454 : Nat := 118140960795 + 1259454 * 2 ^ 59
def prefixEnd_1259454 : Nat := 4983230072969 + 3 ^ 40 * 1259454 * 2
def baseEnd_1259454 : Nat := 287424561879031384059059

theorem tailTrace_1259454 : CollatzResearch.WordTrace tailWord_1259454 prefixEnd_1259454 287424561879031384059059 := by
  unfold tailWord_1259454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742007647402591307939177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30624040786147153642342277 5742007647402591307939177)
  ·
    refine ⟨4306505735551943480954383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5742007647402591307939177 4306505735551943480954383)
    ·
      refine ⟨6459758603327915221431575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306505735551943480954383 6459758603327915221431575)
      ·
        refine ⟨9689637904991872832147363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459758603327915221431575 9689637904991872832147363)
        ·
          refine ⟨14534456857487809248221045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689637904991872832147363 14534456857487809248221045)
          ·
            refine ⟨1362605330389482117020723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14534456857487809248221045 1362605330389482117020723)
            ·
              refine ⟨2043907995584223175531085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362605330389482117020723 2043907995584223175531085)
              ·
                refine ⟨766465498344083690824157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2043907995584223175531085 766465498344083690824157)
                ·
                  refine ⟨287424561879031384059059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766465498344083690824157 287424561879031384059059)
                  ·
                    rfl

theorem cell21_1259454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1259454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259454 prefixEnd_1259454 := by exact prefixLift 1259454
  have htrace : WordTrace (prefixWord ++ tailWord_1259454) baseStart_1259454 baseEnd_1259454 := by
    simpa [prefixWord, tailWord_1259454, baseEnd_1259454] using wordTrace_append hprefix tailTrace_1259454
  have hstable : (prefixWord ++ tailWord_1259454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259454).length < 2 ^ (prefixWord ++ tailWord_1259454).sum := by decide
  have hdescent : baseEnd_1259454 < baseStart_1259454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259485 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1259485 : Nat := 118140960795 + 1259485 * 2 ^ 59
def prefixEnd_1259485 : Nat := 4983230072969 + 3 ^ 40 * 1259485 * 2
def baseEnd_1259485 : Nat := 287431636501382219042329

theorem tailTrace_1259485 : CollatzResearch.WordTrace tailWord_1259485 prefixEnd_1259485 287431636501382219042329 := by
  unfold tailWord_1259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨45937191842108422757891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30624794561405615171927939 45937191842108422757891909)
  ·
    refine ⟨8613223470395329267104733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45937191842108422757891909 8613223470395329267104733)
    ·
      refine ⟨3229958801398248475164275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8613223470395329267104733 3229958801398248475164275)
      ·
        refine ⟨4844938202097372712746413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229958801398248475164275 4844938202097372712746413)
        ·
          refine ⟨1816851825786514767279905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4844938202097372712746413 1816851825786514767279905)
          ·
            refine ⟨1362638869339886075459929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816851825786514767279905 1362638869339886075459929)
            ·
              refine ⟨1021979152004914556594947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362638869339886075459929 1021979152004914556594947)
              ·
                refine ⟨1532968728007371834892421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021979152004914556594947 1532968728007371834892421)
                ·
                  refine ⟨287431636501382219042329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532968728007371834892421 287431636501382219042329)
                  ·
                    rfl

theorem cell21_1259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1259485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259485 prefixEnd_1259485 := by exact prefixLift 1259485
  have htrace : WordTrace (prefixWord ++ tailWord_1259485) baseStart_1259485 baseEnd_1259485 := by
    simpa [prefixWord, tailWord_1259485, baseEnd_1259485] using wordTrace_append hprefix tailTrace_1259485
  have hstable : (prefixWord ++ tailWord_1259485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259485).length < 2 ^ (prefixWord ++ tailWord_1259485).sum := by decide
  have hdescent : baseEnd_1259485 < baseStart_1259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259527 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_1259527 : Nat := 118140960795 + 1259527 * 2 ^ 59
def prefixEnd_1259527 : Nat := 4983230072969 + 3 ^ 40 * 1259527 * 2
def baseEnd_1259527 : Nat := 287441221473599479342243

theorem tailTrace_1259527 : CollatzResearch.WordTrace tailWord_1259527 prefixEnd_1259527 287441221473599479342243 := by
  unfold tailWord_1259527
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938723707956263930920835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30625815805304175953947223 45938723707956263930920835)
  ·
    refine ⟨68908085561934395896381253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45938723707956263930920835 68908085561934395896381253)
    ·
      refine ⟨12920266042862699230571485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68908085561934395896381253 12920266042862699230571485)
      ·
        refine ⟨4845099766073512211464307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12920266042862699230571485 4845099766073512211464307)
        ·
          refine ⟨7267649649110268317196461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845099766073512211464307 7267649649110268317196461)
          ·
            refine ⟨2725368618416350618948673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7267649649110268317196461 2725368618416350618948673)
            ·
              refine ⟨2044026463812262964211505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725368618416350618948673 2044026463812262964211505)
              ·
                refine ⟨1533019847859197223158629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044026463812262964211505 1533019847859197223158629)
                ·
                  refine ⟨287441221473599479342243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533019847859197223158629 287441221473599479342243)
                  ·
                    rfl

theorem cell21_1259527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_1259527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259527 prefixEnd_1259527 := by exact prefixLift 1259527
  have htrace : WordTrace (prefixWord ++ tailWord_1259527) baseStart_1259527 baseEnd_1259527 := by
    simpa [prefixWord, tailWord_1259527, baseEnd_1259527] using wordTrace_append hprefix tailTrace_1259527
  have hstable : (prefixWord ++ tailWord_1259527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259527).length < 2 ^ (prefixWord ++ tailWord_1259527).sum := by decide
  have hdescent : baseEnd_1259527 < baseStart_1259527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259533 : List Nat := [1, 7, 1, 2, 2, 1, 1, 6]
def baseStart_1259533 : Nat := 118140960795 + 1259533 * 2 ^ 59
def prefixEnd_1259533 : Nat := 4983230072969 + 3 ^ 40 * 1259533 * 2
def baseEnd_1259533 : Nat := 95814196918448267414077

theorem tailTrace_1259533 : CollatzResearch.WordTrace tailWord_1259533 prefixEnd_1259533 95814196918448267414077 := by
  unfold tailWord_1259533
  simp only [CollatzResearch.WordTrace]
  refine ⟨45938942545934526955639253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30625961697289684637092835 45938942545934526955639253)
  ·
    refine ⟨1076693965920340475522795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45938942545934526955639253 1076693965920340475522795)
    ·
      refine ⟨1615040948880510713284193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076693965920340475522795 1615040948880510713284193)
      ·
        refine ⟨1211280711660383034963145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615040948880510713284193 1211280711660383034963145)
        ·
          refine ⟨908460533745287276222359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211280711660383034963145 908460533745287276222359)
          ·
            refine ⟨1362690800617930914333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908460533745287276222359 1362690800617930914333539)
            ·
              refine ⟨2044036200926896371500309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362690800617930914333539 2044036200926896371500309)
              ·
                refine ⟨95814196918448267414077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2044036200926896371500309 95814196918448267414077)
                ·
                  rfl

theorem cell21_1259533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].length) (baseStart_1259533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259533 prefixEnd_1259533 := by exact prefixLift 1259533
  have htrace : WordTrace (prefixWord ++ tailWord_1259533) baseStart_1259533 baseEnd_1259533 := by
    simpa [prefixWord, tailWord_1259533, baseEnd_1259533] using wordTrace_append hprefix tailTrace_1259533
  have hstable : (prefixWord ++ tailWord_1259533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259533).length < 2 ^ (prefixWord ++ tailWord_1259533).sum := by decide
  have hdescent : baseEnd_1259533 < baseStart_1259533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259555 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_1259555 : Nat := 118140960795 + 1259555 * 2 ^ 59
def prefixEnd_1259555 : Nat := 4983230072969 + 3 ^ 40 * 1259555 * 2
def baseEnd_1259555 : Nat := 287447611455077652875519

theorem tailTrace_1259555 : CollatzResearch.WordTrace tailWord_1259555 prefixEnd_1259555 287447611455077652875519 := by
  unfold tailWord_1259555
  simp only [CollatzResearch.WordTrace]
  refine ⟨45939744951854824712940119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30626496634569883141960079 45939744951854824712940119)
  ·
    refine ⟨68909617427782237069410179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45939744951854824712940119 68909617427782237069410179)
    ·
      refine ⟨103364426141673355604115269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68909617427782237069410179 103364426141673355604115269)
      ·
        refine ⟨19380829901563754175771613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103364426141673355604115269 19380829901563754175771613)
        ·
          refine ⟨7267811213086407815914355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19380829901563754175771613 7267811213086407815914355)
          ·
            refine ⟨10901716819629611723871533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267811213086407815914355 10901716819629611723871533)
            ·
              refine ⟨4088143807361104396451825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10901716819629611723871533 4088143807361104396451825)
              ·
                refine ⟨3066107855520828297338869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088143807361104396451825 3066107855520828297338869)
                ·
                  refine ⟨287447611455077652875519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066107855520828297338869 287447611455077652875519)
                  ·
                    rfl

theorem cell21_1259555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_1259555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259555 prefixEnd_1259555 := by exact prefixLift 1259555
  have htrace : WordTrace (prefixWord ++ tailWord_1259555) baseStart_1259555 baseEnd_1259555 := by
    simpa [prefixWord, tailWord_1259555, baseEnd_1259555] using wordTrace_append hprefix tailTrace_1259555
  have hstable : (prefixWord ++ tailWord_1259555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259555).length < 2 ^ (prefixWord ++ tailWord_1259555).sum := by decide
  have hdescent : baseEnd_1259555 < baseStart_1259555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259676 : List Nat := [2, 2, 3, 2, 1, 1, 1, 9]
def baseStart_1259676 : Nat := 118140960795 + 1259676 * 2 ^ 59
def prefixEnd_1259676 : Nat := 4983230072969 + 3 ^ 40 * 1259676 * 2
def baseEnd_1259676 : Nat := 95825075101202777119535

theorem tailTrace_1259676 : CollatzResearch.WordTrace tailWord_1259676 prefixEnd_1259676 95825075101202777119535 := by
  unfold tailWord_1259676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22972079092208231189047441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30629438789610974918729921 22972079092208231189047441)
  ·
    refine ⟨17229059319156173391785581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22972079092208231189047441 17229059319156173391785581)
    ·
      refine ⟨6460897244683565021919593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17229059319156173391785581 6460897244683565021919593)
      ·
        refine ⟨4845672933512673766439695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6460897244683565021919593 4845672933512673766439695)
        ·
          refine ⟨7268509400269010649659543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845672933512673766439695 7268509400269010649659543)
          ·
            refine ⟨10902764100403515974489315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268509400269010649659543 10902764100403515974489315)
            ·
              refine ⟨16354146150605273961733973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902764100403515974489315 16354146150605273961733973)
              ·
                refine ⟨95825075101202777119535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16354146150605273961733973 95825075101202777119535)
                ·
                  rfl

theorem cell21_1259676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_1259676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259676 prefixEnd_1259676 := by exact prefixLift 1259676
  have htrace : WordTrace (prefixWord ++ tailWord_1259676) baseStart_1259676 baseEnd_1259676 := by
    simpa [prefixWord, tailWord_1259676, baseEnd_1259676] using wordTrace_append hprefix tailTrace_1259676
  have hstable : (prefixWord ++ tailWord_1259676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259676).length < 2 ^ (prefixWord ++ tailWord_1259676).sum := by decide
  have hdescent : baseEnd_1259676 < baseStart_1259676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259710 : List Nat := [4, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1259710 : Nat := 118140960795 + 1259710 * 2 ^ 59
def prefixEnd_1259710 : Nat := 4983230072969 + 3 ^ 40 * 1259710 * 2
def baseEnd_1259710 : Nat := 95827661522277275930623

theorem tailTrace_1259710 : CollatzResearch.WordTrace tailWord_1259710 prefixEnd_1259710 95827661522277275930623 := by
  unfold tailWord_1259710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743174783286660773104073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30630265510862190789888389 5743174783286660773104073)
  ·
    refine ⟨4307381087464995579828055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5743174783286660773104073 4307381087464995579828055)
    ·
      refine ⟨6461071631197493369742083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4307381087464995579828055 6461071631197493369742083)
      ·
        refine ⟨9691607446796240054613125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461071631197493369742083 9691607446796240054613125)
        ·
          refine ⟨1817176396274295010239961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9691607446796240054613125 1817176396274295010239961)
          ·
            refine ⟨1362882297205721257679971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817176396274295010239961 1362882297205721257679971)
            ·
              refine ⟨2044323445808581886519957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362882297205721257679971 2044323445808581886519957)
              ·
                refine ⟨95827661522277275930623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2044323445808581886519957 95827661522277275930623)
                ·
                  rfl

theorem cell21_1259710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1259710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259710 prefixEnd_1259710 := by exact prefixLift 1259710
  have htrace : WordTrace (prefixWord ++ tailWord_1259710) baseStart_1259710 baseEnd_1259710 := by
    simpa [prefixWord, tailWord_1259710, baseEnd_1259710] using wordTrace_append hprefix tailTrace_1259710
  have hstable : (prefixWord ++ tailWord_1259710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259710).length < 2 ^ (prefixWord ++ tailWord_1259710).sum := by decide
  have hdescent : baseEnd_1259710 < baseStart_1259710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259741 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1259741 : Nat := 118140960795 + 1259741 * 2 ^ 59
def prefixEnd_1259741 : Nat := 4983230072969 + 3 ^ 40 * 1259741 * 2
def baseEnd_1259741 : Nat := 287490059189182662775139

theorem tailTrace_1259741 : CollatzResearch.WordTrace tailWord_1259741 prefixEnd_1259741 287490059189182662775139 := by
  unfold tailWord_1259741
  simp only [CollatzResearch.WordTrace]
  refine ⟨45946528929180978479211077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30631019286120652319474051 45946528929180978479211077)
  ·
    refine ⟨8614974174221433464852077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45946528929180978479211077 8614974174221433464852077)
    ·
      refine ⟨3230615315333037549319529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8614974174221433464852077 3230615315333037549319529)
      ·
        refine ⟨2422961486499778161989647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3230615315333037549319529 2422961486499778161989647)
        ·
          refine ⟨3634442229749667242984471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422961486499778161989647 3634442229749667242984471)
          ·
            refine ⟨5451663344624500864476707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634442229749667242984471 5451663344624500864476707)
            ·
              refine ⟨8177495016936751296715061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5451663344624500864476707 8177495016936751296715061)
              ·
                refine ⟨766640157837820434067037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8177495016936751296715061 766640157837820434067037)
                ·
                  refine ⟨287490059189182662775139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766640157837820434067037 287490059189182662775139)
                  ·
                    rfl

theorem cell21_1259741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1259741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259741 prefixEnd_1259741 := by exact prefixLift 1259741
  have htrace : WordTrace (prefixWord ++ tailWord_1259741) baseStart_1259741 baseEnd_1259741 := by
    simpa [prefixWord, tailWord_1259741, baseEnd_1259741] using wordTrace_append hprefix tailTrace_1259741
  have hstable : (prefixWord ++ tailWord_1259741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259741).length < 2 ^ (prefixWord ++ tailWord_1259741).sum := by decide
  have hdescent : baseEnd_1259741 < baseStart_1259741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259752 : List Nat := [2, 1, 4, 1, 2, 3, 8]
def baseStart_1259752 : Nat := 118140960795 + 1259752 * 2 ^ 59
def prefixEnd_1259752 : Nat := 4983230072969 + 3 ^ 40 * 1259752 * 2
def baseEnd_1259752 : Nat := 31943618837672120899087

theorem tailTrace_1259752 : CollatzResearch.WordTrace tailWord_1259752 prefixEnd_1259752 31943618837672120899087 := by
  unfold tailWord_1259752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22973465066070563678930755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30631286754760751571907673 22973465066070563678930755)
  ·
    refine ⟨34460197599105845518396133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22973465066070563678930755 34460197599105845518396133)
    ·
      refine ⟨6461287049832346034699275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34460197599105845518396133 6461287049832346034699275)
      ·
        refine ⟨9691930574748519052048913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461287049832346034699275 9691930574748519052048913)
        ·
          refine ⟨7268947931061389289036685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9691930574748519052048913 7268947931061389289036685)
          ·
            refine ⟨2725855474148020983388757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7268947931061389289036685 2725855474148020983388757)
            ·
              refine ⟨31943618837672120899087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2725855474148020983388757 31943618837672120899087)
              ·
                rfl

theorem cell21_1259752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 8].length) (baseStart_1259752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259752 prefixEnd_1259752 := by exact prefixLift 1259752
  have htrace : WordTrace (prefixWord ++ tailWord_1259752) baseStart_1259752 baseEnd_1259752 := by
    simpa [prefixWord, tailWord_1259752, baseEnd_1259752] using wordTrace_append hprefix tailTrace_1259752
  have hstable : (prefixWord ++ tailWord_1259752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259752).length < 2 ^ (prefixWord ++ tailWord_1259752).sum := by decide
  have hdescent : baseEnd_1259752 < baseStart_1259752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259797 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1259797 : Nat := 118140960795 + 1259797 * 2 ^ 59
def prefixEnd_1259797 : Nat := 4983230072969 + 3 ^ 40 * 1259797 * 2
def baseEnd_1259797 : Nat := 287502839152139009841691

theorem tailTrace_1259797 : CollatzResearch.WordTrace tailWord_1259797 prefixEnd_1259797 287502839152139009841691 := by
  unfold tailWord_1259797
  simp only [CollatzResearch.WordTrace]
  refine ⟨45948571416978100043249645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30632380944652066695499763 45948571416978100043249645)
  ·
    refine ⟨17230714281366787516218617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45948571416978100043249645 17230714281366787516218617)
    ·
      refine ⟨12923035711025090637163963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17230714281366787516218617 12923035711025090637163963)
      ·
        refine ⟨19384553566537635955745945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12923035711025090637163963 19384553566537635955745945)
        ·
          refine ⟨14538415174903226966809459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19384553566537635955745945 14538415174903226966809459)
          ·
            refine ⟨21807622762354840450214189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14538415174903226966809459 21807622762354840450214189)
            ·
              refine ⟨8177858535883065168830321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21807622762354840450214189 8177858535883065168830321)
              ·
                refine ⟨6133393901912298876622741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8177858535883065168830321 6133393901912298876622741)
                ·
                  refine ⟨287502839152139009841691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6133393901912298876622741 287502839152139009841691)
                  ·
                    rfl

theorem cell21_1259797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1259797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259797 prefixEnd_1259797 := by exact prefixLift 1259797
  have htrace : WordTrace (prefixWord ++ tailWord_1259797) baseStart_1259797 baseEnd_1259797 := by
    simpa [prefixWord, tailWord_1259797, baseEnd_1259797] using wordTrace_append hprefix tailTrace_1259797
  have hstable : (prefixWord ++ tailWord_1259797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259797).length < 2 ^ (prefixWord ++ tailWord_1259797).sum := by decide
  have hdescent : baseEnd_1259797 < baseStart_1259797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259868 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1259868 : Nat := 118140960795 + 1259868 * 2 ^ 59
def prefixEnd_1259868 : Nat := 4983230072969 + 3 ^ 40 * 1259868 * 2
def baseEnd_1259868 : Nat := 287519042319458664158213

theorem tailTrace_1259868 : CollatzResearch.WordTrace tailWord_1259868 prefixEnd_1259868 287519042319458664158213 := by
  unfold tailWord_1259868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22975580499860439584542129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30634107333147252779389505 22975580499860439584542129)
  ·
    refine ⟨17231685374895329688406597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22975580499860439584542129 17231685374895329688406597)
    ·
      refine ⟨3230941007792874316576237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17231685374895329688406597 3230941007792874316576237)
      ·
        refine ⟨1211602877922327868716089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3230941007792874316576237 1211602877922327868716089)
        ·
          refine ⟨908702158441745901537067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211602877922327868716089 908702158441745901537067)
          ·
            refine ⟨1363053237662618852305601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908702158441745901537067 1363053237662618852305601)
            ·
              refine ⟨1022289928246964139229201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363053237662618852305601 1022289928246964139229201)
              ·
                refine ⟨766717446185223104421901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022289928246964139229201 766717446185223104421901)
                ·
                  refine ⟨287519042319458664158213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766717446185223104421901 287519042319458664158213)
                  ·
                    rfl

theorem cell21_1259868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1259868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259868 prefixEnd_1259868 := by exact prefixLift 1259868
  have htrace : WordTrace (prefixWord ++ tailWord_1259868) baseStart_1259868 baseEnd_1259868 := by
    simpa [prefixWord, tailWord_1259868, baseEnd_1259868] using wordTrace_append hprefix tailTrace_1259868
  have hstable : (prefixWord ++ tailWord_1259868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259868).length < 2 ^ (prefixWord ++ tailWord_1259868).sum := by decide
  have hdescent : baseEnd_1259868 < baseStart_1259868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259876 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_1259876 : Nat := 118140960795 + 1259876 * 2 ^ 59
def prefixEnd_1259876 : Nat := 4983230072969 + 3 ^ 40 * 1259876 * 2
def baseEnd_1259876 : Nat := 287520868028452428024863

theorem tailTrace_1259876 : CollatzResearch.WordTrace tailWord_1259876 prefixEnd_1259876 287520868028452428024863 := by
  unfold tailWord_1259876
  simp only [CollatzResearch.WordTrace]
  refine ⟨22975726391845948267687741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30634301855794597690250321 22975726391845948267687741)
  ·
    refine ⟨8615897396942230600382903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22975726391845948267687741 8615897396942230600382903)
    ·
      refine ⟨12923846095413345900574355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615897396942230600382903 12923846095413345900574355)
      ·
        refine ⟨19385769143120018850861533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12923846095413345900574355 19385769143120018850861533)
        ·
          refine ⟨7269663428670007069073075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19385769143120018850861533 7269663428670007069073075)
          ·
            refine ⟨10904495143005010603609613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269663428670007069073075 10904495143005010603609613)
            ·
              refine ⟨4089185678626878976353605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10904495143005010603609613 4089185678626878976353605)
              ·
                refine ⟨766722314742539808066301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4089185678626878976353605 766722314742539808066301)
                ·
                  refine ⟨287520868028452428024863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766722314742539808066301 287520868028452428024863)
                  ·
                    rfl

theorem cell21_1259876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_1259876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259876 prefixEnd_1259876 := by exact prefixLift 1259876
  have htrace : WordTrace (prefixWord ++ tailWord_1259876) baseStart_1259876 baseEnd_1259876 := by
    simpa [prefixWord, tailWord_1259876, baseEnd_1259876] using wordTrace_append hprefix tailTrace_1259876
  have hstable : (prefixWord ++ tailWord_1259876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259876).length < 2 ^ (prefixWord ++ tailWord_1259876).sum := by decide
  have hdescent : baseEnd_1259876 < baseStart_1259876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259887 : List Nat := [1, 1, 2, 1, 3, 1, 2, 10]
def baseStart_1259887 : Nat := 118140960795 + 1259887 * 2 ^ 59
def prefixEnd_1259887 : Nat := 4983230072969 + 3 ^ 40 * 1259887 * 2
def baseEnd_1259887 : Nat := 95841126126106284447169

theorem tailTrace_1259887 : CollatzResearch.WordTrace tailWord_1259887 prefixEnd_1259887 95841126126106284447169 := by
  unfold tailWord_1259887
  simp only [CollatzResearch.WordTrace]
  refine ⟨45951853986652045414025915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30634569324434696942683943 45951853986652045414025915)
  ·
    refine ⟨68927780979978068121038873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45951853986652045414025915 68927780979978068121038873)
    ·
      refine ⟨51695835734983551090779155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68927780979978068121038873 51695835734983551090779155)
      ·
        refine ⟨77543753602475326636168733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51695835734983551090779155 77543753602475326636168733)
        ·
          refine ⟨29078907600928247488563275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77543753602475326636168733 29078907600928247488563275)
          ·
            refine ⟨43618361401392371232844913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29078907600928247488563275 43618361401392371232844913)
            ·
              refine ⟨32713771051044278424633685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43618361401392371232844913 32713771051044278424633685)
              ·
                refine ⟨95841126126106284447169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32713771051044278424633685 95841126126106284447169)
                ·
                  rfl

theorem cell21_1259887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_1259887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259887 prefixEnd_1259887 := by exact prefixLift 1259887
  have htrace : WordTrace (prefixWord ++ tailWord_1259887) baseStart_1259887 baseEnd_1259887 := by
    simpa [prefixWord, tailWord_1259887, baseEnd_1259887] using wordTrace_append hprefix tailTrace_1259887
  have hstable : (prefixWord ++ tailWord_1259887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259887).length < 2 ^ (prefixWord ++ tailWord_1259887).sum := by decide
  have hdescent : baseEnd_1259887 < baseStart_1259887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259890 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1259890 : Nat := 118140960795 + 1259890 * 2 ^ 59
def prefixEnd_1259890 : Nat := 4983230072969 + 3 ^ 40 * 1259890 * 2
def baseEnd_1259890 : Nat := 287524063019191514791501

theorem tailTrace_1259890 : CollatzResearch.WordTrace tailWord_1259890 prefixEnd_1259890 287524063019191514791501 := by
  unfold tailWord_1259890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487990851410294231596281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30634642270427451284256749 11487990851410294231596281)
  ·
    refine ⟨8615993138557720673697211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11487990851410294231596281 8615993138557720673697211)
    ·
      refine ⟨12923989707836581010545817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615993138557720673697211 12923989707836581010545817)
      ·
        refine ⟨9692992280877435757909363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12923989707836581010545817 9692992280877435757909363)
        ·
          refine ⟨14539488421316153636864045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692992280877435757909363 14539488421316153636864045)
          ·
            refine ⟨5452308157993557613824017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14539488421316153636864045 5452308157993557613824017)
            ·
              refine ⟨4089231118495168210368013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5452308157993557613824017 4089231118495168210368013)
              ·
                refine ⟨1533461669435688078888005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4089231118495168210368013 1533461669435688078888005)
                ·
                  refine ⟨287524063019191514791501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533461669435688078888005 287524063019191514791501)
                  ·
                    rfl

theorem cell21_1259890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1259890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259890 prefixEnd_1259890 := by exact prefixLift 1259890
  have htrace : WordTrace (prefixWord ++ tailWord_1259890) baseStart_1259890 baseEnd_1259890 := by
    simpa [prefixWord, tailWord_1259890, baseEnd_1259890] using wordTrace_append hprefix tailTrace_1259890
  have hstable : (prefixWord ++ tailWord_1259890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259890).length < 2 ^ (prefixWord ++ tailWord_1259890).sum := by decide
  have hdescent : baseEnd_1259890 < baseStart_1259890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259924 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1259924 : Nat := 118140960795 + 1259924 * 2 ^ 59
def prefixEnd_1259924 : Nat := 4983230072969 + 3 ^ 40 * 1259924 * 2
def baseEnd_1259924 : Nat := 287531822282415011224765

theorem tailTrace_1259924 : CollatzResearch.WordTrace tailWord_1259924 prefixEnd_1259924 287531822282415011224765 := by
  unfold tailWord_1259924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976601743759000366561413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30635468991678667155415217 22976601743759000366561413)
  ·
    refine ⟨4308112826954812568730265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22976601743759000366561413 4308112826954812568730265)
    ·
      refine ⟨3231084620216109426547699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4308112826954812568730265 3231084620216109426547699)
      ·
        refine ⟨4846626930324164139821549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231084620216109426547699 4846626930324164139821549)
        ·
          refine ⟨1817485098871561552433081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4846626930324164139821549 1817485098871561552433081)
          ·
            refine ⟨1363113824153671164324811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817485098871561552433081 1363113824153671164324811)
            ·
              refine ⟨2044670736230506746487217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363113824153671164324811 2044670736230506746487217)
              ·
                refine ⟨1533503052172880059865413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044670736230506746487217 1533503052172880059865413)
                ·
                  refine ⟨287531822282415011224765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533503052172880059865413 287531822282415011224765)
                  ·
                    rfl

theorem cell21_1259924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1259924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259924 prefixEnd_1259924 := by exact prefixLift 1259924
  have htrace : WordTrace (prefixWord ++ tailWord_1259924) baseStart_1259924 baseEnd_1259924 := by
    simpa [prefixWord, tailWord_1259924, baseEnd_1259924] using wordTrace_append hprefix tailTrace_1259924
  have hstable : (prefixWord ++ tailWord_1259924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259924).length < 2 ^ (prefixWord ++ tailWord_1259924).sum := by decide
  have hdescent : baseEnd_1259924 < baseStart_1259924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259935 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_1259935 : Nat := 118140960795 + 1259935 * 2 ^ 59
def prefixEnd_1259935 : Nat := 4983230072969 + 3 ^ 40 * 1259935 * 2
def baseEnd_1259935 : Nat := 287534332632281436541409

theorem tailTrace_1259935 : CollatzResearch.WordTrace tailWord_1259935 prefixEnd_1259935 287534332632281436541409 := by
  unfold tailWord_1259935
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953604690478149611773259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30635736460318766407848839 45953604690478149611773259)
  ·
    refine ⟨68930407035717224417659889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45953604690478149611773259 68930407035717224417659889)
    ·
      refine ⟨51697805276787918313244917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68930407035717224417659889 51697805276787918313244917)
      ·
        refine ⟨4846669244698867341866711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51697805276787918313244917 4846669244698867341866711)
        ·
          refine ⟨7270003867048301012800067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846669244698867341866711 7270003867048301012800067)
          ·
            refine ⟨10905005800572451519200101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270003867048301012800067 10905005800572451519200101)
            ·
              refine ⟨2044688587607334659850019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10905005800572451519200101 2044688587607334659850019)
              ·
                refine ⟨3067032881411001989775029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044688587607334659850019 3067032881411001989775029)
                ·
                  refine ⟨287534332632281436541409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067032881411001989775029 287534332632281436541409)
                  ·
                    rfl

theorem cell21_1259935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_1259935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259935 prefixEnd_1259935 := by exact prefixLift 1259935
  have htrace : WordTrace (prefixWord ++ tailWord_1259935) baseStart_1259935 baseEnd_1259935 := by
    simpa [prefixWord, tailWord_1259935, baseEnd_1259935] using wordTrace_append hprefix tailTrace_1259935
  have hstable : (prefixWord ++ tailWord_1259935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259935).length < 2 ^ (prefixWord ++ tailWord_1259935).sum := by decide
  have hdescent : baseEnd_1259935 < baseStart_1259935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1259986 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1259986 : Nat := 118140960795 + 1259986 * 2 ^ 59
def prefixEnd_1259986 : Nat := 4983230072969 + 3 ^ 40 * 1259986 * 2
def baseEnd_1259986 : Nat := 287545971527116681191305

theorem tailTrace_1259986 : CollatzResearch.WordTrace tailWord_1259986 prefixEnd_1259986 287545971527116681191305 := by
  unfold tailWord_1259986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488866203323346330469953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30636976542195590214586541 11488866203323346330469953)
  ·
    refine ⟨8616649652492509747852465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11488866203323346330469953 8616649652492509747852465)
    ·
      refine ⟨6462487239369382310889349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8616649652492509747852465 6462487239369382310889349)
      ·
        refine ⟨1211716357381759183291753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6462487239369382310889349 1211716357381759183291753)
        ·
          refine ⟨908787268036319387468815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211716357381759183291753 908787268036319387468815)
          ·
            refine ⟨1363180902054479081203223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908787268036319387468815 1363180902054479081203223)
            ·
              refine ⟨2044771353081718621804835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363180902054479081203223 2044771353081718621804835)
              ·
                refine ⟨3067157029622577932707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044771353081718621804835 3067157029622577932707253)
                ·
                  refine ⟨287545971527116681191305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067157029622577932707253 287545971527116681191305)
                  ·
                    rfl

theorem cell21_1259986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1259986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1259986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1259986 prefixEnd_1259986 := by exact prefixLift 1259986
  have htrace : WordTrace (prefixWord ++ tailWord_1259986) baseStart_1259986 baseEnd_1259986 := by
    simpa [prefixWord, tailWord_1259986, baseEnd_1259986] using wordTrace_append hprefix tailTrace_1259986
  have hstable : (prefixWord ++ tailWord_1259986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1259986).length < 2 ^ (prefixWord ++ tailWord_1259986).sum := by decide
  have hdescent : baseEnd_1259986 < baseStart_1259986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1259986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260039 : List Nat := [1, 1, 4, 3, 12]
def baseStart_1260039 : Nat := 118140960795 + 1260039 * 2 ^ 59
def prefixEnd_1260039 : Nat := 4983230072969 + 3 ^ 40 * 1260039 * 2
def baseEnd_1260039 : Nat := 3550099590730868726023

theorem tailTrace_1260039 : CollatzResearch.WordTrace tailWord_1260039 prefixEnd_1260039 3550099590730868726023 := by
  unfold tailWord_1260039
  simp only [CollatzResearch.WordTrace]
  refine ⟨45957397882101375373559171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30638265254734250249039447 45957397882101375373559171)
  ·
    refine ⟨68936096823152063060338757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45957397882101375373559171 68936096823152063060338757)
    ·
      refine ⟨12925518154341011823813517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68936096823152063060338757 12925518154341011823813517)
      ·
        refine ⟨4847069307877879433930069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12925518154341011823813517 4847069307877879433930069)
        ·
          refine ⟨3550099590730868726023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4847069307877879433930069 3550099590730868726023)
          ·
            rfl

theorem cell21_1260039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 12].length) (baseStart_1260039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260039 prefixEnd_1260039 := by exact prefixLift 1260039
  have htrace : WordTrace (prefixWord ++ tailWord_1260039) baseStart_1260039 baseEnd_1260039 := by
    simpa [prefixWord, tailWord_1260039, baseEnd_1260039] using wordTrace_append hprefix tailTrace_1260039
  have hstable : (prefixWord ++ tailWord_1260039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260039).length < 2 ^ (prefixWord ++ tailWord_1260039).sum := by decide
  have hdescent : baseEnd_1260039 < baseStart_1260039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260042 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1260042 : Nat := 118140960795 + 1260042 * 2 ^ 59
def prefixEnd_1260042 : Nat := 4983230072969 + 3 ^ 40 * 1260042 * 2
def baseEnd_1260042 : Nat := 287558751490073028257857

theorem tailTrace_1260042 : CollatzResearch.WordTrace tailWord_1260042 prefixEnd_1260042 287558751490073028257857 := by
  unfold tailWord_1260042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489376825272626721479595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30638338200727004590612253 11489376825272626721479595)
  ·
    refine ⟨17234065237908940082219393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11489376825272626721479595 17234065237908940082219393)
    ·
      refine ⟨12925548928431705061664545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17234065237908940082219393 12925548928431705061664545)
      ·
        refine ⟨9694161696323778796248409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12925548928431705061664545 9694161696323778796248409)
        ·
          refine ⟨7270621272242834097186307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9694161696323778796248409 7270621272242834097186307)
          ·
            refine ⟨10905931908364251145779461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270621272242834097186307 10905931908364251145779461)
            ·
              refine ⟨2044862232818297089833649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10905931908364251145779461 2044862232818297089833649)
              ·
                refine ⟨1533646674613722817375237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044862232818297089833649 1533646674613722817375237)
                ·
                  refine ⟨287558751490073028257857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533646674613722817375237 287558751490073028257857)
                  ·
                    rfl

theorem cell21_1260042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1260042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260042 prefixEnd_1260042 := by exact prefixLift 1260042
  have htrace : WordTrace (prefixWord ++ tailWord_1260042) baseStart_1260042 baseEnd_1260042 := by
    simpa [prefixWord, tailWord_1260042, baseEnd_1260042] using wordTrace_append hprefix tailTrace_1260042
  have hstable : (prefixWord ++ tailWord_1260042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260042).length < 2 ^ (prefixWord ++ tailWord_1260042).sum := by decide
  have hdescent : baseEnd_1260042 < baseStart_1260042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260056 : List Nat := [2, 1, 2, 3, 3, 1, 3, 6]
def baseStart_1260056 : Nat := 118140960795 + 1260056 * 2 ^ 59
def prefixEnd_1260056 : Nat := 4983230072969 + 3 ^ 40 * 1260056 * 2
def baseEnd_1260056 : Nat := 95853982160270705008165

theorem tailTrace_1260056 : CollatzResearch.WordTrace tailWord_1260056 prefixEnd_1260056 95853982160270705008165 := by
  unfold tailWord_1260056
  simp only [CollatzResearch.WordTrace]
  refine ⟨22979008961519893638464011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30638678615359858184618681 22979008961519893638464011)
  ·
    refine ⟨34468513442279840457696017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22979008961519893638464011 34468513442279840457696017)
    ·
      refine ⟨25851385081709880343272013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34468513442279840457696017 25851385081709880343272013)
      ·
        refine ⟨9694269405641205128727005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25851385081709880343272013 9694269405641205128727005)
        ·
          refine ⟨3635351027115451923272627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9694269405641205128727005 3635351027115451923272627)
          ·
            refine ⟨5453026540673177884908941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635351027115451923272627 5453026540673177884908941)
            ·
              refine ⟨2044884952752441706840853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453026540673177884908941 2044884952752441706840853)
              ·
                refine ⟨95853982160270705008165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2044884952752441706840853 95853982160270705008165)
                ·
                  rfl

theorem cell21_1260056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_1260056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260056 prefixEnd_1260056 := by exact prefixLift 1260056
  have htrace : WordTrace (prefixWord ++ tailWord_1260056) baseStart_1260056 baseEnd_1260056 := by
    simpa [prefixWord, tailWord_1260056, baseEnd_1260056] using wordTrace_append hprefix tailTrace_1260056
  have hstable : (prefixWord ++ tailWord_1260056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260056).length < 2 ^ (prefixWord ++ tailWord_1260056).sum := by decide
  have hdescent : baseEnd_1260056 < baseStart_1260056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260101 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_1260101 : Nat := 118140960795 + 1260101 * 2 ^ 59
def prefixEnd_1260101 : Nat := 4983230072969 + 3 ^ 40 * 1260101 * 2
def baseEnd_1260101 : Nat := 287572216093902036774403

theorem tailTrace_1260101 : CollatzResearch.WordTrace tailWord_1260101 prefixEnd_1260101 287572216093902036774403 := by
  unfold tailWord_1260101
  simp only [CollatzResearch.WordTrace]
  refine ⟨45959659207876759962316157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30639772805251173308210771 45959659207876759962316157)
  ·
    refine ⟨17234872202953784985868559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45959659207876759962316157 17234872202953784985868559)
    ·
      refine ⟨25852308304430677478802839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17234872202953784985868559 25852308304430677478802839)
      ·
        refine ⟨38778462456646016218204259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25852308304430677478802839 38778462456646016218204259)
        ·
          refine ⟨58167693684969024327306389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38778462456646016218204259 58167693684969024327306389)
          ·
            refine ⟨2726610641482923015342487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58167693684969024327306389 2726610641482923015342487)
            ·
              refine ⟨4089915962224384523013731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726610641482923015342487 4089915962224384523013731)
              ·
                refine ⟨6134873943336576784520597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089915962224384523013731 6134873943336576784520597)
                ·
                  refine ⟨287572216093902036774403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6134873943336576784520597 287572216093902036774403)
                  ·
                    rfl

theorem cell21_1260101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_1260101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260101 prefixEnd_1260101 := by exact prefixLift 1260101
  have htrace : WordTrace (prefixWord ++ tailWord_1260101) baseStart_1260101 baseEnd_1260101 := by
    simpa [prefixWord, tailWord_1260101, baseEnd_1260101] using wordTrace_append hprefix tailTrace_1260101
  have hstable : (prefixWord ++ tailWord_1260101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260101).length < 2 ^ (prefixWord ++ tailWord_1260101).sum := by decide
  have hdescent : baseEnd_1260101 < baseStart_1260101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260149 : List Nat := [1, 3, 4, 2, 2, 2, 7]
def baseStart_1260149 : Nat := 118140960795 + 1260149 * 2 ^ 59
def prefixEnd_1260149 : Nat := 4983230072969 + 3 ^ 40 * 1260149 * 2
def baseEnd_1260149 : Nat := 31953685594207179997145

theorem tailTrace_1260149 : CollatzResearch.WordTrace tailWord_1260149 prefixEnd_1260149 31953685594207179997145 := by
  unfold tailWord_1260149
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961409911702864160063501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30640939941135242773375667 45961409911702864160063501)
  ·
    refine ⟨17235528716888574060023813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45961409911702864160063501 17235528716888574060023813)
    ·
      refine ⟨3231661634416607636254465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17235528716888574060023813 3231661634416607636254465)
      ·
        refine ⟨2423746225812455727190849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3231661634416607636254465 2423746225812455727190849)
        ·
          refine ⟨1817809669359341795393137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423746225812455727190849 1817809669359341795393137)
          ·
            refine ⟨1363357252019506346544853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817809669359341795393137 1363357252019506346544853)
            ·
              refine ⟨31953685594207179997145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1363357252019506346544853 31953685594207179997145)
              ·
                rfl

theorem cell21_1260149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 7].length) (baseStart_1260149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260149 prefixEnd_1260149 := by exact prefixLift 1260149
  have htrace : WordTrace (prefixWord ++ tailWord_1260149) baseStart_1260149 baseEnd_1260149 := by
    simpa [prefixWord, tailWord_1260149, baseEnd_1260149] using wordTrace_append hprefix tailTrace_1260149
  have hstable : (prefixWord ++ tailWord_1260149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260149).length < 2 ^ (prefixWord ++ tailWord_1260149).sum := by decide
  have hdescent : baseEnd_1260149 < baseStart_1260149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260163 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 3]
def baseStart_1260163 : Nat := 118140960795 + 1260163 * 2 ^ 59
def prefixEnd_1260163 : Nat := 4983230072969 + 3 ^ 40 * 1260163 * 2
def baseEnd_1260163 : Nat := 287586365338603706740943

theorem tailTrace_1260163 : CollatzResearch.WordTrace tailWord_1260163 prefixEnd_1260163 287586365338603706740943 := by
  unfold tailWord_1260163
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961920533652144551073143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30641280355768096367382095 45961920533652144551073143)
  ·
    refine ⟨68942880800478216826609715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45961920533652144551073143 68942880800478216826609715)
    ·
      refine ⟨103414321200717325239914573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68942880800478216826609715 103414321200717325239914573)
      ·
        refine ⟨38780370450268996964967965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103414321200717325239914573 38780370450268996964967965)
        ·
          refine ⟨14542638918850873861862987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38780370450268996964967965 14542638918850873861862987)
          ·
            refine ⟨21813958378276310792794481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14542638918850873861862987 21813958378276310792794481)
            ·
              refine ⟨16360468783707233094595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21813958378276310792794481 16360468783707233094595861)
              ·
                refine ⟨766896974236276551309181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16360468783707233094595861 766896974236276551309181)
                ·
                  refine ⟨287586365338603706740943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766896974236276551309181 287586365338603706740943)
                  ·
                    rfl

theorem cell21_1260163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].length) (baseStart_1260163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260163 prefixEnd_1260163 := by exact prefixLift 1260163
  have htrace : WordTrace (prefixWord ++ tailWord_1260163) baseStart_1260163 baseEnd_1260163 := by
    simpa [prefixWord, tailWord_1260163, baseEnd_1260163] using wordTrace_append hprefix tailTrace_1260163
  have hstable : (prefixWord ++ tailWord_1260163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260163).length < 2 ^ (prefixWord ++ tailWord_1260163).sum := by decide
  have hdescent : baseEnd_1260163 < baseStart_1260163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260214 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1260214 : Nat := 118140960795 + 1260214 * 2 ^ 59
def prefixEnd_1260214 : Nat := 4983230072969 + 3 ^ 40 * 1260214 * 2
def baseEnd_1260214 : Nat := 287598004233438951390839

theorem tailTrace_1260214 : CollatzResearch.WordTrace tailWord_1260214 prefixEnd_1260214 287598004233438951390839 := by
  unfold tailWord_1260214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872736291029211266323731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30642520437644920174119797 2872736291029211266323731)
  ·
    refine ⟨4309104436543816899485597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872736291029211266323731 4309104436543816899485597)
    ·
      refine ⟨1615914163703931337307099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4309104436543816899485597 1615914163703931337307099)
      ·
        refine ⟨2423871245555897005960649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615914163703931337307099 2423871245555897005960649)
        ·
          refine ⟨1817903434166922754470487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423871245555897005960649 1817903434166922754470487)
          ·
            refine ⟨2726855151250384131705731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817903434166922754470487 2726855151250384131705731)
            ·
              refine ⟨4090282726875576197558597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726855151250384131705731 4090282726875576197558597)
              ·
                refine ⟨766928011289170537042237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4090282726875576197558597 766928011289170537042237)
                ·
                  refine ⟨287598004233438951390839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766928011289170537042237 287598004233438951390839)
                  ·
                    rfl

theorem cell21_1260214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1260214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260214 prefixEnd_1260214 := by exact prefixLift 1260214
  have htrace : WordTrace (prefixWord ++ tailWord_1260214) baseStart_1260214 baseEnd_1260214 := by
    simpa [prefixWord, tailWord_1260214, baseEnd_1260214] using wordTrace_append hprefix tailTrace_1260214
  have hstable : (prefixWord ++ tailWord_1260214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260214).length < 2 ^ (prefixWord ++ tailWord_1260214).sum := by decide
  have hdescent : baseEnd_1260214 < baseStart_1260214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260270 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1260270 : Nat := 118140960795 + 1260270 * 2 ^ 59
def prefixEnd_1260270 : Nat := 4983230072969 + 3 ^ 40 * 1260270 * 2
def baseEnd_1260270 : Nat := 287610784196395298457391

theorem tailTrace_1260270 : CollatzResearch.WordTrace tailWord_1260270 prefixEnd_1260270 287610784196395298457391 := by
  unfold tailWord_1260270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745727893033062728152283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30643882096176334550145509 5745727893033062728152283)
  ·
    refine ⟨8618591839549594092228425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5745727893033062728152283 8618591839549594092228425)
    ·
      refine ⟨6463943879662195569171319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8618591839549594092228425 6463943879662195569171319)
      ·
        refine ⟨9695915819493293353756979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463943879662195569171319 9695915819493293353756979)
        ·
          refine ⟨14543873729239940030635469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695915819493293353756979 14543873729239940030635469)
          ·
            refine ⟨5453952648464977511488301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14543873729239940030635469 5453952648464977511488301)
            ·
              refine ⟨2045232243174366566808113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5453952648464977511488301 2045232243174366566808113)
              ·
                refine ⟨1533924182380774925106085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045232243174366566808113 1533924182380774925106085)
                ·
                  refine ⟨287610784196395298457391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1533924182380774925106085 287610784196395298457391)
                  ·
                    rfl

theorem cell21_1260270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1260270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260270 prefixEnd_1260270 := by exact prefixLift 1260270
  have htrace : WordTrace (prefixWord ++ tailWord_1260270) baseStart_1260270 baseEnd_1260270 := by
    simpa [prefixWord, tailWord_1260270, baseEnd_1260270] using wordTrace_append hprefix tailTrace_1260270
  have hstable : (prefixWord ++ tailWord_1260270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260270).length < 2 ^ (prefixWord ++ tailWord_1260270).sum := by decide
  have hdescent : baseEnd_1260270 < baseStart_1260270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260298 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1260298 : Nat := 118140960795 + 1260298 * 2 ^ 59
def prefixEnd_1260298 : Nat := 4983230072969 + 3 ^ 40 * 1260298 * 2
def baseEnd_1260298 : Nat := 287617174177873471990667

theorem tailTrace_1260298 : CollatzResearch.WordTrace tailWord_1260298 prefixEnd_1260298 287617174177873471990667 := by
  unfold tailWord_1260298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491711097040765651809387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30644562925442041738158365 11491711097040765651809387)
  ·
    refine ⟨17237566645561148477714081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11491711097040765651809387 17237566645561148477714081)
    ·
      refine ⟨12928174984170861358285561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17237566645561148477714081 12928174984170861358285561)
      ·
        refine ⟨9696131238128146018714171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12928174984170861358285561 9696131238128146018714171)
        ·
          refine ⟨14544196857192219028071257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9696131238128146018714171 14544196857192219028071257)
          ·
            refine ⟨10908147642894164271053443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14544196857192219028071257 10908147642894164271053443)
            ·
              refine ⟨16362221464341246406580165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908147642894164271053443 16362221464341246406580165)
              ·
                refine ⟨3067916524563983701233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16362221464341246406580165 3067916524563983701233781)
                ·
                  refine ⟨287617174177873471990667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067916524563983701233781 287617174177873471990667)
                  ·
                    rfl

theorem cell21_1260298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1260298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260298 prefixEnd_1260298 := by exact prefixLift 1260298
  have htrace : WordTrace (prefixWord ++ tailWord_1260298) baseStart_1260298 baseEnd_1260298 := by
    simpa [prefixWord, tailWord_1260298, baseEnd_1260298] using wordTrace_append hprefix tailTrace_1260298
  have hstable : (prefixWord ++ tailWord_1260298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260298).length < 2 ^ (prefixWord ++ tailWord_1260298).sum := by decide
  have hdescent : baseEnd_1260298 < baseStart_1260298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260332 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_1260332 : Nat := 118140960795 + 1260332 * 2 ^ 59
def prefixEnd_1260332 : Nat := 4983230072969 + 3 ^ 40 * 1260332 * 2
def baseEnd_1260332 : Nat := 287624933441096968423931

theorem tailTrace_1260332 : CollatzResearch.WordTrace tailWord_1260332 prefixEnd_1260332 287624933441096968423931 := by
  unfold tailWord_1260332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984042235019943206987625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30645389646693257609316833 22984042235019943206987625)
  ·
    refine ⟨17238031676264957405240719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22984042235019943206987625 17238031676264957405240719)
    ·
      refine ⟨25857047514397436107861079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17238031676264957405240719 25857047514397436107861079)
      ·
        refine ⟨38785571271596154161791619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25857047514397436107861079 38785571271596154161791619)
        ·
          refine ⟨58178356907394231242687429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38785571271596154161791619 58178356907394231242687429)
          ·
            refine ⟨10908441920136418358003893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58178356907394231242687429 10908441920136418358003893)
            ·
              refine ⟨1022666430012789221062865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10908441920136418358003893 1022666430012789221062865)
              ·
                refine ⟨766999822509591915797149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022666430012789221062865 766999822509591915797149)
                ·
                  refine ⟨287624933441096968423931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766999822509591915797149 287624933441096968423931)
                  ·
                    rfl

theorem cell21_1260332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_1260332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260332 prefixEnd_1260332 := by exact prefixLift 1260332
  have htrace : WordTrace (prefixWord ++ tailWord_1260332) baseStart_1260332 baseEnd_1260332 := by
    simpa [prefixWord, tailWord_1260332, baseEnd_1260332] using wordTrace_append hprefix tailTrace_1260332
  have hstable : (prefixWord ++ tailWord_1260332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260332).length < 2 ^ (prefixWord ++ tailWord_1260332).sum := by decide
  have hdescent : baseEnd_1260332 < baseStart_1260332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260343 : List Nat := [1, 1, 3, 1, 2, 1, 6, 6]
def baseStart_1260343 : Nat := 118140960795 + 1260343 * 2 ^ 59
def prefixEnd_1260343 : Nat := 4983230072969 + 3 ^ 40 * 1260343 * 2
def baseEnd_1260343 : Nat := 95875814596987797913525

theorem tailTrace_1260343 : CollatzResearch.WordTrace tailWord_1260343 prefixEnd_1260343 95875814596987797913525 := by
  unfold tailWord_1260343
  simp only [CollatzResearch.WordTrace]
  refine ⟨45968485673000035292625683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30645657115333356861750455 45968485673000035292625683)
  ·
    refine ⟨68952728509500052938938525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45968485673000035292625683 68952728509500052938938525)
    ·
      refine ⟨25857273191062519852101947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68952728509500052938938525 25857273191062519852101947)
      ·
        refine ⟨38785909786593779778152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25857273191062519852101947 38785909786593779778152921)
        ·
          refine ⟨29089432339945334833614691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38785909786593779778152921 29089432339945334833614691)
          ·
            refine ⟨43634148509918002250422037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29089432339945334833614691 43634148509918002250422037)
            ·
              refine ⟨2045350711402406355488533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43634148509918002250422037 2045350711402406355488533)
              ·
                refine ⟨95875814596987797913525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2045350711402406355488533 95875814596987797913525)
                ·
                  rfl

theorem cell21_1260343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_1260343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260343 prefixEnd_1260343 := by exact prefixLift 1260343
  have htrace : WordTrace (prefixWord ++ tailWord_1260343) baseStart_1260343 baseEnd_1260343 := by
    simpa [prefixWord, tailWord_1260343, baseEnd_1260343] using wordTrace_append hprefix tailTrace_1260343
  have hstable : (prefixWord ++ tailWord_1260343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260343).length < 2 ^ (prefixWord ++ tailWord_1260343).sum := by decide
  have hdescent : baseEnd_1260343 < baseStart_1260343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260346 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1260346 : Nat := 118140960795 + 1260346 * 2 ^ 59
def prefixEnd_1260346 : Nat := 4983230072969 + 3 ^ 40 * 1260346 * 2
def baseEnd_1260346 : Nat := 287628128431836055190569

theorem tailTrace_1260346 : CollatzResearch.WordTrace tailWord_1260346 prefixEnd_1260346 287628128431836055190569 := by
  unfold tailWord_1260346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492148772997291701246223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30645730061326111203323261 11492148772997291701246223)
  ·
    refine ⟨17238223159495937551869335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492148772997291701246223 17238223159495937551869335)
    ·
      refine ⟨25857334739243906327804003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17238223159495937551869335 25857334739243906327804003)
      ·
        refine ⟨38786002108865859491706005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25857334739243906327804003 38786002108865859491706005)
        ·
          refine ⟨1818093848853087163673719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38786002108865859491706005 1818093848853087163673719)
          ·
            refine ⟨2727140773279630745510579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818093848853087163673719 2727140773279630745510579)
            ·
              refine ⟨4090711159919446118265869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727140773279630745510579 4090711159919446118265869)
              ·
                refine ⟨1534016684969792294349701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4090711159919446118265869 1534016684969792294349701)
                ·
                  refine ⟨287628128431836055190569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534016684969792294349701 287628128431836055190569)
                  ·
                    rfl

theorem cell21_1260346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1260346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260346 prefixEnd_1260346 := by exact prefixLift 1260346
  have htrace : WordTrace (prefixWord ++ tailWord_1260346) baseStart_1260346 baseEnd_1260346 := by
    simpa [prefixWord, tailWord_1260346, baseEnd_1260346] using wordTrace_append hprefix tailTrace_1260346
  have hstable : (prefixWord ++ tailWord_1260346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260346).length < 2 ^ (prefixWord ++ tailWord_1260346).sum := by decide
  have hdescent : baseEnd_1260346 < baseStart_1260346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260433 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_1260433 : Nat := 118140960795 + 1260433 * 2 ^ 59
def prefixEnd_1260433 : Nat := 4983230072969 + 3 ^ 40 * 1260433 * 2
def baseEnd_1260433 : Nat := 287647983017143237240391

theorem tailTrace_1260433 : CollatzResearch.WordTrace tailWord_1260433 prefixEnd_1260433 287647983017143237240391 := by
  unfold tailWord_1260433
  simp only [CollatzResearch.WordTrace]
  refine ⟨45971768242673980663401953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30647845495115987108934635 45971768242673980663401953)
  ·
    refine ⟨34478826182005485497551465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45971768242673980663401953 34478826182005485497551465)
    ·
      refine ⟨25859119636504114123163599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34478826182005485497551465 25859119636504114123163599)
      ·
        refine ⟨38788679454756171184745399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25859119636504114123163599 38788679454756171184745399)
        ·
          refine ⟨58183019182134256777118099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38788679454756171184745399 58183019182134256777118099)
          ·
            refine ⟨87274528773201385165677149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58183019182134256777118099 87274528773201385165677149)
            ·
              refine ⟨32727948289950519437128931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87274528773201385165677149 32727948289950519437128931)
              ·
                refine ⟨49091922434925779155693397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32727948289950519437128931 49091922434925779155693397)
                ·
                  refine ⟨287647983017143237240391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49091922434925779155693397 287647983017143237240391)
                  ·
                    rfl

theorem cell21_1260433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_1260433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260433 prefixEnd_1260433 := by exact prefixLift 1260433
  have htrace : WordTrace (prefixWord ++ tailWord_1260433) baseStart_1260433 baseEnd_1260433 := by
    simpa [prefixWord, tailWord_1260433, baseEnd_1260433] using wordTrace_append hprefix tailTrace_1260433
  have hstable : (prefixWord ++ tailWord_1260433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260433).length < 2 ^ (prefixWord ++ tailWord_1260433).sum := by decide
  have hdescent : baseEnd_1260433 < baseStart_1260433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260495 : List Nat := [1, 1, 2, 1, 1, 8, 7]
def baseStart_1260495 : Nat := 118140960795 + 1260495 * 2 ^ 59
def prefixEnd_1260495 : Nat := 4983230072969 + 3 ^ 40 * 1260495 * 2
def baseEnd_1260495 : Nat := 31962459140204989689659

theorem tailTrace_1260495 : CollatzResearch.WordTrace tailWord_1260495 prefixEnd_1260495 31962459140204989689659 := by
  unfold tailWord_1260495
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974029568449365252158939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30649353045632910168105959 45974029568449365252158939)
  ·
    refine ⟨68961044352674047878238409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45974029568449365252158939 68961044352674047878238409)
    ·
      refine ⟨51720783264505535908678807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68961044352674047878238409 51720783264505535908678807)
      ·
        refine ⟨77581174896758303863018211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51720783264505535908678807 77581174896758303863018211)
        ·
          refine ⟨116371762345137455794527317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77581174896758303863018211 116371762345137455794527317)
          ·
            refine ⟨1363731589982079560092117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 116371762345137455794527317 1363731589982079560092117)
            ·
              refine ⟨31962459140204989689659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1363731589982079560092117 31962459140204989689659)
              ·
                rfl

theorem cell21_1260495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 7].length) (baseStart_1260495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260495 prefixEnd_1260495 := by exact prefixLift 1260495
  have htrace : WordTrace (prefixWord ++ tailWord_1260495) baseStart_1260495 baseEnd_1260495 := by
    simpa [prefixWord, tailWord_1260495, baseEnd_1260495] using wordTrace_append hprefix tailTrace_1260495
  have hstable : (prefixWord ++ tailWord_1260495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260495).length < 2 ^ (prefixWord ++ tailWord_1260495).sum := by decide
  have hdescent : baseEnd_1260495 < baseStart_1260495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260501 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1260501 : Nat := 118140960795 + 1260501 * 2 ^ 59
def prefixEnd_1260501 : Nat := 4983230072969 + 3 ^ 40 * 1260501 * 2
def baseEnd_1260501 : Nat := 287663501543590230106919

theorem tailTrace_1260501 : CollatzResearch.WordTrace tailWord_1260501 prefixEnd_1260501 287663501543590230106919 := by
  unfold tailWord_1260501
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974248406427628276877357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30649498937618418851251571 45974248406427628276877357)
  ·
    refine ⟨17240343152410360603829009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45974248406427628276877357 17240343152410360603829009)
    ·
      refine ⟨12930257364307770452871757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17240343152410360603829009 12930257364307770452871757)
      ·
        refine ⟨4848846511615413919826909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12930257364307770452871757 4848846511615413919826909)
        ·
          refine ⟨1818317441855780219935091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848846511615413919826909 1818317441855780219935091)
          ·
            refine ⟨2727476162783670329902637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818317441855780219935091 2727476162783670329902637)
            ·
              refine ⟨1022803561043876373713489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2727476162783670329902637 1022803561043876373713489)
              ·
                refine ⟨767102670782907280285117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022803561043876373713489 767102670782907280285117)
                ·
                  refine ⟨287663501543590230106919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767102670782907280285117 287663501543590230106919)
                  ·
                    rfl

theorem cell21_1260501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1260501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260501 prefixEnd_1260501 := by exact prefixLift 1260501
  have htrace : WordTrace (prefixWord ++ tailWord_1260501) baseStart_1260501 baseEnd_1260501 := by
    simpa [prefixWord, tailWord_1260501, baseEnd_1260501] using wordTrace_append hprefix tailTrace_1260501
  have hstable : (prefixWord ++ tailWord_1260501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260501).length < 2 ^ (prefixWord ++ tailWord_1260501).sum := by decide
  have hdescent : baseEnd_1260501 < baseStart_1260501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260616 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_1260616 : Nat := 118140960795 + 1260616 * 2 ^ 59
def prefixEnd_1260616 : Nat := 4983230072969 + 3 ^ 40 * 1260616 * 2
def baseEnd_1260616 : Nat := 287689746110375585690017

theorem tailTrace_1260616 : CollatzResearch.WordTrace tailWord_1260616 prefixEnd_1260616 287689746110375585690017 := by
  unfold tailWord_1260616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22989221400505501458656851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30652295200674001944875801 22989221400505501458656851)
  ·
    refine ⟨34483832100758252187985277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22989221400505501458656851 34483832100758252187985277)
    ·
      refine ⟨12931437037784344570494479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34483832100758252187985277 12931437037784344570494479)
      ·
        refine ⟨19397155556676516855741719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931437037784344570494479 19397155556676516855741719)
        ·
          refine ⟨29095733335014775283612579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19397155556676516855741719 29095733335014775283612579)
          ·
            refine ⟨43643600002522162925418869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29095733335014775283612579 43643600002522162925418869)
            ·
              refine ⟨4091587500236452774258019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43643600002522162925418869 4091587500236452774258019)
              ·
                refine ⟨6137381250354679161387029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091587500236452774258019 6137381250354679161387029)
                ·
                  refine ⟨287689746110375585690017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6137381250354679161387029 287689746110375585690017)
                  ·
                    rfl

theorem cell21_1260616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_1260616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260616 prefixEnd_1260616 := by exact prefixLift 1260616
  have htrace : WordTrace (prefixWord ++ tailWord_1260616) baseStart_1260616 baseEnd_1260616 := by
    simpa [prefixWord, tailWord_1260616, baseEnd_1260616] using wordTrace_append hprefix tailTrace_1260616
  have hstable : (prefixWord ++ tailWord_1260616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260616).length < 2 ^ (prefixWord ++ tailWord_1260616).sum := by decide
  have hdescent : baseEnd_1260616 < baseStart_1260616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260647 : List Nat := [1, 1, 5, 1, 1, 4, 1, 7]
def baseStart_1260647 : Nat := 118140960795 + 1260647 * 2 ^ 59
def prefixEnd_1260647 : Nat := 4983230072969 + 3 ^ 40 * 1260647 * 2
def baseEnd_1260647 : Nat := 95898940244242140224429

theorem tailTrace_1260647 : CollatzResearch.WordTrace tailWord_1260647 prefixEnd_1260647 95898940244242140224429 := by
  unfold tailWord_1260647
  simp only [CollatzResearch.WordTrace]
  refine ⟨45979573463898695211692195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30653048975932463474461463 45979573463898695211692195)
  ·
    refine ⟨68969360195848042817538293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45979573463898695211692195 68969360195848042817538293)
    ·
      refine ⟨6465877518360754014144215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68969360195848042817538293 6465877518360754014144215)
      ·
        refine ⟨9698816277541131021216323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465877518360754014144215 9698816277541131021216323)
        ·
          refine ⟨14548224416311696531824485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9698816277541131021216323 14548224416311696531824485)
          ·
            refine ⟨2727792078058443099717091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14548224416311696531824485 2727792078058443099717091)
            ·
              refine ⟨4091688117087664649575637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727792078058443099717091 4091688117087664649575637)
              ·
                refine ⟨95898940244242140224429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4091688117087664649575637 95898940244242140224429)
                ·
                  rfl

theorem cell21_1260647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_1260647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260647 prefixEnd_1260647 := by exact prefixLift 1260647
  have htrace : WordTrace (prefixWord ++ tailWord_1260647) baseStart_1260647 baseEnd_1260647 := by
    simpa [prefixWord, tailWord_1260647, baseEnd_1260647] using wordTrace_append hprefix tailTrace_1260647
  have hstable : (prefixWord ++ tailWord_1260647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260647).length < 2 ^ (prefixWord ++ tailWord_1260647).sum := by decide
  have hdescent : baseEnd_1260647 < baseStart_1260647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260670 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1260670 : Nat := 118140960795 + 1260670 * 2 ^ 59
def prefixEnd_1260670 : Nat := 4983230072969 + 3 ^ 40 * 1260670 * 2
def baseEnd_1260670 : Nat := 287702069646083491789907

theorem tailTrace_1260670 : CollatzResearch.WordTrace tailWord_1260670 prefixEnd_1260670 287702069646083491789907 := by
  unfold tailWord_1260670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747551542851921267472433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30653608228543580093186309 5747551542851921267472433)
  ·
    refine ⟨4310663657138940950604325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5747551542851921267472433 4310663657138940950604325)
    ·
      refine ⟨808249435713551428238311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4310663657138940950604325 808249435713551428238311)
      ·
        refine ⟨1212374153570327142357467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808249435713551428238311 1212374153570327142357467)
        ·
          refine ⟨1818561230355490713536201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212374153570327142357467 1818561230355490713536201)
          ·
            refine ⟨1363920922766618035152151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818561230355490713536201 1363920922766618035152151)
            ·
              refine ⟨2045881384149927052728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363920922766618035152151 2045881384149927052728227)
              ·
                refine ⟨3068822076224890579092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045881384149927052728227 3068822076224890579092341)
                ·
                  refine ⟨287702069646083491789907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3068822076224890579092341 287702069646083491789907)
                  ·
                    rfl

theorem cell21_1260670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1260670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260670 prefixEnd_1260670 := by exact prefixLift 1260670
  have htrace : WordTrace (prefixWord ++ tailWord_1260670) baseStart_1260670 baseEnd_1260670 := by
    simpa [prefixWord, tailWord_1260670, baseEnd_1260670] using wordTrace_append hprefix tailTrace_1260670
  have hstable : (prefixWord ++ tailWord_1260670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260670).length < 2 ^ (prefixWord ++ tailWord_1260670).sum := by decide
  have hdescent : baseEnd_1260670 < baseStart_1260670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260754 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1260754 : Nat := 118140960795 + 1260754 * 2 ^ 59
def prefixEnd_1260754 : Nat := 4983230072969 + 3 ^ 40 * 1260754 * 2
def baseEnd_1260754 : Nat := 287721239590518012389735

theorem tailTrace_1260754 : CollatzResearch.WordTrace tailWord_1260754 prefixEnd_1260754 287721239590518012389735 := by
  unfold tailWord_1260754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495869018627763121459329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30655650716340701657224877 11495869018627763121459329)
  ·
    refine ⟨8621901763970822341094497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11495869018627763121459329 8621901763970822341094497)
    ·
      refine ⟨6466426322978116755820873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8621901763970822341094497 6466426322978116755820873)
      ·
        refine ⟨4849819742233587566865655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6466426322978116755820873 4849819742233587566865655)
        ·
          refine ⟨7274729613350381350298483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849819742233587566865655 7274729613350381350298483)
          ·
            refine ⟨10912094420025572025447725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7274729613350381350298483 10912094420025572025447725)
            ·
              refine ⟨4092035407509589509542897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10912094420025572025447725 4092035407509589509542897)
              ·
                refine ⟨3069026555632192132157173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092035407509589509542897 3069026555632192132157173)
                ·
                  refine ⟨287721239590518012389735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3069026555632192132157173 287721239590518012389735)
                  ·
                    rfl

theorem cell21_1260754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1260754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260754 prefixEnd_1260754 := by exact prefixLift 1260754
  have htrace : WordTrace (prefixWord ++ tailWord_1260754) baseStart_1260754 baseEnd_1260754 := by
    simpa [prefixWord, tailWord_1260754, baseEnd_1260754] using wordTrace_append hprefix tailTrace_1260754
  have hstable : (prefixWord ++ tailWord_1260754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260754).length < 2 ^ (prefixWord ++ tailWord_1260754).sum := by decide
  have hdescent : baseEnd_1260754 < baseStart_1260754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260844 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1260844 : Nat := 118140960795 + 1260844 * 2 ^ 59
def prefixEnd_1260844 : Nat := 4983230072969 + 3 ^ 40 * 1260844 * 2
def baseEnd_1260844 : Nat := 287741778816697855889551

theorem tailTrace_1260844 : CollatzResearch.WordTrace tailWord_1260844 prefixEnd_1260844 287741778816697855889551 := by
  unfold tailWord_1260844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22993379322092498928306793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30657839096123331904409057 22993379322092498928306793)
  ·
    refine ⟨17245034491569374196230095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22993379322092498928306793 17245034491569374196230095)
    ·
      refine ⟨25867551737354061294345143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17245034491569374196230095 25867551737354061294345143)
      ·
        refine ⟨38801327606031091941517715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25867551737354061294345143 38801327606031091941517715)
        ·
          refine ⟨58201991409046637912276573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38801327606031091941517715 58201991409046637912276573)
          ·
            refine ⟨21825746778392489217103715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58201991409046637912276573 21825746778392489217103715)
            ·
              refine ⟨32738620167588733825655573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21825746778392489217103715 32738620167588733825655573)
              ·
                refine ⟨1534622820355721898077605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32738620167588733825655573 1534622820355721898077605)
                ·
                  refine ⟨287741778816697855889551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534622820355721898077605 287741778816697855889551)
                  ·
                    rfl

theorem cell21_1260844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1260844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260844 prefixEnd_1260844 := by exact prefixLift 1260844
  have htrace : WordTrace (prefixWord ++ tailWord_1260844) baseStart_1260844 baseEnd_1260844 := by
    simpa [prefixWord, tailWord_1260844, baseEnd_1260844] using wordTrace_append hprefix tailTrace_1260844
  have hstable : (prefixWord ++ tailWord_1260844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260844).length < 2 ^ (prefixWord ++ tailWord_1260844).sum := by decide
  have hdescent : baseEnd_1260844 < baseStart_1260844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260926 : List Nat := [4, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1260926 : Nat := 118140960795 + 1260926 * 2 ^ 59
def prefixEnd_1260926 : Nat := 4983230072969 + 3 ^ 40 * 1260926 * 2
def baseEnd_1260926 : Nat := 95920164111294645174239

theorem tailTrace_1260926 : CollatzResearch.WordTrace tailWord_1260926 prefixEnd_1260926 95920164111294645174239 := by
  unfold tailWord_1260926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748718678735990732637329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30659832953258617240732421 5748718678735990732637329)
  ·
    refine ⟨4311539009051993049477997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5748718678735990732637329 4311539009051993049477997)
    ·
      refine ⟨1616827128394497393554249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4311539009051993049477997 1616827128394497393554249)
      ·
        refine ⟨1212620346295873045165687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1616827128394497393554249 1212620346295873045165687)
        ·
          refine ⟨1818930519443809567748531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212620346295873045165687 1818930519443809567748531)
          ·
            refine ⟨2728395779165714351622797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818930519443809567748531 2728395779165714351622797)
            ·
              refine ⟨1023148417187142881858549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2728395779165714351622797 1023148417187142881858549)
              ·
                refine ⟨95920164111294645174239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023148417187142881858549 95920164111294645174239)
                ·
                  rfl

theorem cell21_1260926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1260926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260926 prefixEnd_1260926 := by exact prefixLift 1260926
  have htrace : WordTrace (prefixWord ++ tailWord_1260926) baseStart_1260926 baseEnd_1260926 := by
    simpa [prefixWord, tailWord_1260926, baseEnd_1260926] using wordTrace_append hprefix tailTrace_1260926
  have hstable : (prefixWord ++ tailWord_1260926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260926).length < 2 ^ (prefixWord ++ tailWord_1260926).sum := by decide
  have hdescent : baseEnd_1260926 < baseStart_1260926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260985 : List Nat := [1, 2, 1, 4, 5, 1, 2, 5]
def baseStart_1260985 : Nat := 118140960795 + 1260985 * 2 ^ 59
def prefixEnd_1260985 : Nat := 4983230072969 + 3 ^ 40 * 1260985 * 2
def baseEnd_1260985 : Nat := 95924652312570981346421

theorem tailTrace_1260985 : CollatzResearch.WordTrace tailWord_1260985 prefixEnd_1260985 95924652312570981346421 := by
  unfold tailWord_1260985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45991901336674178937496409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30661267557782785958330939 45991901336674178937496409)
  ·
    refine ⟨34493926002505634203122307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45991901336674178937496409 34493926002505634203122307)
    ·
      refine ⟨51740889003758451304683461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34493926002505634203122307 51740889003758451304683461)
      ·
        refine ⟨9701416688204709619628149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51740889003758451304683461 9701416688204709619628149)
        ·
          refine ⟨909507814519191526840139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9701416688204709619628149 909507814519191526840139)
          ·
            refine ⟨1364261721778787290260209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909507814519191526840139 1364261721778787290260209)
            ·
              refine ⟨1023196291334090467695157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364261721778787290260209 1023196291334090467695157)
              ·
                refine ⟨95924652312570981346421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023196291334090467695157 95924652312570981346421)
                ·
                  rfl

theorem cell21_1260985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 5].length) (baseStart_1260985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1260985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1260985 prefixEnd_1260985 := by exact prefixLift 1260985
  have htrace : WordTrace (prefixWord ++ tailWord_1260985) baseStart_1260985 baseEnd_1260985 := by
    simpa [prefixWord, tailWord_1260985, baseEnd_1260985] using wordTrace_append hprefix tailTrace_1260985
  have hstable : (prefixWord ++ tailWord_1260985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260985).length < 2 ^ (prefixWord ++ tailWord_1260985).sum := by decide
  have hdescent : baseEnd_1260985 < baseStart_1260985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261027 : List Nat := [1, 1, 1, 6, 2, 2, 2, 6]
def baseStart_1261027 : Nat := 118140960795 + 1261027 * 2 ^ 59
def prefixEnd_1261027 : Nat := 4983230072969 + 3 ^ 40 * 1261027 * 2
def baseEnd_1261027 : Nat := 95927847303310068113059

theorem tailTrace_1261027 : CollatzResearch.WordTrace tailWord_1261027 prefixEnd_1261027 95927847303310068113059 := by
  unfold tailWord_1261027
  simp only [CollatzResearch.WordTrace]
  refine ⟨45993433202522020110525335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30662288801681346740350223 45993433202522020110525335)
  ·
    refine ⟨68990149803783030165788003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45993433202522020110525335 68990149803783030165788003)
    ·
      refine ⟨103485224705674545248682005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68990149803783030165788003 103485224705674545248682005)
      ·
        refine ⟨4850869908078494308531969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103485224705674545248682005 4850869908078494308531969)
        ·
          refine ⟨3638152431058870731398977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850869908078494308531969 3638152431058870731398977)
          ·
            refine ⟨2728614323294153048549233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3638152431058870731398977 2728614323294153048549233)
            ·
              refine ⟨2046460742470614786411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728614323294153048549233 2046460742470614786411925)
              ·
                refine ⟨95927847303310068113059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2046460742470614786411925 95927847303310068113059)
                ·
                  rfl

theorem cell21_1261027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_1261027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261027 prefixEnd_1261027 := by exact prefixLift 1261027
  have htrace : WordTrace (prefixWord ++ tailWord_1261027) baseStart_1261027 baseEnd_1261027 := by
    simpa [prefixWord, tailWord_1261027, baseEnd_1261027] using wordTrace_append hprefix tailTrace_1261027
  have hstable : (prefixWord ++ tailWord_1261027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261027).length < 2 ^ (prefixWord ++ tailWord_1261027).sum := by decide
  have hdescent : baseEnd_1261027 < baseStart_1261027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261055 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_1261055 : Nat := 118140960795 + 1261055 * 2 ^ 59
def prefixEnd_1261055 : Nat := 4983230072969 + 3 ^ 40 * 1261055 * 2
def baseEnd_1261055 : Nat := 287789931891408377872453

theorem tailTrace_1261055 : CollatzResearch.WordTrace tailWord_1261055 prefixEnd_1261055 287789931891408377872453 := by
  unfold tailWord_1261055
  simp only [CollatzResearch.WordTrace]
  refine ⟨45994454446420580892544619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30662969630947053928363079 45994454446420580892544619)
  ·
    refine ⟨68991681669630871338816929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45994454446420580892544619 68991681669630871338816929)
    ·
      refine ⟨51743761252223153504112697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68991681669630871338816929 51743761252223153504112697)
      ·
        refine ⟨38807820939167365128084523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51743761252223153504112697 38807820939167365128084523)
        ·
          refine ⟨58211731408751047692126785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38807820939167365128084523 58211731408751047692126785)
          ·
            refine ⟨43658798556563285769095089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58211731408751047692126785 43658798556563285769095089)
            ·
              refine ⟨32744098917422464326821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43658798556563285769095089 32744098917422464326821317)
              ·
                refine ⟨6139518547016712061278997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32744098917422464326821317 6139518547016712061278997)
                ·
                  refine ⟨287789931891408377872453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6139518547016712061278997 287789931891408377872453)
                  ·
                    rfl

theorem cell21_1261055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_1261055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261055 prefixEnd_1261055 := by exact prefixLift 1261055
  have htrace : WordTrace (prefixWord ++ tailWord_1261055) baseStart_1261055 baseEnd_1261055 := by
    simpa [prefixWord, tailWord_1261055, baseEnd_1261055] using wordTrace_append hprefix tailTrace_1261055
  have hstable : (prefixWord ++ tailWord_1261055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261055).length < 2 ^ (prefixWord ++ tailWord_1261055).sum := by decide
  have hdescent : baseEnd_1261055 < baseStart_1261055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261075 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 3]
def baseStart_1261075 : Nat := 118140960795 + 1261075 * 2 ^ 59
def prefixEnd_1261075 : Nat := 4983230072969 + 3 ^ 40 * 1261075 * 2
def baseEnd_1261075 : Nat := 287794496163892787539079

theorem tailTrace_1261075 : CollatzResearch.WordTrace tailWord_1261075 prefixEnd_1261075 287794496163892787539079 := by
  unfold tailWord_1261075
  simp only [CollatzResearch.WordTrace]
  refine ⟨45995183906348124308272679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30663455937565416205515119 45995183906348124308272679)
  ·
    refine ⟨68992775859522186462409019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45995183906348124308272679 68992775859522186462409019)
    ·
      refine ⟨103489163789283279693613529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68992775859522186462409019 103489163789283279693613529)
      ·
        refine ⟨77616872841962459770210147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103489163789283279693613529 77616872841962459770210147)
        ·
          refine ⟨116425309262943689655315221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77616872841962459770210147 116425309262943689655315221)
          ·
            refine ⟨5457436371700485452592901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116425309262943689655315221 5457436371700485452592901)
            ·
              refine ⟨1023269319693841022361169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5457436371700485452592901 1023269319693841022361169)
              ·
                refine ⟨767451989770380766770877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023269319693841022361169 767451989770380766770877)
                ·
                  refine ⟨287794496163892787539079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767451989770380766770877 287794496163892787539079)
                  ·
                    rfl

theorem cell21_1261075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 3].length) (baseStart_1261075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261075 prefixEnd_1261075 := by exact prefixLift 1261075
  have htrace : WordTrace (prefixWord ++ tailWord_1261075) baseStart_1261075 baseEnd_1261075 := by
    simpa [prefixWord, tailWord_1261075, baseEnd_1261075] using wordTrace_append hprefix tailTrace_1261075
  have hstable : (prefixWord ++ tailWord_1261075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261075).length < 2 ^ (prefixWord ++ tailWord_1261075).sum := by decide
  have hdescent : baseEnd_1261075 < baseStart_1261075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261193 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_1261193 : Nat := 118140960795 + 1261193 * 2 ^ 59
def prefixEnd_1261193 : Nat := 4983230072969 + 3 ^ 40 * 1261193 * 2
def baseEnd_1261193 : Nat := 287821425371550804572171

theorem tailTrace_1261193 : CollatzResearch.WordTrace tailWord_1261193 prefixEnd_1261193 287821425371550804572171 := by
  unfold tailWord_1261193
  simp only [CollatzResearch.WordTrace]
  refine ⟨45999487719920630461068233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30666325146613753640712155 45999487719920630461068233)
  ·
    refine ⟨34499615789940472845801175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45999487719920630461068233 34499615789940472845801175)
    ·
      refine ⟨51749423684910709268701763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34499615789940472845801175 51749423684910709268701763)
      ·
        refine ⟨77624135527366063903052645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51749423684910709268701763 77624135527366063903052645)
        ·
          refine ⟨14554525411381136981822371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77624135527366063903052645 14554525411381136981822371)
          ·
            refine ⟨21831788117071705472733557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554525411381136981822371 21831788117071705472733557)
            ·
              refine ⟨2046730135975472388068771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21831788117071705472733557 2046730135975472388068771)
              ·
                refine ⟨3070095203963208582103157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046730135975472388068771 3070095203963208582103157)
                ·
                  refine ⟨287821425371550804572171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070095203963208582103157 287821425371550804572171)
                  ·
                    rfl

theorem cell21_1261193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_1261193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261193 prefixEnd_1261193 := by exact prefixLift 1261193
  have htrace : WordTrace (prefixWord ++ tailWord_1261193) baseStart_1261193 baseEnd_1261193 := by
    simpa [prefixWord, tailWord_1261193, baseEnd_1261193] using wordTrace_append hprefix tailTrace_1261193
  have hstable : (prefixWord ++ tailWord_1261193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261193).length < 2 ^ (prefixWord ++ tailWord_1261193).sum := by decide
  have hdescent : baseEnd_1261193 < baseStart_1261193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261244 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_1261244 : Nat := 118140960795 + 1261244 * 2 ^ 59
def prefixEnd_1261244 : Nat := 4983230072969 + 3 ^ 40 * 1261244 * 2
def baseEnd_1261244 : Nat := 287833064266386049222067

theorem tailTrace_1261244 : CollatzResearch.WordTrace tailWord_1261244 prefixEnd_1261244 287833064266386049222067 := by
  unfold tailWord_1261244
  simp only [CollatzResearch.WordTrace]
  refine ⟨23000673921367933085587393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30667565228490577447449857 23000673921367933085587393)
  ·
    refine ⟨17250505441025949814190545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23000673921367933085587393 17250505441025949814190545)
    ·
      refine ⟨12937879080769462360642909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17250505441025949814190545 12937879080769462360642909)
      ·
        refine ⟨4851704655288548385241091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12937879080769462360642909 4851704655288548385241091)
        ·
          refine ⟨7277556982932822577861637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851704655288548385241091 7277556982932822577861637)
          ·
            refine ⟨1364541934299904233349057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7277556982932822577861637 1364541934299904233349057)
            ·
              refine ⟨1023406450724928175011793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364541934299904233349057 1023406450724928175011793)
              ·
                refine ⟨767554838043696131258845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023406450724928175011793 767554838043696131258845)
                ·
                  refine ⟨287833064266386049222067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767554838043696131258845 287833064266386049222067)
                  ·
                    rfl

theorem cell21_1261244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_1261244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261244 prefixEnd_1261244 := by exact prefixLift 1261244
  have htrace : WordTrace (prefixWord ++ tailWord_1261244) baseStart_1261244 baseEnd_1261244 := by
    simpa [prefixWord, tailWord_1261244, baseEnd_1261244] using wordTrace_append hprefix tailTrace_1261244
  have hstable : (prefixWord ++ tailWord_1261244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261244).length < 2 ^ (prefixWord ++ tailWord_1261244).sum := by decide
  have hdescent : baseEnd_1261244 < baseStart_1261244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261362 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1261362 : Nat := 118140960795 + 1261362 * 2 ^ 59
def prefixEnd_1261362 : Nat := 4983230072969 + 3 ^ 40 * 1261362 * 2
def baseEnd_1261362 : Nat := 287859993474044066255159

theorem tailTrace_1261362 : CollatzResearch.WordTrace tailWord_1261362 prefixEnd_1261362 287859993474044066255159 := by
  unfold tailWord_1261362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501412914077093080992585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30670434437538914882646893 11501412914077093080992585)
  ·
    refine ⟨8626059685557819810744439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11501412914077093080992585 8626059685557819810744439)
    ·
      refine ⟨12939089528336729716116659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8626059685557819810744439 12939089528336729716116659)
      ·
        refine ⟨19408634292505094574174989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12939089528336729716116659 19408634292505094574174989)
        ·
          refine ⟨7278237859689410465315621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19408634292505094574174989 7278237859689410465315621)
          ·
            refine ⟨1364669598691764462246679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7278237859689410465315621 1364669598691764462246679)
            ·
              refine ⟨2047004398037646693370019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364669598691764462246679 2047004398037646693370019)
              ·
                refine ⟨3070506597056470040055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047004398037646693370019 3070506597056470040055029)
                ·
                  refine ⟨287859993474044066255159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070506597056470040055029 287859993474044066255159)
                  ·
                    rfl

theorem cell21_1261362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1261362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261362 prefixEnd_1261362 := by exact prefixLift 1261362
  have htrace : WordTrace (prefixWord ++ tailWord_1261362) baseStart_1261362 baseEnd_1261362 := by
    simpa [prefixWord, tailWord_1261362, baseEnd_1261362] using wordTrace_append hprefix tailTrace_1261362
  have hstable : (prefixWord ++ tailWord_1261362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261362).length < 2 ^ (prefixWord ++ tailWord_1261362).sum := by decide
  have hdescent : baseEnd_1261362 < baseStart_1261362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261438 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1261438 : Nat := 118140960795 + 1261438 * 2 ^ 59
def prefixEnd_1261438 : Nat := 4983230072969 + 3 ^ 40 * 1261438 * 2
def baseEnd_1261438 : Nat := 287877337709484822988337

theorem tailTrace_1261438 : CollatzResearch.WordTrace tailWord_1261438 prefixEnd_1261438 287877337709484822988337 := by
  unfold tailWord_1261438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751052950504129662967121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30672282402688691535824645 5751052950504129662967121)
  ·
    refine ⟨4313289712878097247225341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5751052950504129662967121 4313289712878097247225341)
    ·
      refine ⟨1617483642329286467709503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4313289712878097247225341 1617483642329286467709503)
      ·
        refine ⟨2426225463493929701564255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617483642329286467709503 2426225463493929701564255)
        ·
          refine ⟨3639338195240894552346383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426225463493929701564255 3639338195240894552346383)
          ·
            refine ⟨5459007292861341828519575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639338195240894552346383 5459007292861341828519575)
            ·
              refine ⟨8188510939292012742779363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459007292861341828519575 8188510939292012742779363)
              ·
                refine ⟨12282766408938019114169045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188510939292012742779363 12282766408938019114169045)
                ·
                  refine ⟨287877337709484822988337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12282766408938019114169045 287877337709484822988337)
                  ·
                    rfl

theorem cell21_1261438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1261438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261438 prefixEnd_1261438 := by exact prefixLift 1261438
  have htrace : WordTrace (prefixWord ++ tailWord_1261438) baseStart_1261438 baseEnd_1261438 := by
    simpa [prefixWord, tailWord_1261438, baseEnd_1261438] using wordTrace_append hprefix tailTrace_1261438
  have hstable : (prefixWord ++ tailWord_1261438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261438).length < 2 ^ (prefixWord ++ tailWord_1261438).sum := by decide
  have hdescent : baseEnd_1261438 < baseStart_1261438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261466 : List Nat := [3, 1, 1, 4, 2, 2, 8]
def baseStart_1261466 : Nat := 118140960795 + 1261466 * 2 ^ 59
def prefixEnd_1261466 : Nat := 4983230072969 + 3 ^ 40 * 1261466 * 2
def baseEnd_1261466 : Nat := 31987080854551444057957

theorem tailTrace_1261466 : CollatzResearch.WordTrace tailWord_1261466 prefixEnd_1261466 31987080854551444057957 := by
  unfold tailWord_1261466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502361211982899521439063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30672963231954398723837501 11502361211982899521439063)
  ·
    refine ⟨17253541817974349282158595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11502361211982899521439063 17253541817974349282158595)
    ·
      refine ⟨25880312726961523923237893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17253541817974349282158595 25880312726961523923237893)
      ·
        refine ⟨4852558636305285735607105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25880312726961523923237893 4852558636305285735607105)
        ·
          refine ⟨3639418977228964301705329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852558636305285735607105 3639418977228964301705329)
          ·
            refine ⟨2729564232921723226278997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3639418977228964301705329 2729564232921723226278997)
            ·
              refine ⟨31987080854551444057957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2729564232921723226278997 31987080854551444057957)
              ·
                rfl

theorem cell21_1261466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 8].length) (baseStart_1261466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261466 prefixEnd_1261466 := by exact prefixLift 1261466
  have htrace : WordTrace (prefixWord ++ tailWord_1261466) baseStart_1261466 baseEnd_1261466 := by
    simpa [prefixWord, tailWord_1261466, baseEnd_1261466] using wordTrace_append hprefix tailTrace_1261466
  have hstable : (prefixWord ++ tailWord_1261466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261466).length < 2 ^ (prefixWord ++ tailWord_1261466).sum := by decide
  have hdescent : baseEnd_1261466 < baseStart_1261466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261469 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1261469 : Nat := 118140960795 + 1261469 * 2 ^ 59
def prefixEnd_1261469 : Nat := 4983230072969 + 3 ^ 40 * 1261469 * 2
def baseEnd_1261469 : Nat := 287884412331835657971607

theorem tailTrace_1261469 : CollatzResearch.WordTrace tailWord_1261469 prefixEnd_1261469 287884412331835657971607 := by
  unfold tailWord_1261469
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009554266920729598115461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30673036177947153065410307 46009554266920729598115461)
  ·
    refine ⟨8626791425047636799646649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46009554266920729598115461 8626791425047636799646649)
    ·
      refine ⟨6470093568785727599734987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8626791425047636799646649 6470093568785727599734987)
      ·
        refine ⟨9705140353178591399602481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6470093568785727599734987 9705140353178591399602481)
        ·
          refine ⟨7278855264883943549701861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9705140353178591399602481 7278855264883943549701861)
          ·
            refine ⟨1364785362165739415569099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7278855264883943549701861 1364785362165739415569099)
            ·
              refine ⟨2047178043248609123353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364785362165739415569099 2047178043248609123353649)
              ·
                refine ⟨1535383532436456842515237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047178043248609123353649 1535383532436456842515237)
                ·
                  refine ⟨287884412331835657971607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535383532436456842515237 287884412331835657971607)
                  ·
                    rfl

theorem cell21_1261469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1261469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261469 prefixEnd_1261469 := by exact prefixLift 1261469
  have htrace : WordTrace (prefixWord ++ tailWord_1261469) baseStart_1261469 baseEnd_1261469 := by
    simpa [prefixWord, tailWord_1261469, baseEnd_1261469] using wordTrace_append hprefix tailTrace_1261469
  have hstable : (prefixWord ++ tailWord_1261469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261469).length < 2 ^ (prefixWord ++ tailWord_1261469).sum := by decide
  have hdescent : baseEnd_1261469 < baseStart_1261469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261514 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_1261514 : Nat := 118140960795 + 1261514 * 2 ^ 59
def prefixEnd_1261514 : Nat := 4983230072969 + 3 ^ 40 * 1261514 * 2
def baseEnd_1261514 : Nat := 287894681944925579721515

theorem tailTrace_1261514 : CollatzResearch.WordTrace tailWord_1261514 prefixEnd_1261514 287894681944925579721515 := by
  unfold tailWord_1261514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502798887939425570875899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30674130367838468189002397 11502798887939425570875899)
  ·
    refine ⟨17254198331909138356313849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11502798887939425570875899 17254198331909138356313849)
    ·
      refine ⟨12940648748931853767235387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17254198331909138356313849 12940648748931853767235387)
      ·
        refine ⟨19410973123397780650853081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940648748931853767235387 19410973123397780650853081)
        ·
          refine ⟨14558229842548335488139811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19410973123397780650853081 14558229842548335488139811)
          ·
            refine ⟨21837344763822503232209717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14558229842548335488139811 21837344763822503232209717)
            ·
              refine ⟨2047251071608359678019661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21837344763822503232209717 2047251071608359678019661)
              ·
                refine ⟨767719151853134879257373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2047251071608359678019661 767719151853134879257373)
                ·
                  refine ⟨287894681944925579721515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767719151853134879257373 287894681944925579721515)
                  ·
                    rfl

theorem cell21_1261514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_1261514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261514 prefixEnd_1261514 := by exact prefixLift 1261514
  have htrace : WordTrace (prefixWord ++ tailWord_1261514) baseStart_1261514 baseEnd_1261514 := by
    simpa [prefixWord, tailWord_1261514, baseEnd_1261514] using wordTrace_append hprefix tailTrace_1261514
  have hstable : (prefixWord ++ tailWord_1261514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261514).length < 2 ^ (prefixWord ++ tailWord_1261514).sum := by decide
  have hdescent : baseEnd_1261514 < baseStart_1261514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261587 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_1261587 : Nat := 118140960795 + 1261587 * 2 ^ 59
def prefixEnd_1261587 : Nat := 4983230072969 + 3 ^ 40 * 1261587 * 2
def baseEnd_1261587 : Nat := 287911341539493675004699

theorem tailTrace_1261587 : CollatzResearch.WordTrace tailWord_1261587 prefixEnd_1261587 287911341539493675004699 := by
  unfold tailWord_1261587
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013858080493235750911015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30675905386995490500607343 46013858080493235750911015)
  ·
    refine ⟨69020787120739853626366523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46013858080493235750911015 69020787120739853626366523)
    ·
      refine ⟨103531180681109780439549785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69020787120739853626366523 103531180681109780439549785)
      ·
        refine ⟨77648385510832335329662339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103531180681109780439549785 77648385510832335329662339)
        ·
          refine ⟨116472578266248502994493509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77648385510832335329662339 116472578266248502994493509)
          ·
            refine ⟨21838608424921594311467533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116472578266248502994493509 21838608424921594311467533)
            ·
              refine ⟨8189478159345597866800325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21838608424921594311467533 8189478159345597866800325)
              ·
                refine ⟨1535527154877299600025061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8189478159345597866800325 1535527154877299600025061)
                ·
                  refine ⟨287911341539493675004699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535527154877299600025061 287911341539493675004699)
                  ·
                    rfl

theorem cell21_1261587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_1261587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261587 prefixEnd_1261587 := by exact prefixLift 1261587
  have htrace : WordTrace (prefixWord ++ tailWord_1261587) baseStart_1261587 baseEnd_1261587 := by
    simpa [prefixWord, tailWord_1261587, baseEnd_1261587] using wordTrace_append hprefix tailTrace_1261587
  have hstable : (prefixWord ++ tailWord_1261587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261587).length < 2 ^ (prefixWord ++ tailWord_1261587).sum := by decide
  have hdescent : baseEnd_1261587 < baseStart_1261587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261784 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_1261784 : Nat := 118140960795 + 1261784 * 2 ^ 59
def prefixEnd_1261784 : Nat := 4983230072969 + 3 ^ 40 * 1261784 * 2
def baseEnd_1261784 : Nat := 287956299623465110220963

theorem tailTrace_1261784 : CollatzResearch.WordTrace tailWord_1261784 prefixEnd_1261784 287956299623465110220963 := by
  unfold tailWord_1261784
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010521630389769197916203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30680695507186358930554937 23010521630389769197916203)
  ·
    refine ⟨34515782445584653796874305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23010521630389769197916203 34515782445584653796874305)
    ·
      refine ⟨25886836834188490347655729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34515782445584653796874305 25886836834188490347655729)
      ·
        refine ⟨19415127625641367760741797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25886836834188490347655729 19415127625641367760741797)
        ·
          refine ⟨3640336429807756455139087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19415127625641367760741797 3640336429807756455139087)
          ·
            refine ⟨5460504644711634682708631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640336429807756455139087 5460504644711634682708631)
            ·
              refine ⟨8190756967067452024062947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460504644711634682708631 8190756967067452024062947)
              ·
                refine ⟨12286135450601178036094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190756967067452024062947 12286135450601178036094421)
                ·
                  refine ⟨287956299623465110220963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12286135450601178036094421 287956299623465110220963)
                  ·
                    rfl

theorem cell21_1261784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_1261784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261784 prefixEnd_1261784 := by exact prefixLift 1261784
  have htrace : WordTrace (prefixWord ++ tailWord_1261784) baseStart_1261784 baseEnd_1261784 := by
    simpa [prefixWord, tailWord_1261784, baseEnd_1261784] using wordTrace_append hprefix tailTrace_1261784
  have hstable : (prefixWord ++ tailWord_1261784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261784).length < 2 ^ (prefixWord ++ tailWord_1261784).sum := by decide
  have hdescent : baseEnd_1261784 < baseStart_1261784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261905 : List Nat := [1, 2, 2, 1, 4, 2, 2, 7]
def baseStart_1261905 : Nat := 118140960795 + 1261905 * 2 ^ 59
def prefixEnd_1261905 : Nat := 4983230072969 + 3 ^ 40 * 1261905 * 2
def baseEnd_1261905 : Nat := 95994637823998596234683

theorem tailTrace_1261905 : CollatzResearch.WordTrace tailWord_1261905 prefixEnd_1261905 95994637823998596234683 := by
  unfold tailWord_1261905
  simp only [CollatzResearch.WordTrace]
  refine ⟨46025456493341176060987169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30683637662227450707324779 46025456493341176060987169)
  ·
    refine ⟨34519092370005882045740377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46025456493341176060987169 34519092370005882045740377)
    ·
      refine ⟨25889319277504411534305283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34519092370005882045740377 25889319277504411534305283)
      ·
        refine ⟨38833978916256617301457925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25889319277504411534305283 38833978916256617301457925)
        ·
          refine ⟨7281371046798115744023361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38833978916256617301457925 7281371046798115744023361)
          ·
            refine ⟨5461028285098586808017521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7281371046798115744023361 5461028285098586808017521)
            ·
              refine ⟨4095771213823940106013141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5461028285098586808017521 4095771213823940106013141)
              ·
                refine ⟨95994637823998596234683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4095771213823940106013141 95994637823998596234683)
                ·
                  rfl

theorem cell21_1261905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_1261905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261905 prefixEnd_1261905 := by exact prefixLift 1261905
  have htrace : WordTrace (prefixWord ++ tailWord_1261905) baseStart_1261905 baseEnd_1261905 := by
    simpa [prefixWord, tailWord_1261905, baseEnd_1261905] using wordTrace_append hprefix tailTrace_1261905
  have hstable : (prefixWord ++ tailWord_1261905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261905).length < 2 ^ (prefixWord ++ tailWord_1261905).sum := by decide
  have hdescent : baseEnd_1261905 < baseStart_1261905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261953 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1261953 : Nat := 118140960795 + 1261953 * 2 ^ 59
def prefixEnd_1261953 : Nat := 4983230072969 + 3 ^ 40 * 1261953 * 2
def baseEnd_1261953 : Nat := 287994867725958371903951

theorem tailTrace_1261953 : CollatzResearch.WordTrace tailWord_1261953 prefixEnd_1261953 287994867725958371903951 := by
  unfold tailWord_1261953
  simp only [CollatzResearch.WordTrace]
  refine ⟨46027207197167280258734513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30684804798111520172489675 46027207197167280258734513)
  ·
    refine ⟨34520405397875460194050885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46027207197167280258734513 34520405397875460194050885)
    ·
      refine ⟨6472576012101648786384541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34520405397875460194050885 6472576012101648786384541)
      ·
        refine ⟨2427216004538118294894203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6472576012101648786384541 2427216004538118294894203)
        ·
          refine ⟨3640824006807177442341305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427216004538118294894203 3640824006807177442341305)
          ·
            refine ⟨2730618005105383081755979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640824006807177442341305 2730618005105383081755979)
            ·
              refine ⟨4095927007658074622633969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730618005105383081755979 4095927007658074622633969)
              ·
                refine ⟨3071945255743555966975477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095927007658074622633969 3071945255743555966975477)
                ·
                  refine ⟨287994867725958371903951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3071945255743555966975477 287994867725958371903951)
                  ·
                    rfl

theorem cell21_1261953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1261953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261953 prefixEnd_1261953 := by exact prefixLift 1261953
  have htrace : WordTrace (prefixWord ++ tailWord_1261953) baseStart_1261953 baseEnd_1261953 := by
    simpa [prefixWord, tailWord_1261953, baseEnd_1261953] using wordTrace_append hprefix tailTrace_1261953
  have hstable : (prefixWord ++ tailWord_1261953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261953).length < 2 ^ (prefixWord ++ tailWord_1261953).sum := by decide
  have hdescent : baseEnd_1261953 < baseStart_1261953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261984 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_1261984 : Nat := 118140960795 + 1261984 * 2 ^ 59
def prefixEnd_1261984 : Nat := 4983230072969 + 3 ^ 40 * 1261984 * 2
def baseEnd_1261984 : Nat := 288001942348309206887221

theorem tailTrace_1261984 : CollatzResearch.WordTrace tailWord_1261984 prefixEnd_1261984 288001942348309206887221 := by
  unfold tailWord_1261984
  simp only [CollatzResearch.WordTrace]
  refine ⟨23014168930027486276556503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30685558573369981702075337 23014168930027486276556503)
  ·
    refine ⟨34521253395041229414834755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23014168930027486276556503 34521253395041229414834755)
    ·
      refine ⟨51781880092561844122252133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34521253395041229414834755 51781880092561844122252133)
      ·
        refine ⟨9709102517355345772922275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51781880092561844122252133 9709102517355345772922275)
        ·
          refine ⟨14563653776033018659383413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709102517355345772922275 14563653776033018659383413)
          ·
            refine ⟨1365342541503095499317195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14563653776033018659383413 1365342541503095499317195)
            ·
              refine ⟨2048013812254643248975793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365342541503095499317195 2048013812254643248975793)
              ·
                refine ⟨1536010359190982436731845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048013812254643248975793 1536010359190982436731845)
                ·
                  refine ⟨288001942348309206887221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536010359190982436731845 288001942348309206887221)
                  ·
                    rfl

theorem cell21_1261984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_1261984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1261984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1261984 prefixEnd_1261984 := by exact prefixLift 1261984
  have htrace : WordTrace (prefixWord ++ tailWord_1261984) baseStart_1261984 baseEnd_1261984 := by
    simpa [prefixWord, tailWord_1261984, baseEnd_1261984] using wordTrace_append hprefix tailTrace_1261984
  have hstable : (prefixWord ++ tailWord_1261984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261984).length < 2 ^ (prefixWord ++ tailWord_1261984).sum := by decide
  have hdescent : baseEnd_1261984 < baseStart_1261984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262026 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1262026 : Nat := 118140960795 + 1262026 * 2 ^ 59
def prefixEnd_1262026 : Nat := 4983230072969 + 3 ^ 40 * 1262026 * 2
def baseEnd_1262026 : Nat := 288011527320526467187135

theorem tailTrace_1262026 : CollatzResearch.WordTrace tailWord_1262026 prefixEnd_1262026 288011527320526467187135 := by
  unfold tailWord_1262026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507467431475703431535483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30686579817268542484094621 11507467431475703431535483)
  ·
    refine ⟨17261201147213555147303225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11507467431475703431535483 17261201147213555147303225)
    ·
      refine ⟨12945900860410166360477419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17261201147213555147303225 12945900860410166360477419)
      ·
        refine ⟨19418851290615249540716129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12945900860410166360477419 19418851290615249540716129)
        ·
          refine ⟨14564138467961437155537097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19418851290615249540716129 14564138467961437155537097)
          ·
            refine ⟨10923103850971077866652823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14564138467961437155537097 10923103850971077866652823)
            ·
              refine ⟨16384655776456616799979235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10923103850971077866652823 16384655776456616799979235)
              ·
                refine ⟨24576983664684925199968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16384655776456616799979235 24576983664684925199968853)
                ·
                  refine ⟨288011527320526467187135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24576983664684925199968853 288011527320526467187135)
                  ·
                    rfl

theorem cell21_1262026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1262026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262026 prefixEnd_1262026 := by exact prefixLift 1262026
  have htrace : WordTrace (prefixWord ++ tailWord_1262026) baseStart_1262026 baseEnd_1262026 := by
    simpa [prefixWord, tailWord_1262026, baseEnd_1262026] using wordTrace_append hprefix tailTrace_1262026
  have hstable : (prefixWord ++ tailWord_1262026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262026).length < 2 ^ (prefixWord ++ tailWord_1262026).sum := by decide
  have hdescent : baseEnd_1262026 < baseStart_1262026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262125 : List Nat := [1, 5, 4, 1, 1, 1, 3, 5]
def baseStart_1262125 : Nat := 118140960795 + 1262125 * 2 ^ 59
def prefixEnd_1262125 : Nat := 4983230072969 + 3 ^ 40 * 1262125 * 2
def baseEnd_1262125 : Nat := 96011373489774765012311

theorem tailTrace_1262125 : CollatzResearch.WordTrace tailWord_1262125 prefixEnd_1262125 96011373489774765012311 := by
  unfold tailWord_1262125
  simp only [CollatzResearch.WordTrace]
  refine ⟨46033480552544153633995829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30688987035029435755997219 46033480552544153633995829)
  ·
    refine ⟨4315638801801014403187109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46033480552544153633995829 4315638801801014403187109)
    ·
      refine ⟨809182275337690200597583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4315638801801014403187109 809182275337690200597583)
      ·
        refine ⟨1213773413006535300896375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809182275337690200597583 1213773413006535300896375)
        ·
          refine ⟨1820660119509802951344563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213773413006535300896375 1820660119509802951344563)
          ·
            refine ⟨2730990179264704427016845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820660119509802951344563 2730990179264704427016845)
            ·
              refine ⟨1024121317224264160131317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2730990179264704427016845 1024121317224264160131317)
              ·
                refine ⟨96011373489774765012311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024121317224264160131317 96011373489774765012311)
                ·
                  rfl

theorem cell21_1262125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].length) (baseStart_1262125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262125 prefixEnd_1262125 := by exact prefixLift 1262125
  have htrace : WordTrace (prefixWord ++ tailWord_1262125) baseStart_1262125 baseEnd_1262125 := by
    simpa [prefixWord, tailWord_1262125, baseEnd_1262125] using wordTrace_append hprefix tailTrace_1262125
  have hstable : (prefixWord ++ tailWord_1262125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262125).length < 2 ^ (prefixWord ++ tailWord_1262125).sum := by decide
  have hdescent : baseEnd_1262125 < baseStart_1262125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262164 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1262164 : Nat := 118140960795 + 1262164 * 2 ^ 59
def prefixEnd_1262164 : Nat := 4983230072969 + 3 ^ 40 * 1262164 * 2
def baseEnd_1262164 : Nat := 288043020800668893886853

theorem tailTrace_1262164 : CollatzResearch.WordTrace tailWord_1262164 prefixEnd_1262164 288043020800668893886853 := by
  unfold tailWord_1262164
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017451499701431647332773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30689935332935242196443697 23017451499701431647332773)
  ·
    refine ⟨4315772156194018433874895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23017451499701431647332773 4315772156194018433874895)
    ·
      refine ⟨6473658234291027650812343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315772156194018433874895 6473658234291027650812343)
      ·
        refine ⟨9710487351436541476218515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6473658234291027650812343 9710487351436541476218515)
        ·
          refine ⟨14565731027154812214327773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710487351436541476218515 14565731027154812214327773)
          ·
            refine ⟨5462149135183054580372915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14565731027154812214327773 5462149135183054580372915)
            ·
              refine ⟨8193223702774581870559373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462149135183054580372915 8193223702774581870559373)
              ·
                refine ⟨3072458888540468201459765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8193223702774581870559373 3072458888540468201459765)
                ·
                  refine ⟨288043020800668893886853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3072458888540468201459765 288043020800668893886853)
                  ·
                    rfl

theorem cell21_1262164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1262164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1262164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1262164 prefixEnd_1262164 := by exact prefixLift 1262164
  have htrace : WordTrace (prefixWord ++ tailWord_1262164) baseStart_1262164 baseEnd_1262164 := by
    simpa [prefixWord, tailWord_1262164, baseEnd_1262164] using wordTrace_append hprefix tailTrace_1262164
  have hstable : (prefixWord ++ tailWord_1262164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262164).length < 2 ^ (prefixWord ++ tailWord_1262164).sum := by decide
  have hdescent : baseEnd_1262164 < baseStart_1262164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
