import V185TrunkScan22Chunk399

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3567820 : List Nat := [2, 2, 1, 6, 1, 1, 1, 8]
def baseStart_3567820 : Nat := 118140960795 + 3567820 * 2 ^ 59
def prefixEnd_3567820 : Nat := 4983230072969 + 3 ^ 40 * 3567820 * 2
def baseEnd_3567820 : Nat := 135704188794395268262363

theorem tailTrace_3567820 : CollatzResearch.WordTrace tailWord_3567820 prefixEnd_3567820 135704188794395268262363 := by
  unfold tailWord_3567820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65064542967202474994730457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86752723956269966659640609 65064542967202474994730457)
  ·
    refine ⟨48798407225401856246047843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65064542967202474994730457 48798407225401856246047843)
    ·
      refine ⟨73197610838102784369071765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48798407225401856246047843 73197610838102784369071765)
      ·
        refine ⟨3431138008036068017300239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73197610838102784369071765 3431138008036068017300239)
        ·
          refine ⟨5146707012054102025950359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431138008036068017300239 5146707012054102025950359)
          ·
            refine ⟨7720060518081153038925539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146707012054102025950359 7720060518081153038925539)
            ·
              refine ⟨11580090777121729558388309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720060518081153038925539 11580090777121729558388309)
              ·
                refine ⟨135704188794395268262363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11580090777121729558388309 135704188794395268262363)
                ·
                  rfl

theorem cell22_3567820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_3567820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567820 prefixEnd_3567820 := by exact prefixLift 3567820
  have htrace : WordTrace (prefixWord ++ tailWord_3567820) baseStart_3567820 baseEnd_3567820 := by
    simpa [prefixWord, tailWord_3567820, baseEnd_3567820] using wordTrace_append hprefix tailTrace_3567820
  have hstable : (prefixWord ++ tailWord_3567820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567820).length < 2 ^ (prefixWord ++ tailWord_3567820).sum := by decide
  have hdescent : baseEnd_3567820 < baseStart_3567820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567848 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_3567848 : Nat := 118140960795 + 3567848 * 2 ^ 59
def prefixEnd_3567848 : Nat := 4983230072969 + 3 ^ 40 * 3567848 * 2
def baseEnd_3567848 : Nat := 407115761373924891553727

theorem tailTrace_3567848 : CollatzResearch.WordTrace tailWord_3567848 prefixEnd_3567848 407115761373924891553727 := by
  unfold tailWord_3567848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65065053589151755385740099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86753404785535673847653465 65065053589151755385740099)
  ·
    refine ⟨97597580383727633078610149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65065053589151755385740099 97597580383727633078610149)
    ·
      refine ⟨18299546321948931202239403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97597580383727633078610149 18299546321948931202239403)
      ·
        refine ⟨27449319482923396803359105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299546321948931202239403 27449319482923396803359105)
        ·
          refine ⟨20586989612192547602519329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27449319482923396803359105 20586989612192547602519329)
          ·
            refine ⟨15440242209144410701889497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20586989612192547602519329 15440242209144410701889497)
            ·
              refine ⟨11580181656858308026417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15440242209144410701889497 11580181656858308026417123)
              ·
                refine ⟨17370272485287462039625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580181656858308026417123 17370272485287462039625685)
                ·
                  refine ⟨407115761373924891553727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17370272485287462039625685 407115761373924891553727)
                  ·
                    rfl

theorem cell22_3567848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_3567848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567848 prefixEnd_3567848 := by exact prefixLift 3567848
  have htrace : WordTrace (prefixWord ++ tailWord_3567848) baseStart_3567848 baseEnd_3567848 := by
    simpa [prefixWord, tailWord_3567848, baseEnd_3567848] using wordTrace_append hprefix tailTrace_3567848
  have hstable : (prefixWord ++ tailWord_3567848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567848).length < 2 ^ (prefixWord ++ tailWord_3567848).sum := by decide
  have hdescent : baseEnd_3567848 < baseStart_3567848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567923 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_3567923 : Nat := 118140960795 + 3567923 * 2 ^ 59
def prefixEnd_3567923 : Nat := 4983230072969 + 3 ^ 40 * 3567923 * 2
def baseEnd_3567923 : Nat := 1221372958154499479035951

theorem tailTrace_3567923 : CollatzResearch.WordTrace tailWord_3567923 prefixEnd_3567923 1221372958154499479035951 := by
  unfold tailWord_3567923
  simp only [CollatzResearch.WordTrace]
  refine ⟨130132842653031798580460423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86755228435354532386973615 130132842653031798580460423)
  ·
    refine ⟨195199263979547697870690635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130132842653031798580460423 195199263979547697870690635)
    ·
      refine ⟨292798895969321546806035953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195199263979547697870690635 292798895969321546806035953)
      ·
        refine ⟨219599171976991160104526965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292798895969321546806035953 219599171976991160104526965)
        ·
          refine ⟨20587422372842921259799403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219599171976991160104526965 20587422372842921259799403)
          ·
            refine ⟨30881133559264381889699105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20587422372842921259799403 30881133559264381889699105)
            ·
              refine ⟨23160850169448286417274329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30881133559264381889699105 23160850169448286417274329)
              ·
                refine ⟨17370637627086214812955747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23160850169448286417274329 17370637627086214812955747)
                ·
                  refine ⟨26055956440629322219433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17370637627086214812955747 26055956440629322219433621)
                  ·
                    refine ⟨1221372958154499479035951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26055956440629322219433621 1221372958154499479035951)
                    ·
                      rfl

theorem cell22_3567923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_3567923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567923 prefixEnd_3567923 := by exact prefixLift 3567923
  have htrace : WordTrace (prefixWord ++ tailWord_3567923) baseStart_3567923 baseEnd_3567923 := by
    simpa [prefixWord, tailWord_3567923, baseEnd_3567923] using wordTrace_append hprefix tailTrace_3567923
  have hstable : (prefixWord ++ tailWord_3567923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567923).length < 2 ^ (prefixWord ++ tailWord_3567923).sum := by decide
  have hdescent : baseEnd_3567923 < baseStart_3567923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3567925 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3567925 : Nat := 118140960795 + 3567925 * 2 ^ 59
def prefixEnd_3567925 : Nat := 4983230072969 + 3 ^ 40 * 3567925 * 2
def baseEnd_3567925 : Nat := 1221373642795372140485945

theorem tailTrace_3567925 : CollatzResearch.WordTrace tailWord_3567925 prefixEnd_3567925 1221373642795372140485945 := by
  unfold tailWord_3567925
  simp only [CollatzResearch.WordTrace]
  refine ⟨130132915599024552922033229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86755277066016368614688819 130132915599024552922033229)
  ·
    refine ⟨48799843349634207345762461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130132915599024552922033229 48799843349634207345762461)
    ·
      refine ⟨18299941256112827754660923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48799843349634207345762461 18299941256112827754660923)
      ·
        refine ⟨27449911884169241631991385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299941256112827754660923 27449911884169241631991385)
        ·
          refine ⟨20587433913126931223993539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27449911884169241631991385 20587433913126931223993539)
          ·
            refine ⟨30881150869690396835990309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20587433913126931223993539 30881150869690396835990309)
            ·
              refine ⟨5790215788066949406748183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30881150869690396835990309 5790215788066949406748183)
              ·
                refine ⟨8685323682100424110122275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790215788066949406748183 8685323682100424110122275)
                ·
                  refine ⟨13027985523150636165183413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8685323682100424110122275 13027985523150636165183413)
                  ·
                    refine ⟨1221373642795372140485945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13027985523150636165183413 1221373642795372140485945)
                    ·
                      rfl

theorem cell22_3567925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3567925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3567925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3567925 prefixEnd_3567925 := by exact prefixLift 3567925
  have htrace : WordTrace (prefixWord ++ tailWord_3567925) baseStart_3567925 baseEnd_3567925 := by
    simpa [prefixWord, tailWord_3567925, baseEnd_3567925] using wordTrace_append hprefix tailTrace_3567925
  have hstable : (prefixWord ++ tailWord_3567925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3567925).length < 2 ^ (prefixWord ++ tailWord_3567925).sum := by decide
  have hdescent : baseEnd_3567925 < baseStart_3567925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3567925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568043 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_3568043 : Nat := 118140960795 + 3568043 * 2 ^ 59
def prefixEnd_3568043 : Nat := 4983230072969 + 3 ^ 40 * 3568043 * 2
def baseEnd_3568043 : Nat := 1221414036606859166035583

theorem tailTrace_3568043 : CollatzResearch.WordTrace tailWord_3568043 prefixEnd_3568043 1221414036606859166035583 := by
  unfold tailWord_3568043
  simp only [CollatzResearch.WordTrace]
  refine ⟨130137219412597059074828783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86758146275064706049885855 130137219412597059074828783)
  ·
    refine ⟨195205829118895588612243175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130137219412597059074828783 195205829118895588612243175)
    ·
      refine ⟨292808743678343382918364763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195205829118895588612243175 292808743678343382918364763)
      ·
        refine ⟨439213115517515074377547145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292808743678343382918364763 439213115517515074377547145)
        ·
          refine ⟨329409836638136305783160359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439213115517515074377547145 329409836638136305783160359)
          ·
            refine ⟨494114754957204458674740539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329409836638136305783160359 494114754957204458674740539)
            ·
              refine ⟨741172132435806688012110809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494114754957204458674740539 741172132435806688012110809)
              ·
                refine ⟨555879099326855016009083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741172132435806688012110809 555879099326855016009083107)
                ·
                  refine ⟨833818648990282524013624661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555879099326855016009083107 833818648990282524013624661)
                  ·
                    refine ⟨1221414036606859166035583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 833818648990282524013624661 1221414036606859166035583)
                    ·
                      rfl

theorem cell22_3568043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_3568043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568043 prefixEnd_3568043 := by exact prefixLift 3568043
  have htrace : WordTrace (prefixWord ++ tailWord_3568043) baseStart_3568043 baseEnd_3568043 := by
    simpa [prefixWord, tailWord_3568043, baseEnd_3568043] using wordTrace_append hprefix tailTrace_3568043
  have hstable : (prefixWord ++ tailWord_3568043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568043).length < 2 ^ (prefixWord ++ tailWord_3568043).sum := by decide
  have hdescent : baseEnd_3568043 < baseStart_3568043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568109 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3568109 : Nat := 118140960795 + 3568109 * 2 ^ 59
def prefixEnd_3568109 : Nat := 4983230072969 + 3 ^ 40 * 3568109 * 2
def baseEnd_3568109 : Nat := 1221436629755656993885381

theorem tailTrace_3568109 : CollatzResearch.WordTrace tailWord_3568109 prefixEnd_3568109 1221436629755656993885381 := by
  unfold tailWord_3568109
  simp only [CollatzResearch.WordTrace]
  refine ⟨130139626630357952346731381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86759751086905301564487587 130139626630357952346731381)
  ·
    refine ⟨12200589996596058032506067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130139626630357952346731381 12200589996596058032506067)
    ·
      refine ⟨18300884994894087048759101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200589996596058032506067 18300884994894087048759101)
      ·
        refine ⟨6862831873085282643284663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18300884994894087048759101 6862831873085282643284663)
        ·
          refine ⟨10294247809627923964926995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6862831873085282643284663 10294247809627923964926995)
          ·
            refine ⟨15441371714441885947390493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10294247809627923964926995 15441371714441885947390493)
            ·
              refine ⟨5790514392915707230271435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15441371714441885947390493 5790514392915707230271435)
              ·
                refine ⟨8685771589373560845407153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790514392915707230271435 8685771589373560845407153)
                ·
                  refine ⟨6514328692030170634055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8685771589373560845407153 6514328692030170634055365)
                  ·
                    refine ⟨1221436629755656993885381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6514328692030170634055365 1221436629755656993885381)
                    ·
                      rfl

theorem cell22_3568109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3568109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568109 prefixEnd_3568109 := by exact prefixLift 3568109
  have htrace : WordTrace (prefixWord ++ tailWord_3568109) baseStart_3568109 baseEnd_3568109 := by
    simpa [prefixWord, tailWord_3568109, baseEnd_3568109] using wordTrace_append hprefix tailTrace_3568109
  have hstable : (prefixWord ++ tailWord_3568109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568109).length < 2 ^ (prefixWord ++ tailWord_3568109).sum := by decide
  have hdescent : baseEnd_3568109 < baseStart_3568109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568139 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 3, 3]
def baseStart_3568139 : Nat := 118140960795 + 3568139 * 2 ^ 59
def prefixEnd_3568139 : Nat := 4983230072969 + 3 ^ 40 * 3568139 * 2
def baseEnd_3568139 : Nat := 1221446899368746915635289

theorem tailTrace_3568139 : CollatzResearch.WordTrace tailWord_3568139 prefixEnd_3568139 1221446899368746915635289 := by
  unfold tailWord_3568139
  simp only [CollatzResearch.WordTrace]
  refine ⟨130140720820249267470323471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86760480546832844980215647 130140720820249267470323471)
  ·
    refine ⟨195211081230373901205485207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130140720820249267470323471 195211081230373901205485207)
    ·
      refine ⟨292816621845560851808227811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195211081230373901205485207 292816621845560851808227811)
      ·
        refine ⟨439224932768341277712341717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292816621845560851808227811 439224932768341277712341717)
        ·
          refine ⟨10294334361757998696383009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 439224932768341277712341717 10294334361757998696383009)
          ·
            refine ⟨7720750771318499022287257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10294334361757998696383009 7720750771318499022287257)
            ·
              refine ⟨5790563078488874266715443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720750771318499022287257 5790563078488874266715443)
              ·
                refine ⟨8685844617733311400073165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790563078488874266715443 8685844617733311400073165)
                ·
                  refine ⟨3257191731649991775027437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8685844617733311400073165 3257191731649991775027437)
                  ·
                    refine ⟨1221446899368746915635289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257191731649991775027437 1221446899368746915635289)
                    ·
                      rfl

theorem cell22_3568139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 3].length) (baseStart_3568139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568139 prefixEnd_3568139 := by exact prefixLift 3568139
  have htrace : WordTrace (prefixWord ++ tailWord_3568139) baseStart_3568139 baseEnd_3568139 := by
    simpa [prefixWord, tailWord_3568139, baseEnd_3568139] using wordTrace_append hprefix tailTrace_3568139
  have hstable : (prefixWord ++ tailWord_3568139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568139).length < 2 ^ (prefixWord ++ tailWord_3568139).sum := by decide
  have hdescent : baseEnd_3568139 < baseStart_3568139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568190 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3568190 : Nat := 118140960795 + 3568190 * 2 ^ 59
def prefixEnd_3568190 : Nat := 4983230072969 + 3 ^ 40 * 3568190 * 2
def baseEnd_3568190 : Nat := 1221464357710999782610133

theorem tailTrace_3568190 : CollatzResearch.WordTrace tailWord_3568190 prefixEnd_3568190 1221464357710999782610133 := by
  unfold tailWord_3568190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267822617883062897553753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86761720628709668786953349 16267822617883062897553753)
  ·
    refine ⟨12200866963412297173165315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16267822617883062897553753 12200866963412297173165315)
    ·
      refine ⟨18301300445118445759747973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200866963412297173165315 18301300445118445759747973)
      ·
        refine ⟨3431493833459708579952745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18301300445118445759747973 3431493833459708579952745)
        ·
          refine ⟨2573620375094781434964559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431493833459708579952745 2573620375094781434964559)
          ·
            refine ⟨3860430562642172152446839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573620375094781434964559 3860430562642172152446839)
            ·
              refine ⟨5790645843963258228670259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860430562642172152446839 5790645843963258228670259)
              ·
                refine ⟨8685968765944887343005389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790645843963258228670259 8685968765944887343005389)
                ·
                  refine ⟨3257238287229332753627021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8685968765944887343005389 3257238287229332753627021)
                  ·
                    refine ⟨1221464357710999782610133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257238287229332753627021 1221464357710999782610133)
                    ·
                      rfl

theorem cell22_3568190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3568190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568190 prefixEnd_3568190 := by exact prefixLift 3568190
  have htrace : WordTrace (prefixWord ++ tailWord_3568190) baseStart_3568190 baseEnd_3568190 := by
    simpa [prefixWord, tailWord_3568190, baseEnd_3568190] using wordTrace_append hprefix tailTrace_3568190
  have hstable : (prefixWord ++ tailWord_3568190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568190).length < 2 ^ (prefixWord ++ tailWord_3568190).sum := by decide
  have hdescent : baseEnd_3568190 < baseStart_3568190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568197 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3568197 : Nat := 118140960795 + 3568197 * 2 ^ 59
def prefixEnd_3568197 : Nat := 4983230072969 + 3 ^ 40 * 3568197 * 2
def baseEnd_3568197 : Nat := 407155584651351365895037

theorem tailTrace_3568197 : CollatzResearch.WordTrace tailWord_3568197 prefixEnd_3568197 407155584651351365895037 := by
  unfold tailWord_3568197
  simp only [CollatzResearch.WordTrace]
  refine ⟨130142836254039143375934845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86761890836026095583956563 130142836254039143375934845)
  ·
    refine ⟨48803563595264678765975567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130142836254039143375934845 48803563595264678765975567)
    ·
      refine ⟨73205345392897018148963351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48803563595264678765975567 73205345392897018148963351)
      ·
        refine ⟨109808018089345527223445027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73205345392897018148963351 109808018089345527223445027)
        ·
          refine ⟨164712027134018290835167541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109808018089345527223445027 164712027134018290835167541)
          ·
            refine ⟨15441752543814214765796957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164712027134018290835167541 15441752543814214765796957)
            ·
              refine ⟨5790657203930330537173859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15441752543814214765796957 5790657203930330537173859)
              ·
                refine ⟨8685985805895495805760789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790657203930330537173859 8685985805895495805760789)
                ·
                  refine ⟨407155584651351365895037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8685985805895495805760789 407155584651351365895037)
                  ·
                    rfl

theorem cell22_3568197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3568197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568197 prefixEnd_3568197 := by exact prefixLift 3568197
  have htrace : WordTrace (prefixWord ++ tailWord_3568197) baseStart_3568197 baseEnd_3568197 := by
    simpa [prefixWord, tailWord_3568197, baseEnd_3568197] using wordTrace_append hprefix tailTrace_3568197
  have hstable : (prefixWord ++ tailWord_3568197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568197).length < 2 ^ (prefixWord ++ tailWord_3568197).sum := by decide
  have hdescent : baseEnd_3568197 < baseStart_3568197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568229 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_3568229 : Nat := 118140960795 + 3568229 * 2 ^ 59
def prefixEnd_3568229 : Nat := 4983230072969 + 3 ^ 40 * 3568229 * 2
def baseEnd_3568229 : Nat := 1221477708208016680885013

theorem tailTrace_3568229 : CollatzResearch.WordTrace tailWord_3568229 prefixEnd_3568229 1221477708208016680885013 := by
  unfold tailWord_3568229
  simp only [CollatzResearch.WordTrace]
  refine ⟨130144003389923212841099741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86762668926615475227399827 130144003389923212841099741)
  ·
    refine ⟨48804001271221204815412403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130144003389923212841099741 48804001271221204815412403)
    ·
      refine ⟨73206001906831807223118605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48804001271221204815412403 73206001906831807223118605)
      ·
        refine ⟨27452250715061927708669477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73206001906831807223118605 27452250715061927708669477)
        ·
          refine ⟨5147297009074111445375527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27452250715061927708669477 5147297009074111445375527)
          ·
            refine ⟨7720945513611167168063291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147297009074111445375527 7720945513611167168063291)
            ·
              refine ⟨11581418270416750752094937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720945513611167168063291 11581418270416750752094937)
              ·
                refine ⟨8686063702812563064071203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11581418270416750752094937 8686063702812563064071203)
                ·
                  refine ⟨13029095554218844596106805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8686063702812563064071203 13029095554218844596106805)
                  ·
                    refine ⟨1221477708208016680885013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13029095554218844596106805 1221477708208016680885013)
                    ·
                      rfl

theorem cell22_3568229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_3568229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568229 prefixEnd_3568229 := by exact prefixLift 3568229
  have htrace : WordTrace (prefixWord ++ tailWord_3568229) baseStart_3568229 baseEnd_3568229 := by
    simpa [prefixWord, tailWord_3568229, baseEnd_3568229] using wordTrace_append hprefix tailTrace_3568229
  have hstable : (prefixWord ++ tailWord_3568229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568229).length < 2 ^ (prefixWord ++ tailWord_3568229).sum := by decide
  have hdescent : baseEnd_3568229 < baseStart_3568229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568242 : List Nat := [3, 2, 1, 2, 4, 10]
def baseStart_3568242 : Nat := 118140960795 + 3568242 * 2 ^ 59
def prefixEnd_3568242 : Nat := 4983230072969 + 3 ^ 40 * 3568242 * 2
def baseEnd_3568242 : Nat := 15080026646588752843333

theorem tailTrace_3568242 : CollatzResearch.WordTrace tailWord_3568242 prefixEnd_3568242 15080026646588752843333 := by
  unfold tailWord_3568242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32536119384719029015330745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86762985025917410707548653 32536119384719029015330745)
  ·
    refine ⟨24402089538539271761498059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32536119384719029015330745 24402089538539271761498059)
    ·
      refine ⟨36603134307808907642247089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24402089538539271761498059 36603134307808907642247089)
      ·
        refine ⟨27452350730856680731685317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36603134307808907642247089 27452350730856680731685317)
        ·
          refine ⟨5147315762035627637190997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27452350730856680731685317 5147315762035627637190997)
          ·
            refine ⟨15080026646588752843333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5147315762035627637190997 15080026646588752843333)
            ·
              rfl

theorem cell22_3568242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 10].length) (baseStart_3568242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568242 prefixEnd_3568242 := by exact prefixLift 3568242
  have htrace : WordTrace (prefixWord ++ tailWord_3568242) baseStart_3568242 baseEnd_3568242 := by
    simpa [prefixWord, tailWord_3568242, baseEnd_3568242] using wordTrace_append hprefix tailTrace_3568242
  have hstable : (prefixWord ++ tailWord_3568242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568242).length < 2 ^ (prefixWord ++ tailWord_3568242).sum := by decide
  have hdescent : baseEnd_3568242 < baseStart_3568242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568276 : List Nat := [2, 4, 2, 2, 1, 2, 3, 6]
def baseStart_3568276 : Nat := 118140960795 + 3568276 * 2 ^ 59
def prefixEnd_3568276 : Nat := 4983230072969 + 3 ^ 40 * 3568276 * 2
def baseEnd_3568276 : Nat := 135721533029836024995541

theorem tailTrace_3568276 : CollatzResearch.WordTrace tailWord_3568276 prefixEnd_3568276 135721533029836024995541 := by
  unfold tailWord_3568276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65072858810376469934030341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86763811747168626578707121 65072858810376469934030341)
  ·
    refine ⟨12201161026945588112630689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65072858810376469934030341 12201161026945588112630689)
    ·
      refine ⟨9150870770209191084473017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12201161026945588112630689 9150870770209191084473017)
      ·
        refine ⟨6863153077656893313354763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9150870770209191084473017 6863153077656893313354763)
        ·
          refine ⟨10294729616485339970032145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863153077656893313354763 10294729616485339970032145)
          ·
            refine ⟨7721047212364004977524109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10294729616485339970032145 7721047212364004977524109)
            ·
              refine ⟨2895392704636501866571541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7721047212364004977524109 2895392704636501866571541)
              ·
                refine ⟨135721533029836024995541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2895392704636501866571541 135721533029836024995541)
                ·
                  rfl

theorem cell22_3568276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_3568276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568276 prefixEnd_3568276 := by exact prefixLift 3568276
  have htrace : WordTrace (prefixWord ++ tailWord_3568276) baseStart_3568276 baseEnd_3568276 := by
    simpa [prefixWord, tailWord_3568276, baseEnd_3568276] using wordTrace_append hprefix tailTrace_3568276
  have hstable : (prefixWord ++ tailWord_3568276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568276).length < 2 ^ (prefixWord ++ tailWord_3568276).sum := by decide
  have hdescent : baseEnd_3568276 < baseStart_3568276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568366 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3568366 : Nat := 118140960795 + 3568366 * 2 ^ 59
def prefixEnd_3568366 : Nat := 4983230072969 + 3 ^ 40 * 3568366 * 2
def baseEnd_3568366 : Nat := 407174868702597996736531

theorem tailTrace_3568366 : CollatzResearch.WordTrace tailWord_3568366 prefixEnd_3568366 407174868702597996736531 := by
  unfold tailWord_3568366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16268625023803360654854619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86766000126951256825891301 16268625023803360654854619)
  ·
    refine ⟨24402937535705040982281929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16268625023803360654854619 24402937535705040982281929)
    ·
      refine ⟨18302203151778780736711447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24402937535705040982281929 18302203151778780736711447)
      ·
        refine ⟨27453304727668171105067171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18302203151778780736711447 27453304727668171105067171)
        ·
          refine ⟨41179957091502256657600757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27453304727668171105067171 41179957091502256657600757)
          ·
            refine ⟨3860620977328336561650071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41179957091502256657600757 3860620977328336561650071)
            ·
              refine ⟨5790931465992504842475107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860620977328336561650071 5790931465992504842475107)
              ·
                refine ⟨8686397198988757263712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5790931465992504842475107 8686397198988757263712661)
                ·
                  refine ⟨407174868702597996736531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686397198988757263712661 407174868702597996736531)
                  ·
                    rfl

theorem cell22_3568366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3568366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568366 prefixEnd_3568366 := by exact prefixLift 3568366
  have htrace : WordTrace (prefixWord ++ tailWord_3568366) baseStart_3568366 baseEnd_3568366 := by
    simpa [prefixWord, tailWord_3568366, baseEnd_3568366] using wordTrace_append hprefix tailTrace_3568366
  have hstable : (prefixWord ++ tailWord_3568366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568366).length < 2 ^ (prefixWord ++ tailWord_3568366).sum := by decide
  have hdescent : baseEnd_3568366 < baseStart_3568366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568372 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3568372 : Nat := 118140960795 + 3568372 * 2 ^ 59
def prefixEnd_3568372 : Nat := 4983230072969 + 3 ^ 40 * 3568372 * 2
def baseEnd_3568372 : Nat := 407175553343470658186525

theorem tailTrace_3568372 : CollatzResearch.WordTrace tailWord_3568372 prefixEnd_3568372 407175553343470658186525 := by
  unfold tailWord_3568372
  simp only [CollatzResearch.WordTrace]
  refine ⟨65074609514202574131777685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86766146018936765509036913 65074609514202574131777685)
  ·
    refine ⟨3050372320978245662427079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65074609514202574131777685 3050372320978245662427079)
    ·
      refine ⟨4575558481467368493640619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050372320978245662427079 4575558481467368493640619)
      ·
        refine ⟨6863337722201052740460929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575558481467368493640619 6863337722201052740460929)
        ·
          refine ⟨5147503291650789555345697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6863337722201052740460929 5147503291650789555345697)
          ·
            refine ⟨3860627468738092166509273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5147503291650789555345697 3860627468738092166509273)
            ·
              refine ⟨2895470601553569124881955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860627468738092166509273 2895470601553569124881955)
              ·
                refine ⟨4343205902330353687322933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895470601553569124881955 4343205902330353687322933)
                ·
                  refine ⟨407175553343470658186525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343205902330353687322933 407175553343470658186525)
                  ·
                    rfl

theorem cell22_3568372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3568372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568372 prefixEnd_3568372 := by exact prefixLift 3568372
  have htrace : WordTrace (prefixWord ++ tailWord_3568372) baseStart_3568372 baseEnd_3568372 := by
    simpa [prefixWord, tailWord_3568372, baseEnd_3568372] using wordTrace_append hprefix tailTrace_3568372
  have hstable : (prefixWord ++ tailWord_3568372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568372).length < 2 ^ (prefixWord ++ tailWord_3568372).sum := by decide
  have hdescent : baseEnd_3568372 < baseStart_3568372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568381 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_3568381 : Nat := 118140960795 + 3568381 * 2 ^ 59
def prefixEnd_3568381 : Nat := 4983230072969 + 3 ^ 40 * 3568381 * 2
def baseEnd_3568381 : Nat := 1221529740914338951084547

theorem tailTrace_3568381 : CollatzResearch.WordTrace tailWord_3568381 prefixEnd_3568381 1221529740914338951084547 := by
  unfold tailWord_3568381
  simp only [CollatzResearch.WordTrace]
  refine ⟨130149547285372542800632997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86766364856915028533755331 130149547285372542800632997)
  ·
    refine ⟨24403040116007351775118687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130149547285372542800632997 24403040116007351775118687)
    ·
      refine ⟨36604560174011027662678031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24403040116007351775118687 36604560174011027662678031)
      ·
        refine ⟨54906840261016541494017047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36604560174011027662678031 54906840261016541494017047)
        ·
          refine ⟨82360260391524812241025571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54906840261016541494017047 82360260391524812241025571)
          ·
            refine ⟨123540390587287218361538357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82360260391524812241025571 123540390587287218361538357)
            ·
              refine ⟨11581911617558176721394221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123540390587287218361538357 11581911617558176721394221)
              ·
                refine ⟨4343216856584316270522833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11581911617558176721394221 4343216856584316270522833)
                ·
                  refine ⟨3257412642438237202892125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4343216856584316270522833 3257412642438237202892125)
                  ·
                    refine ⟨1221529740914338951084547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257412642438237202892125 1221529740914338951084547)
                    ·
                      rfl

theorem cell22_3568381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_3568381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568381 prefixEnd_3568381 := by exact prefixLift 3568381
  have htrace : WordTrace (prefixWord ++ tailWord_3568381) baseStart_3568381 baseEnd_3568381 := by
    simpa [prefixWord, tailWord_3568381, baseEnd_3568381] using wordTrace_append hprefix tailTrace_3568381
  have hstable : (prefixWord ++ tailWord_3568381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568381).length < 2 ^ (prefixWord ++ tailWord_3568381).sum := by decide
  have hdescent : baseEnd_3568381 < baseStart_3568381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568409 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_3568409 : Nat := 118140960795 + 3568409 * 2 ^ 59
def prefixEnd_3568409 : Nat := 4983230072969 + 3 ^ 40 * 3568409 * 2
def baseEnd_3568409 : Nat := 1221539325886556211384461

theorem tailTrace_3568409 : CollatzResearch.WordTrace tailWord_3568409 prefixEnd_3568409 1221539325886556211384461 := by
  unfold tailWord_3568409
  simp only [CollatzResearch.WordTrace]
  refine ⟨130150568529271103582652281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86767045686180735721768187 130150568529271103582652281)
  ·
    refine ⟨97612926396953327686989211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130150568529271103582652281 97612926396953327686989211)
    ·
      refine ⟨146419389595429991530483817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97612926396953327686989211 146419389595429991530483817)
      ·
        refine ⟨109814542196572493647862863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146419389595429991530483817 109814542196572493647862863)
        ·
          refine ⟨164721813294858740471794295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109814542196572493647862863 164721813294858740471794295)
          ·
            refine ⟨247082719942288110707691443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164721813294858740471794295 247082719942288110707691443)
            ·
              refine ⟨370624079913432166061537165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247082719942288110707691443 370624079913432166061537165)
              ·
                refine ⟨138984029967537062273076437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370624079913432166061537165 138984029967537062273076437)
                ·
                  refine ⟨3257438202364149897025229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138984029967537062273076437 3257438202364149897025229)
                  ·
                    refine ⟨1221539325886556211384461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257438202364149897025229 1221539325886556211384461)
                    ·
                      rfl

theorem cell22_3568409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_3568409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568409 prefixEnd_3568409 := by exact prefixLift 3568409
  have htrace : WordTrace (prefixWord ++ tailWord_3568409) baseStart_3568409 baseEnd_3568409 := by
    simpa [prefixWord, tailWord_3568409, baseEnd_3568409] using wordTrace_append hprefix tailTrace_3568409
  have hstable : (prefixWord ++ tailWord_3568409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568409).length < 2 ^ (prefixWord ++ tailWord_3568409).sum := by decide
  have hdescent : baseEnd_3568409 < baseStart_3568409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568424 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3568424 : Nat := 118140960795 + 3568424 * 2 ^ 59
def prefixEnd_3568424 : Nat := 4983230072969 + 3 ^ 40 * 3568424 * 2
def baseEnd_3568424 : Nat := 1221544460693101172259415

theorem tailTrace_3568424 : CollatzResearch.WordTrace tailWord_3568424 prefixEnd_3568424 1221544460693101172259415 := by
  unfold tailWord_3568424
  simp only [CollatzResearch.WordTrace]
  refine ⟨65075557812108380572224163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86767410416144507429632217 65075557812108380572224163)
  ·
    refine ⟨97613336718162570858336245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65075557812108380572224163 97613336718162570858336245)
    ·
      refine ⟨9151250317327741017969023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97613336718162570858336245 9151250317327741017969023)
      ·
        refine ⟨13726875475991611526953535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9151250317327741017969023 13726875475991611526953535)
        ·
          refine ⟨20590313213987417290430303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13726875475991611526953535 20590313213987417290430303)
          ·
            refine ⟨30885469820981125935645455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20590313213987417290430303 30885469820981125935645455)
            ·
              refine ⟨46328204731471688903468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30885469820981125935645455 46328204731471688903468183)
              ·
                refine ⟨69492307097207533355202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46328204731471688903468183 69492307097207533355202275)
                ·
                  refine ⟨104238460645811300032803413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69492307097207533355202275 104238460645811300032803413)
                  ·
                    refine ⟨1221544460693101172259415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104238460645811300032803413 1221544460693101172259415)
                    ·
                      rfl

theorem cell22_3568424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3568424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568424 prefixEnd_3568424 := by exact prefixLift 3568424
  have htrace : WordTrace (prefixWord ++ tailWord_3568424) baseStart_3568424 baseEnd_3568424 := by
    simpa [prefixWord, tailWord_3568424, baseEnd_3568424] using wordTrace_append hprefix tailTrace_3568424
  have hstable : (prefixWord ++ tailWord_3568424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568424).length < 2 ^ (prefixWord ++ tailWord_3568424).sum := by decide
  have hdescent : baseEnd_3568424 < baseStart_3568424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568439 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 5]
def baseStart_3568439 : Nat := 118140960795 + 3568439 * 2 ^ 59
def prefixEnd_3568439 : Nat := 4983230072969 + 3 ^ 40 * 3568439 * 2
def baseEnd_3568439 : Nat := 407183198499882044378123

theorem tailTrace_3568439 : CollatzResearch.WordTrace tailWord_3568439 prefixEnd_3568439 407183198499882044378123 := by
  unfold tailWord_3568439
  simp only [CollatzResearch.WordTrace]
  refine ⟨130151662719162418706244371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86767775146108279137496247 130151662719162418706244371)
  ·
    refine ⟨195227494078743628059366557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130151662719162418706244371 195227494078743628059366557)
    ·
      refine ⟨73210310279528860522262459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195227494078743628059366557 73210310279528860522262459)
      ·
        refine ⟨109815465419293290783393689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73210310279528860522262459 109815465419293290783393689)
        ·
          refine ⟨82361599064469968087545267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109815465419293290783393689 82361599064469968087545267)
          ·
            refine ⟨123542398596704952131317901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82361599064469968087545267 123542398596704952131317901)
            ·
              refine ⟨46328399473764357049244213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123542398596704952131317901 46328399473764357049244213)
              ·
                refine ⟨4343287450665408473366645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46328399473764357049244213 4343287450665408473366645)
                ·
                  refine ⟨407183198499882044378123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343287450665408473366645 407183198499882044378123)
                  ·
                    rfl

theorem cell22_3568439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 5].length) (baseStart_3568439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568439 prefixEnd_3568439 := by exact prefixLift 3568439
  have htrace : WordTrace (prefixWord ++ tailWord_3568439) baseStart_3568439 baseEnd_3568439 := by
    simpa [prefixWord, tailWord_3568439, baseEnd_3568439] using wordTrace_append hprefix tailTrace_3568439
  have hstable : (prefixWord ++ tailWord_3568439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568439).length < 2 ^ (prefixWord ++ tailWord_3568439).sum := by decide
  have hdescent : baseEnd_3568439 < baseStart_3568439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568460 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_3568460 : Nat := 118140960795 + 3568460 * 2 ^ 59
def prefixEnd_3568460 : Nat := 4983230072969 + 3 ^ 40 * 3568460 * 2
def baseEnd_3568460 : Nat := 1221556784228809078359305

theorem tailTrace_3568460 : CollatzResearch.WordTrace tailWord_3568460 prefixEnd_3568460 1221556784228809078359305 := by
  unfold tailWord_3568460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65076214326043169646379417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86768285768057559528505889 65076214326043169646379417)
  ·
    refine ⟨48807160744532377234784563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65076214326043169646379417 48807160744532377234784563)
    ·
      refine ⟨73210741116798565852176845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48807160744532377234784563 73210741116798565852176845)
      ·
        refine ⟨27454027918799462194566317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73210741116798565852176845 27454027918799462194566317)
        ·
          refine ⟨10295260469549798322962369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27454027918799462194566317 10295260469549798322962369)
          ·
            refine ⟨7721445352162348742221777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10295260469549798322962369 7721445352162348742221777)
            ·
              refine ⟨5791084014121761556666333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7721445352162348742221777 5791084014121761556666333)
              ·
                refine ⟨2171656505295660583749875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5791084014121761556666333 2171656505295660583749875)
                ·
                  refine ⟨3257484757943490875624813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171656505295660583749875 3257484757943490875624813)
                  ·
                    refine ⟨1221556784228809078359305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257484757943490875624813 1221556784228809078359305)
                    ·
                      rfl

theorem cell22_3568460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_3568460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568460 prefixEnd_3568460 := by exact prefixLift 3568460
  have htrace : WordTrace (prefixWord ++ tailWord_3568460) baseStart_3568460 baseEnd_3568460 := by
    simpa [prefixWord, tailWord_3568460, baseEnd_3568460] using wordTrace_append hprefix tailTrace_3568460
  have hstable : (prefixWord ++ tailWord_3568460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568460).length < 2 ^ (prefixWord ++ tailWord_3568460).sum := by decide
  have hdescent : baseEnd_3568460 < baseStart_3568460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568501 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 6]
def baseStart_3568501 : Nat := 118140960795 + 3568501 * 2 ^ 59
def prefixEnd_3568501 : Nat := 4983230072969 + 3 ^ 40 * 3568501 * 2
def baseEnd_3568501 : Nat := 407190273122232879361393

theorem tailTrace_3568501 : CollatzResearch.WordTrace tailWord_3568501 prefixEnd_3568501 407190273122232879361393 := by
  unfold tailWord_3568501
  simp only [CollatzResearch.WordTrace]
  refine ⟨130153924044937803295001357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86769282696625202196667571 130153924044937803295001357)
  ·
    refine ⟨48807721516851676235625509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130153924044937803295001357 48807721516851676235625509)
    ·
      refine ⟨9151447784409689294179783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48807721516851676235625509 9151447784409689294179783)
      ·
        refine ⟨13727171676614533941269675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9151447784409689294179783 13727171676614533941269675)
        ·
          refine ⟨20590757514921800911904513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727171676614533941269675 20590757514921800911904513)
          ·
            refine ⟨15443068136191350683928385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20590757514921800911904513 15443068136191350683928385)
            ·
              refine ⟨11582301102143513012946289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15443068136191350683928385 11582301102143513012946289)
              ·
                refine ⟨8686725826607634759709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11582301102143513012946289 8686725826607634759709717)
                ·
                  refine ⟨407190273122232879361393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8686725826607634759709717 407190273122232879361393)
                  ·
                    rfl

theorem cell22_3568501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_3568501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568501 prefixEnd_3568501 := by exact prefixLift 3568501
  have htrace : WordTrace (prefixWord ++ tailWord_3568501) baseStart_3568501 baseEnd_3568501 := by
    simpa [prefixWord, tailWord_3568501, baseEnd_3568501] using wordTrace_append hprefix tailTrace_3568501
  have hstable : (prefixWord ++ tailWord_3568501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568501).length < 2 ^ (prefixWord ++ tailWord_3568501).sum := by decide
  have hdescent : baseEnd_3568501 < baseStart_3568501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568546 : List Nat := [3, 3, 1, 2, 2, 1, 1, 9]
def baseStart_3568546 : Nat := 118140960795 + 3568546 * 2 ^ 59
def prefixEnd_3568546 : Nat := 4983230072969 + 3 ^ 40 * 3568546 * 2
def baseEnd_3568546 : Nat := 135731802642925946745449

theorem tailTrace_3568546 : CollatzResearch.WordTrace tailWord_3568546 prefixEnd_3568546 135731802642925946745449 := by
  unfold tailWord_3568546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538891332443693995097373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86770376886516517320259661 32538891332443693995097373)
  ·
    refine ⟨12202084249666385248161515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32538891332443693995097373 12202084249666385248161515)
    ·
      refine ⟨18303126374499577872242273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12202084249666385248161515 18303126374499577872242273)
      ·
        refine ⟨13727344780874683404181705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18303126374499577872242273 13727344780874683404181705)
        ·
          refine ⟨10295508585656012553136279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13727344780874683404181705 10295508585656012553136279)
          ·
            refine ⟨15443262878484018829704419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10295508585656012553136279 15443262878484018829704419)
            ·
              refine ⟨23164894317726028244556629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15443262878484018829704419 23164894317726028244556629)
              ·
                refine ⟨135731802642925946745449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23164894317726028244556629 135731802642925946745449)
                ·
                  rfl

theorem cell22_3568546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_3568546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568546 prefixEnd_3568546 := by exact prefixLift 3568546
  have htrace : WordTrace (prefixWord ++ tailWord_3568546) baseStart_3568546 baseEnd_3568546 := by
    simpa [prefixWord, tailWord_3568546, baseEnd_3568546] using wordTrace_append hprefix tailTrace_3568546
  have hstable : (prefixWord ++ tailWord_3568546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568546).length < 2 ^ (prefixWord ++ tailWord_3568546).sum := by decide
  have hdescent : baseEnd_3568546 < baseStart_3568546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568559 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3568559 : Nat := 118140960795 + 3568559 * 2 ^ 59
def prefixEnd_3568559 : Nat := 4983230072969 + 3 ^ 40 * 3568559 * 2
def baseEnd_3568559 : Nat := 1221590673952005820134001

theorem tailTrace_3568559 : CollatzResearch.WordTrace tailWord_3568559 prefixEnd_3568559 1221590673952005820134001 := by
  unfold tailWord_3568559
  simp only [CollatzResearch.WordTrace]
  refine ⟨130156039478727679200612731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86770692985818452800408487 130156039478727679200612731)
  ·
    refine ⟨195234059218091518800919097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130156039478727679200612731 195234059218091518800919097)
    ·
      refine ⟨146425544413568639100689323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195234059218091518800919097 146425544413568639100689323)
      ·
        refine ⟨219638316620352958651033985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146425544413568639100689323 219638316620352958651033985)
        ·
          refine ⟨164728737465264718988275489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219638316620352958651033985 164728737465264718988275489)
          ·
            refine ⟨123546553098948539241206617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164728737465264718988275489 123546553098948539241206617)
            ·
              refine ⟨92659914824211404430904963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123546553098948539241206617 92659914824211404430904963)
              ·
                refine ⟨138989872236317106646357445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92659914824211404430904963 138989872236317106646357445)
                ·
                  refine ⟨26060601044309457496192021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138989872236317106646357445 26060601044309457496192021)
                  ·
                    refine ⟨1221590673952005820134001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26060601044309457496192021 1221590673952005820134001)
                    ·
                      rfl

theorem cell22_3568559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3568559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568559 prefixEnd_3568559 := by exact prefixLift 3568559
  have htrace : WordTrace (prefixWord ++ tailWord_3568559) baseStart_3568559 baseEnd_3568559 := by
    simpa [prefixWord, tailWord_3568559, baseEnd_3568559] using wordTrace_append hprefix tailTrace_3568559
  have hstable : (prefixWord ++ tailWord_3568559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568559).length < 2 ^ (prefixWord ++ tailWord_3568559).sum := by decide
  have hdescent : baseEnd_3568559 < baseStart_3568559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568591 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 5]
def baseStart_3568591 : Nat := 118140960795 + 3568591 * 2 ^ 59
def prefixEnd_3568591 : Nat := 4983230072969 + 3 ^ 40 * 3568591 * 2
def baseEnd_3568591 : Nat := 407200542735322801111301

theorem tailTrace_3568591 : CollatzResearch.WordTrace tailWord_3568591 prefixEnd_3568591 407200542735322801111301 := by
  unfold tailWord_3568591
  simp only [CollatzResearch.WordTrace]
  refine ⟨130157206614611748665777627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86771471076407832443851751 130157206614611748665777627)
  ·
    refine ⟨195235809921917622998666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130157206614611748665777627 195235809921917622998666441)
    ·
      refine ⟨146426857441438217248999831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195235809921917622998666441 146426857441438217248999831)
      ·
        refine ⟨219640286162157325873499747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146426857441438217248999831 219640286162157325873499747)
        ·
          refine ⟨329460429243235988810249621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219640286162157325873499747 329460429243235988810249621)
          ·
            refine ⟨15443457620776686975480451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 329460429243235988810249621 15443457620776686975480451)
            ·
              refine ⟨23165186431165030463220677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15443457620776686975480451 23165186431165030463220677)
              ·
                refine ⟨4343472455843443211853877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23165186431165030463220677 4343472455843443211853877)
                ·
                  refine ⟨407200542735322801111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343472455843443211853877 407200542735322801111301)
                  ·
                    rfl

theorem cell22_3568591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 5].length) (baseStart_3568591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568591 prefixEnd_3568591 := by exact prefixLift 3568591
  have htrace : WordTrace (prefixWord ++ tailWord_3568591) baseStart_3568591 baseEnd_3568591 := by
    simpa [prefixWord, tailWord_3568591, baseEnd_3568591] using wordTrace_append hprefix tailTrace_3568591
  have hstable : (prefixWord ++ tailWord_3568591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568591).length < 2 ^ (prefixWord ++ tailWord_3568591).sum := by decide
  have hdescent : baseEnd_3568591 < baseStart_3568591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568666 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3568666 : Nat := 118140960795 + 3568666 * 2 ^ 59
def prefixEnd_3568666 : Nat := 4983230072969 + 3 ^ 40 * 3568666 * 2
def baseEnd_3568666 : Nat := 1221627302238693207708673

theorem tailTrace_3568666 : CollatzResearch.WordTrace tailWord_3568666 prefixEnd_3568666 1221627302238693207708673 := by
  unfold tailWord_3568666
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539985522335009118689463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86773294726226690983171901 32539985522335009118689463)
  ·
    refine ⟨48809978283502513678034195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32539985522335009118689463 48809978283502513678034195)
    ·
      refine ⟨73214967425253770517051293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48809978283502513678034195 73214967425253770517051293)
      ·
        refine ⟨27455612784470163943894235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73214967425253770517051293 27455612784470163943894235)
        ·
          refine ⟨41183419176705245915841353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27455612784470163943894235 41183419176705245915841353)
          ·
            refine ⟨30887564382528934436881015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41183419176705245915841353 30887564382528934436881015)
            ·
              refine ⟨46331346573793401655321523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30887564382528934436881015 46331346573793401655321523)
              ·
                refine ⟨69497019860690102482982285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46331346573793401655321523 69497019860690102482982285)
                ·
                  refine ⟨26061382447758788431118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69497019860690102482982285 26061382447758788431118357)
                  ·
                    refine ⟨1221627302238693207708673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26061382447758788431118357 1221627302238693207708673)
                    ·
                      rfl

theorem cell22_3568666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3568666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568666 prefixEnd_3568666 := by exact prefixLift 3568666
  have htrace : WordTrace (prefixWord ++ tailWord_3568666) baseStart_3568666 baseEnd_3568666 := by
    simpa [prefixWord, tailWord_3568666, baseEnd_3568666] using wordTrace_append hprefix tailTrace_3568666
  have hstable : (prefixWord ++ tailWord_3568666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568666).length < 2 ^ (prefixWord ++ tailWord_3568666).sum := by decide
  have hdescent : baseEnd_3568666 < baseStart_3568666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568672 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_3568672 : Nat := 118140960795 + 3568672 * 2 ^ 59
def prefixEnd_3568672 : Nat := 4983230072969 + 3 ^ 40 * 3568672 * 2
def baseEnd_3568672 : Nat := 1221629356161311192058655

theorem tailTrace_3568672 : CollatzResearch.WordTrace tailWord_3568672 prefixEnd_3568672 1221629356161311192058655 := by
  unfold tailWord_3568672
  simp only [CollatzResearch.WordTrace]
  refine ⟨65080080463659149749738135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86773440618212199666317513 65080080463659149749738135)
  ·
    refine ⟨97620120695488724624607203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65080080463659149749738135 97620120695488724624607203)
    ·
      refine ⟨146430181043233086936910805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97620120695488724624607203 146430181043233086936910805)
      ·
        refine ⟨3431957368200775475083847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 146430181043233086936910805 3431957368200775475083847)
        ·
          refine ⟨5147936052301163212625771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431957368200775475083847 5147936052301163212625771)
          ·
            refine ⟨7721904078451744818938657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147936052301163212625771 7721904078451744818938657)
            ·
              refine ⟨5791428058838808614203993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7721904078451744818938657 5791428058838808614203993)
              ·
                refine ⟨4343571044129106460652995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5791428058838808614203993 4343571044129106460652995)
                ·
                  refine ⟨6515356566193659690979493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343571044129106460652995 6515356566193659690979493)
                  ·
                    refine ⟨1221629356161311192058655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515356566193659690979493 1221629356161311192058655)
                    ·
                      rfl

theorem cell22_3568672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_3568672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568672 prefixEnd_3568672 := by exact prefixLift 3568672
  have htrace : WordTrace (prefixWord ++ tailWord_3568672) baseStart_3568672 baseEnd_3568672 := by
    simpa [prefixWord, tailWord_3568672, baseEnd_3568672] using wordTrace_append hprefix tailTrace_3568672
  have hstable : (prefixWord ++ tailWord_3568672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568672).length < 2 ^ (prefixWord ++ tailWord_3568672).sum := by decide
  have hdescent : baseEnd_3568672 < baseStart_3568672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568713 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_3568713 : Nat := 118140960795 + 3568713 * 2 ^ 59
def prefixEnd_3568713 : Nat := 4983230072969 + 3 ^ 40 * 3568713 * 2
def baseEnd_3568713 : Nat := 1221643391299200751783529

theorem tailTrace_3568713 : CollatzResearch.WordTrace tailWord_3568713 prefixEnd_3568713 1221643391299200751783529 := by
  unfold tailWord_3568713
  simp only [CollatzResearch.WordTrace]
  refine ⟨130161656320169763501718793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86774437546779842334479195 130161656320169763501718793)
  ·
    refine ⟨97621242240127322626289095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130161656320169763501718793 97621242240127322626289095)
    ·
      refine ⟨146431863360190983939433643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97621242240127322626289095 146431863360190983939433643)
      ·
        refine ⟨219647795040286475909150465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146431863360190983939433643 219647795040286475909150465)
        ·
          refine ⟨164735846280214856931862849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219647795040286475909150465 164735846280214856931862849)
          ·
            refine ⟨123551884710161142698897137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164735846280214856931862849 123551884710161142698897137)
            ·
              refine ⟨92663913532620857024172853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123551884710161142698897137 92663913532620857024172853)
              ·
                refine ⟨8687241893683205346016205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92663913532620857024172853 8687241893683205346016205)
                ·
                  refine ⟨3257715710131202004756077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687241893683205346016205 3257715710131202004756077)
                  ·
                    refine ⟨1221643391299200751783529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257715710131202004756077 1221643391299200751783529)
                    ·
                      rfl

theorem cell22_3568713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_3568713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568713 prefixEnd_3568713 := by exact prefixLift 3568713
  have htrace : WordTrace (prefixWord ++ tailWord_3568713) baseStart_3568713 baseEnd_3568713 := by
    simpa [prefixWord, tailWord_3568713, baseEnd_3568713] using wordTrace_append hprefix tailTrace_3568713
  have hstable : (prefixWord ++ tailWord_3568713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568713).length < 2 ^ (prefixWord ++ tailWord_3568713).sum := by decide
  have hdescent : baseEnd_3568713 < baseStart_3568713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568734 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3568734 : Nat := 118140960795 + 3568734 * 2 ^ 59
def prefixEnd_3568734 : Nat := 4983230072969 + 3 ^ 40 * 3568734 * 2
def baseEnd_3568734 : Nat := 1221650580028363697008465

theorem tailTrace_3568734 : CollatzResearch.WordTrace tailWord_3568734 prefixEnd_3568734 1221650580028363697008465 := by
  unfold tailWord_3568734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270302781636710511029157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86774948168729122725488837 16270302781636710511029157)
  ·
    refine ⟨3050681771556883220817967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16270302781636710511029157 3050681771556883220817967)
    ·
      refine ⟨4576022657335324831226951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050681771556883220817967 4576022657335324831226951)
      ·
        refine ⟨6864033986002987246840427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576022657335324831226951 6864033986002987246840427)
        ·
          refine ⟨10296050979004480870260641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864033986002987246840427 10296050979004480870260641)
          ·
            refine ⟨7722038234253360652695481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10296050979004480870260641 7722038234253360652695481)
            ·
              refine ⟨5791528675690020489521611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7722038234253360652695481 5791528675690020489521611)
              ·
                refine ⟨8687293013535030734282417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791528675690020489521611 8687293013535030734282417)
                ·
                  refine ⟨6515469760151273050711813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8687293013535030734282417 6515469760151273050711813)
                  ·
                    refine ⟨1221650580028363697008465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515469760151273050711813 1221650580028363697008465)
                    ·
                      rfl

theorem cell22_3568734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3568734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568734 prefixEnd_3568734 := by exact prefixLift 3568734
  have htrace : WordTrace (prefixWord ++ tailWord_3568734) baseStart_3568734 baseEnd_3568734 := by
    simpa [prefixWord, tailWord_3568734, baseEnd_3568734] using wordTrace_append hprefix tailTrace_3568734
  have hstable : (prefixWord ++ tailWord_3568734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568734).length < 2 ^ (prefixWord ++ tailWord_3568734).sum := by decide
  have hdescent : baseEnd_3568734 < baseStart_3568734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568766 : List Nat := [4, 2, 4, 1, 2, 1, 1, 7]
def baseStart_3568766 : Nat := 118140960795 + 3568766 * 2 ^ 59
def prefixEnd_3568766 : Nat := 4983230072969 + 3 ^ 40 * 3568766 * 2
def baseEnd_3568766 : Nat := 135740170475814031134263

theorem tailTrace_3568766 : CollatzResearch.WordTrace tailWord_3568766 prefixEnd_3568766 135740170475814031134263 := by
  unfold tailWord_3568766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270448673622219194174769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86775726259318502368932101 16270448673622219194174769)
  ·
    refine ⟨12202836505216664395631077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16270448673622219194174769 12202836505216664395631077)
    ·
      refine ⟨2288031844728124574180827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12202836505216664395631077 2288031844728124574180827)
      ·
        refine ⟨3432047767092186861271241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288031844728124574180827 3432047767092186861271241)
        ·
          refine ⟨2574035825319140145953431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432047767092186861271241 2574035825319140145953431)
          ·
            refine ⟨3861053737978710218930147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574035825319140145953431 3861053737978710218930147)
            ·
              refine ⟨5791580606968065328395221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861053737978710218930147 5791580606968065328395221)
              ·
                refine ⟨135740170475814031134263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5791580606968065328395221 135740170475814031134263)
                ·
                  rfl

theorem cell22_3568766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_3568766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568766 prefixEnd_3568766 := by exact prefixLift 3568766
  have htrace : WordTrace (prefixWord ++ tailWord_3568766) baseStart_3568766 baseEnd_3568766 := by
    simpa [prefixWord, tailWord_3568766, baseEnd_3568766] using wordTrace_append hprefix tailTrace_3568766
  have hstable : (prefixWord ++ tailWord_3568766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568766).length < 2 ^ (prefixWord ++ tailWord_3568766).sum := by decide
  have hdescent : baseEnd_3568766 < baseStart_3568766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568805 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 4]
def baseStart_3568805 : Nat := 118140960795 + 3568805 * 2 ^ 59
def prefixEnd_3568805 : Nat := 4983230072969 + 3 ^ 40 * 3568805 * 2
def baseEnd_3568805 : Nat := 407224961593114392827749

theorem tailTrace_3568805 : CollatzResearch.WordTrace tailWord_3568805 prefixEnd_3568805 407224961593114392827749 := by
  unfold tailWord_3568805
  simp only [CollatzResearch.WordTrace]
  refine ⟨130165011835836463214067869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86776674557224308809378579 130165011835836463214067869)
  ·
    refine ⟨48811879438438673705275451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130165011835836463214067869 48811879438438673705275451)
    ·
      refine ⟨73217819157658010557913177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48811879438438673705275451 73217819157658010557913177)
      ·
        refine ⟨54913364368243507918434883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73217819157658010557913177 54913364368243507918434883)
        ·
          refine ⟨82370046552365261877652325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54913364368243507918434883 82370046552365261877652325)
          ·
            refine ⟨15444383728568486602059811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82370046552365261877652325 15444383728568486602059811)
            ·
              refine ⟨23166575592852729903089717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444383728568486602059811 23166575592852729903089717)
              ·
                refine ⟨2171866461829943428414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23166575592852729903089717 2171866461829943428414661)
                ·
                  refine ⟨407224961593114392827749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171866461829943428414661 407224961593114392827749)
                  ·
                    rfl

theorem cell22_3568805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_3568805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568805 prefixEnd_3568805 := by exact prefixLift 3568805
  have htrace : WordTrace (prefixWord ++ tailWord_3568805) baseStart_3568805 baseEnd_3568805 := by
    simpa [prefixWord, tailWord_3568805, baseEnd_3568805] using wordTrace_append hprefix tailTrace_3568805
  have hstable : (prefixWord ++ tailWord_3568805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568805).length < 2 ^ (prefixWord ++ tailWord_3568805).sum := by decide
  have hdescent : baseEnd_3568805 < baseStart_3568805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568807 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3568807 : Nat := 118140960795 + 3568807 * 2 ^ 59
def prefixEnd_3568807 : Nat := 4983230072969 + 3 ^ 40 * 3568807 * 2
def baseEnd_3568807 : Nat := 1221675569420215839933241

theorem tailTrace_3568807 : CollatzResearch.WordTrace tailWord_3568807 prefixEnd_3568807 1221675569420215839933241 := by
  unfold tailWord_3568807
  simp only [CollatzResearch.WordTrace]
  refine ⟨130165084781829217555640675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86776723187886145037093783 130165084781829217555640675)
  ·
    refine ⟨195247627172743826333461013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130165084781829217555640675 195247627172743826333461013)
    ·
      refine ⟨9152232523722366859380985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 195247627172743826333461013 9152232523722366859380985)
      ·
        refine ⟨6864174392791775144535739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9152232523722366859380985 6864174392791775144535739)
        ·
          refine ⟨10296261589187662716803609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864174392791775144535739 10296261589187662716803609)
          ·
            refine ⟨7722196191890747037602707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10296261589187662716803609 7722196191890747037602707)
            ·
              refine ⟨11583294287836120556404061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722196191890747037602707 11583294287836120556404061)
              ·
                refine ⟨4343735357938545208651523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11583294287836120556404061 4343735357938545208651523)
                ·
                  refine ⟨6515603036907817812977285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343735357938545208651523 6515603036907817812977285)
                  ·
                    refine ⟨1221675569420215839933241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6515603036907817812977285 1221675569420215839933241)
                    ·
                      rfl

theorem cell22_3568807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3568807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568807 prefixEnd_3568807 := by exact prefixLift 3568807
  have htrace : WordTrace (prefixWord ++ tailWord_3568807) baseStart_3568807 baseEnd_3568807 := by
    simpa [prefixWord, tailWord_3568807, baseEnd_3568807] using wordTrace_append hprefix tailTrace_3568807
  have hstable : (prefixWord ++ tailWord_3568807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568807).length < 2 ^ (prefixWord ++ tailWord_3568807).sum := by decide
  have hdescent : baseEnd_3568807 < baseStart_3568807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3568895 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 5]
def baseStart_3568895 : Nat := 118140960795 + 3568895 * 2 ^ 59
def prefixEnd_3568895 : Nat := 4983230072969 + 3 ^ 40 * 3568895 * 2
def baseEnd_3568895 : Nat := 407235231206204314577657

theorem tailTrace_3568895 : CollatzResearch.WordTrace tailWord_3568895 prefixEnd_3568895 407235231206204314577657 := by
  unfold tailWord_3568895
  simp only [CollatzResearch.WordTrace]
  refine ⟨130168294405510408584844139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86778862937006939056562759 130168294405510408584844139)
  ·
    refine ⟨195252441608265612877266209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130168294405510408584844139 195252441608265612877266209)
    ·
      refine ⟨146439331206199209657949657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195252441608265612877266209 146439331206199209657949657)
      ·
        refine ⟨109829498404649407243462243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146439331206199209657949657 109829498404649407243462243)
        ·
          refine ⟨164744247606974110865193365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109829498404649407243462243 164744247606974110865193365)
          ·
            refine ⟨7722386606576911446805939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164744247606974110865193365 7722386606576911446805939)
            ·
              refine ⟨11583579909865367170208909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7722386606576911446805939 11583579909865367170208909)
              ·
                refine ⟨4343842466199512688828341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11583579909865367170208909 4343842466199512688828341)
                ·
                  refine ⟨407235231206204314577657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4343842466199512688828341 407235231206204314577657)
                  ·
                    rfl

theorem cell22_3568895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 5].length) (baseStart_3568895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3568895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3568895 prefixEnd_3568895 := by exact prefixLift 3568895
  have htrace : WordTrace (prefixWord ++ tailWord_3568895) baseStart_3568895 baseEnd_3568895 := by
    simpa [prefixWord, tailWord_3568895, baseEnd_3568895] using wordTrace_append hprefix tailTrace_3568895
  have hstable : (prefixWord ++ tailWord_3568895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3568895).length < 2 ^ (prefixWord ++ tailWord_3568895).sum := by decide
  have hdescent : baseEnd_3568895 < baseStart_3568895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3568895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569006 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3569006 : Nat := 118140960795 + 3569006 * 2 ^ 59
def prefixEnd_3569006 : Nat := 4983230072969 + 3 ^ 40 * 3569006 * 2
def baseEnd_3569006 : Nat := 1221743691187045654207631

theorem tailTrace_3569006 : CollatzResearch.WordTrace tailWord_3569006 prefixEnd_3569006 1221743691187045654207631 := by
  unfold tailWord_3569006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271542863513534317766859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86781561938738849694756581 16271542863513534317766859)
  ·
    refine ⟨24407314295270301476650289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16271542863513534317766859 24407314295270301476650289)
    ·
      refine ⟨18305485721452726107487717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24407314295270301476650289 18305485721452726107487717)
      ·
        refine ⟨3432278572772386145153947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18305485721452726107487717 3432278572772386145153947)
        ·
          refine ⟨5148417859158579217730921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432278572772386145153947 5148417859158579217730921)
          ·
            refine ⟨3861313394368934413298191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5148417859158579217730921 3861313394368934413298191)
            ·
              refine ⟨5791970091553401619947287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861313394368934413298191 5791970091553401619947287)
              ·
                refine ⟨8687955137330102429920931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791970091553401619947287 8687955137330102429920931)
                ·
                  refine ⟨13031932705995153644881397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8687955137330102429920931 13031932705995153644881397)
                  ·
                    refine ⟨1221743691187045654207631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13031932705995153644881397 1221743691187045654207631)
                    ·
                      rfl

theorem cell22_3569006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3569006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569006 prefixEnd_3569006 := by exact prefixLift 3569006
  have htrace : WordTrace (prefixWord ++ tailWord_3569006) baseStart_3569006 baseEnd_3569006 := by
    simpa [prefixWord, tailWord_3569006, baseEnd_3569006] using wordTrace_append hprefix tailTrace_3569006
  have hstable : (prefixWord ++ tailWord_3569006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569006).length < 2 ^ (prefixWord ++ tailWord_3569006).sum := by decide
  have hdescent : baseEnd_3569006 < baseStart_3569006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569017 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_3569017 : Nat := 118140960795 + 3569017 * 2 ^ 59
def prefixEnd_3569017 : Nat := 4983230072969 + 3 ^ 40 * 3569017 * 2
def baseEnd_3569017 : Nat := 1221747456711845292182597

theorem tailTrace_3569017 : CollatzResearch.WordTrace tailWord_3569017 prefixEnd_3569017 1221747456711845292182597 := by
  unfold tailWord_3569017
  simp only [CollatzResearch.WordTrace]
  refine ⟨130172744111068423420785305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86781829407378948947190203 130172744111068423420785305)
  ·
    refine ⟨97629558083301317565588979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130172744111068423420785305 97629558083301317565588979)
    ·
      refine ⟨146444337124951976348383469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97629558083301317565588979 146444337124951976348383469)
      ·
        refine ⟨54916626421856991130643801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146444337124951976348383469 54916626421856991130643801)
        ·
          refine ⟨41187469816392743347982851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54916626421856991130643801 41187469816392743347982851)
          ·
            refine ⟨61781204724589115021974277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41187469816392743347982851 61781204724589115021974277)
            ·
              refine ⟨11583975885860459066620177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61781204724589115021974277 11583975885860459066620177)
              ·
                refine ⟨8687981914395344299965133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583975885860459066620177 8687981914395344299965133)
                ·
                  refine ⟨3257993217898254112486925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8687981914395344299965133 3257993217898254112486925)
                  ·
                    refine ⟨1221747456711845292182597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257993217898254112486925 1221747456711845292182597)
                    ·
                      rfl

theorem cell22_3569017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_3569017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569017 prefixEnd_3569017 := by exact prefixLift 3569017
  have htrace : WordTrace (prefixWord ++ tailWord_3569017) baseStart_3569017 baseEnd_3569017 := by
    simpa [prefixWord, tailWord_3569017, baseEnd_3569017] using wordTrace_append hprefix tailTrace_3569017
  have hstable : (prefixWord ++ tailWord_3569017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569017).length < 2 ^ (prefixWord ++ tailWord_3569017).sum := by decide
  have hdescent : baseEnd_3569017 < baseStart_3569017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569045 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3569045 : Nat := 118140960795 + 3569045 * 2 ^ 59
def prefixEnd_3569045 : Nat := 4983230072969 + 3 ^ 40 * 3569045 * 2
def baseEnd_3569045 : Nat := 1221757041684062552482511

theorem tailTrace_3569045 : CollatzResearch.WordTrace tailWord_3569045 prefixEnd_3569045 1221757041684062552482511 := by
  unfold tailWord_3569045
  simp only [CollatzResearch.WordTrace]
  refine ⟨130173765354966984202804589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86782510236644656135203059 130173765354966984202804589)
  ·
    refine ⟨48815162008112619076051721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130173765354966984202804589 48815162008112619076051721)
    ·
      refine ⟨36611371506084464307038791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48815162008112619076051721 36611371506084464307038791)
      ·
        refine ⟨54917057259126696460558187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36611371506084464307038791 54917057259126696460558187)
        ·
          refine ⟨82375585888690044690837281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54917057259126696460558187 82375585888690044690837281)
          ·
            refine ⟨61781689416517533518127961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82375585888690044690837281 61781689416517533518127961)
            ·
              refine ⟨46336267062388150138595971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61781689416517533518127961 46336267062388150138595971)
              ·
                refine ⟨69504400593582225207893957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46336267062388150138595971 69504400593582225207893957)
                ·
                  refine ⟨13032075111296667226480117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69504400593582225207893957 13032075111296667226480117)
                  ·
                    refine ⟨1221757041684062552482511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032075111296667226480117 1221757041684062552482511)
                    ·
                      rfl

theorem cell22_3569045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3569045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569045 prefixEnd_3569045 := by exact prefixLift 3569045
  have htrace : WordTrace (prefixWord ++ tailWord_3569045) baseStart_3569045 baseEnd_3569045 := by
    simpa [prefixWord, tailWord_3569045, baseEnd_3569045] using wordTrace_append hprefix tailTrace_3569045
  have hstable : (prefixWord ++ tailWord_3569045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569045).length < 2 ^ (prefixWord ++ tailWord_3569045).sum := by decide
  have hdescent : baseEnd_3569045 < baseStart_3569045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569060 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3569060 : Nat := 118140960795 + 3569060 * 2 ^ 59
def prefixEnd_3569060 : Nat := 4983230072969 + 3 ^ 40 * 3569060 * 2
def baseEnd_3569060 : Nat := 1221762176490607513357465

theorem tailTrace_3569060 : CollatzResearch.WordTrace tailWord_3569060 prefixEnd_3569060 1221762176490607513357465 := by
  unfold tailWord_3569060
  simp only [CollatzResearch.WordTrace]
  refine ⟨65087156224956320882300317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86782874966608427843067089 65087156224956320882300317)
  ·
    refine ⟨24407683584358620330862619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65087156224956320882300317 24407683584358620330862619)
    ·
      refine ⟨36611525376537930496293929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24407683584358620330862619 36611525376537930496293929)
      ·
        refine ⟨27458644032403447872220447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36611525376537930496293929 27458644032403447872220447)
        ·
          refine ⟨41187966048605171808330671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27458644032403447872220447 41187966048605171808330671)
          ·
            refine ⟨61781949072907757712496007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41187966048605171808330671 61781949072907757712496007)
            ·
              refine ⟨92672923609361636568744011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61781949072907757712496007 92672923609361636568744011)
              ·
                refine ⟨139009385414042454853116017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92672923609361636568744011 139009385414042454853116017)
                ·
                  refine ⟨104257039060531841139837013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139009385414042454853116017 104257039060531841139837013)
                  ·
                    refine ⟨1221762176490607513357465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104257039060531841139837013 1221762176490607513357465)
                    ·
                      rfl

theorem cell22_3569060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3569060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569060 prefixEnd_3569060 := by exact prefixLift 3569060
  have htrace : WordTrace (prefixWord ++ tailWord_3569060) baseStart_3569060 baseEnd_3569060 := by
    simpa [prefixWord, tailWord_3569060, baseEnd_3569060] using wordTrace_append hprefix tailTrace_3569060
  have hstable : (prefixWord ++ tailWord_3569060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569060).length < 2 ^ (prefixWord ++ tailWord_3569060).sum := by decide
  have hdescent : baseEnd_3569060 < baseStart_3569060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569075 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 6]
def baseStart_3569075 : Nat := 118140960795 + 3569075 * 2 ^ 59
def prefixEnd_3569075 : Nat := 4983230072969 + 3 ^ 40 * 3569075 * 2
def baseEnd_3569075 : Nat := 407255770432384158077473

theorem tailTrace_3569075 : CollatzResearch.WordTrace tailWord_3569075 prefixEnd_3569075 407255770432384158077473 := by
  unfold tailWord_3569075
  simp only [CollatzResearch.WordTrace]
  refine ⟨130174859544858299326396679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86783239696572199550931119 130174859544858299326396679)
  ·
    refine ⟨195262289317287448989595019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130174859544858299326396679 195262289317287448989595019)
    ·
      refine ⟨292893433975931173484392529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195262289317287448989595019 292893433975931173484392529)
      ·
        refine ⟨219670075481948380113294397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292893433975931173484392529 219670075481948380113294397)
        ·
          refine ⟨82376278305730642542485399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219670075481948380113294397 82376278305730642542485399)
          ·
            refine ⟨123564417458595963813728099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82376278305730642542485399 123564417458595963813728099)
            ·
              refine ⟨185346626187893945720592149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123564417458595963813728099 185346626187893945720592149)
              ·
                refine ⟨8688123102557528705652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185346626187893945720592149 8688123102557528705652757)
                ·
                  refine ⟨407255770432384158077473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8688123102557528705652757 407255770432384158077473)
                  ·
                    rfl

theorem cell22_3569075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_3569075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569075 prefixEnd_3569075 := by exact prefixLift 3569075
  have htrace : WordTrace (prefixWord ++ tailWord_3569075) baseStart_3569075 baseEnd_3569075 := by
    simpa [prefixWord, tailWord_3569075, baseEnd_3569075] using wordTrace_append hprefix tailTrace_3569075
  have hstable : (prefixWord ++ tailWord_3569075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569075).length < 2 ^ (prefixWord ++ tailWord_3569075).sum := by decide
  have hdescent : baseEnd_3569075 < baseStart_3569075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569105 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3569105 : Nat := 118140960795 + 3569105 * 2 ^ 59
def prefixEnd_3569105 : Nat := 4983230072969 + 3 ^ 40 * 3569105 * 2
def baseEnd_3569105 : Nat := 1221777580910242395982327

theorem tailTrace_3569105 : CollatzResearch.WordTrace tailWord_3569105 prefixEnd_3569105 1221777580910242395982327 := by
  unfold tailWord_3569105
  simp only [CollatzResearch.WordTrace]
  refine ⟨130175953734749614449988769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86783969156499742966659179 130175953734749614449988769)
  ·
    refine ⟨97631965301062210837491577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130175953734749614449988769 97631965301062210837491577)
    ·
      refine ⟨73223973975796658128118683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97631965301062210837491577 73223973975796658128118683)
      ·
        refine ⟨109835960963694987192178025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73223973975796658128118683 109835960963694987192178025)
        ·
          refine ⟨82376970722771240394133519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109835960963694987192178025 82376970722771240394133519)
          ·
            refine ⟨123565456084156860591200279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82376970722771240394133519 123565456084156860591200279)
            ·
              refine ⟨185348184126235290886800419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123565456084156860591200279 185348184126235290886800419)
              ·
                refine ⟨278022276189352936330200629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185348184126235290886800419 278022276189352936330200629)
                ·
                  refine ⟨26064588392751837780956309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278022276189352936330200629 26064588392751837780956309)
                  ·
                    refine ⟨1221777580910242395982327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26064588392751837780956309 1221777580910242395982327)
                    ·
                      rfl

theorem cell22_3569105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3569105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569105 prefixEnd_3569105 := by exact prefixLift 3569105
  have htrace : WordTrace (prefixWord ++ tailWord_3569105) baseStart_3569105 baseEnd_3569105 := by
    simpa [prefixWord, tailWord_3569105, baseEnd_3569105] using wordTrace_append hprefix tailTrace_3569105
  have hstable : (prefixWord ++ tailWord_3569105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569105).length < 2 ^ (prefixWord ++ tailWord_3569105).sum := by decide
  have hdescent : baseEnd_3569105 < baseStart_3569105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569109 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 4]
def baseStart_3569109 : Nat := 118140960795 + 3569109 * 2 ^ 59
def prefixEnd_3569109 : Nat := 4983230072969 + 3 ^ 40 * 3569109 * 2
def baseEnd_3569109 : Nat := 407259650063995906294105

theorem tailTrace_3569109 : CollatzResearch.WordTrace tailWord_3569109 prefixEnd_3569109 407259650063995906294105 := by
  unfold tailWord_3569109
  simp only [CollatzResearch.WordTrace]
  refine ⟨130176099626735123133134381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86784066417823415422089587 130176099626735123133134381)
  ·
    refine ⟨48816037360025671174925393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130176099626735123133134381 48816037360025671174925393)
    ·
      refine ⟨36612028020019253381194045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48816037360025671174925393 36612028020019253381194045)
      ·
        refine ⟨13729510507507220017947767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36612028020019253381194045 13729510507507220017947767)
        ·
          refine ⟨20594265761260830026921651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13729510507507220017947767 20594265761260830026921651)
          ·
            refine ⟨30891398641891245040382477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20594265761260830026921651 30891398641891245040382477)
            ·
              refine ⟨11584274490709216890143429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30891398641891245040382477 11584274490709216890143429)
              ·
                refine ⟨2172051467007978166901893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11584274490709216890143429 2172051467007978166901893)
                ·
                  refine ⟨407259650063995906294105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172051467007978166901893 407259650063995906294105)
                  ·
                    rfl

theorem cell22_3569109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_3569109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569109 prefixEnd_3569109 := by exact prefixLift 3569109
  have htrace : WordTrace (prefixWord ++ tailWord_3569109) baseStart_3569109 baseEnd_3569109 := by
    simpa [prefixWord, tailWord_3569109, baseEnd_3569109] using wordTrace_append hprefix tailTrace_3569109
  have hstable : (prefixWord ++ tailWord_3569109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569109).length < 2 ^ (prefixWord ++ tailWord_3569109).sum := by decide
  have hdescent : baseEnd_3569109 < baseStart_3569109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569120 : List Nat := [2, 1, 1, 3, 1, 1, 2, 11]
def baseStart_3569120 : Nat := 118140960795 + 3569120 * 2 ^ 59
def prefixEnd_3569120 : Nat := 4983230072969 + 3 ^ 40 * 3569120 * 2
def baseEnd_3569120 : Nat := 135753635079643039650809

theorem tailTrace_3569120 : CollatzResearch.WordTrace tailWord_3569120 prefixEnd_3569120 135753635079643039650809 := by
  unfold tailWord_3569120
  simp only [CollatzResearch.WordTrace]
  refine ⟨65088250414847636005892407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86784333886463514674523209 65088250414847636005892407)
  ·
    refine ⟨97632375622271454008838611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65088250414847636005892407 97632375622271454008838611)
    ·
      refine ⟨146448563433407181013257917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97632375622271454008838611 146448563433407181013257917)
      ·
        refine ⟨54918211287527692879971719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146448563433407181013257917 54918211287527692879971719)
        ·
          refine ⟨82377316931291539319957579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54918211287527692879971719 82377316931291539319957579)
          ·
            refine ⟨123565975396937308979936369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82377316931291539319957579 123565975396937308979936369)
            ·
              refine ⟨92674481547702981734952277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123565975396937308979936369 92674481547702981734952277)
              ·
                refine ⟨135753635079643039650809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92674481547702981734952277 135753635079643039650809)
                ·
                  rfl

theorem cell22_3569120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_3569120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569120 prefixEnd_3569120 := by exact prefixLift 3569120
  have htrace : WordTrace (prefixWord ++ tailWord_3569120) baseStart_3569120 baseEnd_3569120 := by
    simpa [prefixWord, tailWord_3569120, baseEnd_3569120] using wordTrace_append hprefix tailTrace_3569120
  have hstable : (prefixWord ++ tailWord_3569120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569120).length < 2 ^ (prefixWord ++ tailWord_3569120).sum := by decide
  have hdescent : baseEnd_3569120 < baseStart_3569120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569154 : List Nat := [3, 4, 1, 2, 1, 2, 9]
def baseStart_3569154 : Nat := 118140960795 + 3569154 * 2 ^ 59
def prefixEnd_3569154 : Nat := 4983230072969 + 3 ^ 40 * 3569154 * 2
def baseEnd_3569154 : Nat := 45251642763393429685451

theorem tailTrace_3569154 : CollatzResearch.WordTrace tailWord_3569154 prefixEnd_3569154 45251642763393429685451 := by
  unfold tailWord_3569154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32544435227893023954630629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86785160607714730545681677 32544435227893023954630629)
  ·
    refine ⟨6102081605229941991493243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32544435227893023954630629 6102081605229941991493243)
    ·
      refine ⟨9153122407844912987239865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6102081605229941991493243 9153122407844912987239865)
      ·
        refine ⟨6864841805883684740429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9153122407844912987239865 6864841805883684740429899)
        ·
          refine ⟨10297262708825527110644849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864841805883684740429899 10297262708825527110644849)
          ·
            refine ⟨7722947031619145332983637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10297262708825527110644849 7722947031619145332983637)
            ·
              refine ⟨45251642763393429685451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7722947031619145332983637 45251642763393429685451)
              ·
                rfl

theorem cell22_3569154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 9].length) (baseStart_3569154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569154 prefixEnd_3569154 := by exact prefixLift 3569154
  have htrace : WordTrace (prefixWord ++ tailWord_3569154) baseStart_3569154 baseEnd_3569154 := by
    simpa [prefixWord, tailWord_3569154, baseEnd_3569154] using wordTrace_append hprefix tailTrace_3569154
  have hstable : (prefixWord ++ tailWord_3569154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569154).length < 2 ^ (prefixWord ++ tailWord_3569154).sum := by decide
  have hdescent : baseEnd_3569154 < baseStart_3569154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569169 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3569169 : Nat := 118140960795 + 3569169 * 2 ^ 59
def prefixEnd_3569169 : Nat := 4983230072969 + 3 ^ 40 * 3569169 * 2
def baseEnd_3569169 : Nat := 1221799489418167562382131

theorem tailTrace_3569169 : CollatzResearch.WordTrace tailWord_3569169 prefixEnd_3569169 1221799489418167562382131 := by
  unfold tailWord_3569169
  simp only [CollatzResearch.WordTrace]
  refine ⟨130178288006517753380318561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86785525337678502253545707 130178288006517753380318561)
  ·
    refine ⟨97633716004888315035238921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130178288006517753380318561 97633716004888315035238921)
    ·
      refine ⟨73225287003666236276429191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97633716004888315035238921 73225287003666236276429191)
      ·
        refine ⟨109837930505499354414643787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73225287003666236276429191 109837930505499354414643787)
        ·
          refine ⟨164756895758249031621965681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109837930505499354414643787 164756895758249031621965681)
          ·
            refine ⟨123567671818686773716474261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164756895758249031621965681 123567671818686773716474261)
            ·
              refine ⟨5792234616500942517959731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123567671818686773716474261 5792234616500942517959731)
              ·
                refine ⟨8688351924751413776939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792234616500942517959731 8688351924751413776939597)
                ·
                  refine ⟨3258131971781780166352349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8688351924751413776939597 3258131971781780166352349)
                  ·
                    refine ⟨1221799489418167562382131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258131971781780166352349 1221799489418167562382131)
                    ·
                      rfl

theorem cell22_3569169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3569169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569169 prefixEnd_3569169 := by exact prefixLift 3569169
  have htrace : WordTrace (prefixWord ++ tailWord_3569169) baseStart_3569169 baseEnd_3569169 := by
    simpa [prefixWord, tailWord_3569169, baseEnd_3569169] using wordTrace_append hprefix tailTrace_3569169
  have hstable : (prefixWord ++ tailWord_3569169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569169).length < 2 ^ (prefixWord ++ tailWord_3569169).sum := by decide
  have hdescent : baseEnd_3569169 < baseStart_3569169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569203 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 1, 3]
def baseStart_3569203 : Nat := 118140960795 + 3569203 * 2 ^ 59
def prefixEnd_3569203 : Nat := 4983230072969 + 3 ^ 40 * 3569203 * 2
def baseEnd_3569203 : Nat := 1221811128313002807032027

theorem tailTrace_3569203 : CollatzResearch.WordTrace tailWord_3569203 prefixEnd_3569203 1221811128313002807032027 := by
  unfold tailWord_3569203
  simp only [CollatzResearch.WordTrace]
  refine ⟨130179528088394577187056263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86786352058929718124704175 130179528088394577187056263)
  ·
    refine ⟨195269292132591865780584395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130179528088394577187056263 195269292132591865780584395)
    ·
      refine ⟨292903938198887798670876593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195269292132591865780584395 292903938198887798670876593)
      ·
        refine ⟨219677953649165849003157445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292903938198887798670876593 219677953649165849003157445)
        ·
          refine ⟨41189616309218596688092021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219677953649165849003157445 41189616309218596688092021)
          ·
            refine ⟨3861526528989243439508627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41189616309218596688092021 3861526528989243439508627)
            ·
              refine ⟨5792289793483865159262941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861526528989243439508627 5792289793483865159262941)
              ·
                refine ⟨2172108672556449434723603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5792289793483865159262941 2172108672556449434723603)
                ·
                  refine ⟨3258163008834674152085405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172108672556449434723603 3258163008834674152085405)
                  ·
                    refine ⟨1221811128313002807032027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258163008834674152085405 1221811128313002807032027)
                    ·
                      rfl

theorem cell22_3569203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 3].length) (baseStart_3569203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569203 prefixEnd_3569203 := by exact prefixLift 3569203
  have htrace : WordTrace (prefixWord ++ tailWord_3569203) baseStart_3569203 baseEnd_3569203 := by
    simpa [prefixWord, tailWord_3569203, baseEnd_3569203] using wordTrace_append hprefix tailTrace_3569203
  have hstable : (prefixWord ++ tailWord_3569203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569203).length < 2 ^ (prefixWord ++ tailWord_3569203).sum := by decide
  have hdescent : baseEnd_3569203 < baseStart_3569203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569242 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3569242 : Nat := 118140960795 + 3569242 * 2 ^ 59
def prefixEnd_3569242 : Nat := 4983230072969 + 3 ^ 40 * 3569242 * 2
def baseEnd_3569242 : Nat := 1221824478810019705306907

theorem tailTrace_3569242 : CollatzResearch.WordTrace tailWord_3569242 prefixEnd_3569242 1221824478810019705306907 := by
  unfold tailWord_3569242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545237633813321711931495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86787300356835524565150653 32545237633813321711931495)
  ·
    refine ⟨48817856450719982567897243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32545237633813321711931495 48817856450719982567897243)
    ·
      refine ⟨73226784676079973851845865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48817856450719982567897243 73226784676079973851845865)
      ·
        refine ⟨54920088507059980388884399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73226784676079973851845865 54920088507059980388884399)
        ·
          refine ⟨82380132760589970583326599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54920088507059980388884399 82380132760589970583326599)
          ·
            refine ⟨123570199140884955874989899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82380132760589970583326599 123570199140884955874989899)
            ·
              refine ⟨185355298711327433812484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123570199140884955874989899 185355298711327433812484849)
              ·
                refine ⟨139016474033495575359363637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185355298711327433812484849 139016474033495575359363637)
                ·
                  refine ⟨13032794440640210189940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139016474033495575359363637 13032794440640210189940341)
                  ·
                    refine ⟨1221824478810019705306907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13032794440640210189940341 1221824478810019705306907)
                    ·
                      rfl

theorem cell22_3569242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3569242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569242 prefixEnd_3569242 := by exact prefixLift 3569242
  have htrace : WordTrace (prefixWord ++ tailWord_3569242) baseStart_3569242 baseEnd_3569242 := by
    simpa [prefixWord, tailWord_3569242, baseEnd_3569242] using wordTrace_append hprefix tailTrace_3569242
  have hstable : (prefixWord ++ tailWord_3569242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569242).length < 2 ^ (prefixWord ++ tailWord_3569242).sum := by decide
  have hdescent : baseEnd_3569242 < baseStart_3569242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569257 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_3569257 : Nat := 118140960795 + 3569257 * 2 ^ 59
def prefixEnd_3569257 : Nat := 4983230072969 + 3 ^ 40 * 3569257 * 2
def baseEnd_3569257 : Nat := 1221829613616564666181861

theorem tailTrace_3569257 : CollatzResearch.WordTrace tailWord_3569257 prefixEnd_3569257 1221829613616564666181861 := by
  unfold tailWord_3569257
  simp only [CollatzResearch.WordTrace]
  refine ⟨130181497630198944409522025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86787665086799296273014683 130181497630198944409522025)
  ·
    refine ⟨97636123222649208307141519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130181497630198944409522025 97636123222649208307141519)
    ·
      refine ⟨146454184833973812460712279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97636123222649208307141519 146454184833973812460712279)
      ·
        refine ⟨219681277250960718691068419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146454184833973812460712279 219681277250960718691068419)
        ·
          refine ⟨329521915876441078036602629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219681277250960718691068419 329521915876441078036602629)
          ·
            refine ⟨61785359226832702131862993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 329521915876441078036602629 61785359226832702131862993)
            ·
              refine ⟨46339019420124526598897245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61785359226832702131862993 46339019420124526598897245)
              ·
                refine ⟨17377132282546697474586467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46339019420124526598897245 17377132282546697474586467)
                ·
                  refine ⟨26065698423820046211879701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17377132282546697474586467 26065698423820046211879701)
                  ·
                    refine ⟨1221829613616564666181861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26065698423820046211879701 1221829613616564666181861)
                    ·
                      rfl

theorem cell22_3569257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_3569257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569257 prefixEnd_3569257 := by exact prefixLift 3569257
  have htrace : WordTrace (prefixWord ++ tailWord_3569257) baseStart_3569257 baseEnd_3569257 := by
    simpa [prefixWord, tailWord_3569257, baseEnd_3569257] using wordTrace_append hprefix tailTrace_3569257
  have hstable : (prefixWord ++ tailWord_3569257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569257).length < 2 ^ (prefixWord ++ tailWord_3569257).sum := by decide
  have hdescent : baseEnd_3569257 < baseStart_3569257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569308 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3569308 : Nat := 118140960795 + 3569308 * 2 ^ 59
def prefixEnd_3569308 : Nat := 4983230072969 + 3 ^ 40 * 3569308 * 2
def baseEnd_3569308 : Nat := 1221847071958817533156705

theorem tailTrace_3569308 : CollatzResearch.WordTrace tailWord_3569308 prefixEnd_3569308 1221847071958817533156705 := by
  unfold tailWord_3569308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65091678876507090059814289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86788905168676120079752385 65091678876507090059814289)
  ·
    refine ⟨48818759157380317544860717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65091678876507090059814289 48818759157380317544860717)
    ·
      refine ⟨18307034684017619079322769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48818759157380317544860717 18307034684017619079322769)
      ·
        refine ⟨13730276013013214309492077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18307034684017619079322769 13730276013013214309492077)
        ·
          refine ⟨5148853504879955366059529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13730276013013214309492077 5148853504879955366059529)
          ·
            refine ⟨3861640128659966524544647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5148853504879955366059529 3861640128659966524544647)
            ·
              refine ⟨5792460192989949786816971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861640128659966524544647 5792460192989949786816971)
              ·
                refine ⟨8688690289484924680225457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792460192989949786816971 8688690289484924680225457)
                ·
                  refine ⟨6516517717113693510169093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8688690289484924680225457 6516517717113693510169093)
                  ·
                    refine ⟨1221847071958817533156705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516517717113693510169093 1221847071958817533156705)
                    ·
                      rfl

theorem cell22_3569308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3569308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569308 prefixEnd_3569308 := by exact prefixLift 3569308
  have htrace : WordTrace (prefixWord ++ tailWord_3569308) baseStart_3569308 baseEnd_3569308 := by
    simpa [prefixWord, tailWord_3569308, baseEnd_3569308] using wordTrace_append hprefix tailTrace_3569308
  have hstable : (prefixWord ++ tailWord_3569308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569308).length < 2 ^ (prefixWord ++ tailWord_3569308).sum := by decide
  have hdescent : baseEnd_3569308 < baseStart_3569308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569338 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_3569338 : Nat := 118140960795 + 3569338 * 2 ^ 59
def prefixEnd_3569338 : Nat := 4983230072969 + 3 ^ 40 * 3569338 * 2
def baseEnd_3569338 : Nat := 1221857341571907454906613

theorem tailTrace_3569338 : CollatzResearch.WordTrace tailWord_3569338 prefixEnd_3569338 1221857341571907454906613 := by
  unfold tailWord_3569338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546112985726373810805167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86789634628603663495480445 32546112985726373810805167)
  ·
    refine ⟨48819169478589560716207751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32546112985726373810805167 48819169478589560716207751)
    ·
      refine ⟨73228754217884341074311627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48819169478589560716207751 73228754217884341074311627)
      ·
        refine ⟨109843131326826511611467441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73228754217884341074311627 109843131326826511611467441)
        ·
          refine ⟨82382348495119883708600581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109843131326826511611467441 82382348495119883708600581)
          ·
            refine ⟨15446690342834978195362609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82382348495119883708600581 15446690342834978195362609)
            ·
              refine ⟨11585017757126233646521957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15446690342834978195362609 11585017757126233646521957)
              ·
                refine ⟨2172190829461168808722867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11585017757126233646521957 2172190829461168808722867)
                ·
                  refine ⟨3258286244191753213084301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172190829461168808722867 3258286244191753213084301)
                  ·
                    refine ⟨1221857341571907454906613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258286244191753213084301 1221857341571907454906613)
                    ·
                      rfl

theorem cell22_3569338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_3569338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569338 prefixEnd_3569338 := by exact prefixLift 3569338
  have htrace : WordTrace (prefixWord ++ tailWord_3569338) baseStart_3569338 baseEnd_3569338 := by
    simpa [prefixWord, tailWord_3569338, baseEnd_3569338] using wordTrace_append hprefix tailTrace_3569338
  have hstable : (prefixWord ++ tailWord_3569338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569338).length < 2 ^ (prefixWord ++ tailWord_3569338).sum := by decide
  have hdescent : baseEnd_3569338 < baseStart_3569338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569351 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 5]
def baseStart_3569351 : Nat := 118140960795 + 3569351 * 2 ^ 59
def prefixEnd_3569351 : Nat := 4983230072969 + 3 ^ 40 * 3569351 * 2
def baseEnd_3569351 : Nat := 407287263912526584777191

theorem tailTrace_3569351 : CollatzResearch.WordTrace tailWord_3569351 prefixEnd_3569351 407287263912526584777191 := by
  unfold tailWord_3569351
  simp only [CollatzResearch.WordTrace]
  refine ⟨130184926091858398463443907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86789950727905598975629271 130184926091858398463443907)
  ·
    refine ⟨195277389137787597695165861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130184926091858398463443907 195277389137787597695165861)
    ·
      refine ⟨36614510463335174567843599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195277389137787597695165861 36614510463335174567843599)
      ·
        refine ⟨54921765695002761851765399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36614510463335174567843599 54921765695002761851765399)
        ·
          refine ⟨82382648542504142777648099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54921765695002761851765399 82382648542504142777648099)
          ·
            refine ⟨123573972813756214166472149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82382648542504142777648099 123573972813756214166472149)
            ·
              refine ⟨2896264987822411269526691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123573972813756214166472149 2896264987822411269526691)
              ·
                refine ⟨4344397481733616904290037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896264987822411269526691 4344397481733616904290037)
                ·
                  refine ⟨407287263912526584777191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344397481733616904290037 407287263912526584777191)
                  ·
                    rfl

theorem cell22_3569351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 5].length) (baseStart_3569351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569351 prefixEnd_3569351 := by exact prefixLift 3569351
  have htrace : WordTrace (prefixWord ++ tailWord_3569351) baseStart_3569351 baseEnd_3569351 := by
    simpa [prefixWord, tailWord_3569351, baseEnd_3569351] using wordTrace_append hprefix tailTrace_3569351
  have hstable : (prefixWord ++ tailWord_3569351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569351).length < 2 ^ (prefixWord ++ tailWord_3569351).sum := by decide
  have hdescent : baseEnd_3569351 < baseStart_3569351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569381 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_3569381 : Nat := 118140960795 + 3569381 * 2 ^ 59
def prefixEnd_3569381 : Nat := 4983230072969 + 3 ^ 40 * 3569381 * 2
def baseEnd_3569381 : Nat := 1221872061350669676081481

theorem tailTrace_3569381 : CollatzResearch.WordTrace tailWord_3569381 prefixEnd_3569381 1221872061350669676081481 := by
  unfold tailWord_3569381
  simp only [CollatzResearch.WordTrace]
  refine ⟨130186020281749713587035997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86790680187833142391357331 130186020281749713587035997)
  ·
    refine ⟨48819757605656142595138499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130186020281749713587035997 48819757605656142595138499)
    ·
      refine ⟨73229636408484213892707749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48819757605656142595138499 73229636408484213892707749)
      ·
        refine ⟨13730556826590790104882703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73229636408484213892707749 13730556826590790104882703)
        ·
          refine ⟨20595835239886185157324055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13730556826590790104882703 20595835239886185157324055)
          ·
            refine ⟨30893752859829277735986083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20595835239886185157324055 30893752859829277735986083)
            ·
              refine ⟨46340629289743916603979125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30893752859829277735986083 46340629289743916603979125)
              ·
                refine ⟨4344433995913492181623043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46340629289743916603979125 4344433995913492181623043)
                ·
                  refine ⟨6516650993870238272434565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344433995913492181623043 6516650993870238272434565)
                  ·
                    refine ⟨1221872061350669676081481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516650993870238272434565 1221872061350669676081481)
                    ·
                      rfl

theorem cell22_3569381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_3569381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569381 prefixEnd_3569381 := by exact prefixLift 3569381
  have htrace : WordTrace (prefixWord ++ tailWord_3569381) baseStart_3569381 baseEnd_3569381 := by
    simpa [prefixWord, tailWord_3569381, baseEnd_3569381] using wordTrace_append hprefix tailTrace_3569381
  have hstable : (prefixWord ++ tailWord_3569381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569381).length < 2 ^ (prefixWord ++ tailWord_3569381).sum := by decide
  have hdescent : baseEnd_3569381 < baseStart_3569381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569409 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3569409 : Nat := 118140960795 + 3569409 * 2 ^ 59
def prefixEnd_3569409 : Nat := 4983230072969 + 3 ^ 40 * 3569409 * 2
def baseEnd_3569409 : Nat := 1221881646322886936381395

theorem tailTrace_3569409 : CollatzResearch.WordTrace tailWord_3569409 prefixEnd_3569409 1221881646322886936381395 := by
  unfold tailWord_3569409
  simp only [CollatzResearch.WordTrace]
  refine ⟨130187041525648274369055281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86791361017098849579370187 130187041525648274369055281)
  ·
    refine ⟨97640281144236205776791461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130187041525648274369055281 97640281144236205776791461)
    ·
      refine ⟨18307552714544288583148399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97640281144236205776791461 18307552714544288583148399)
      ·
        refine ⟨27461329071816432874722599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307552714544288583148399 27461329071816432874722599)
        ·
          refine ⟨41191993607724649312083899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27461329071816432874722599 41191993607724649312083899)
          ·
            refine ⟨61787990411586973968125849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41191993607724649312083899 61787990411586973968125849)
            ·
              refine ⟨46340992808690230476094387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61787990411586973968125849 46340992808690230476094387)
              ·
                refine ⟨69511489213035345714141581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46340992808690230476094387 69511489213035345714141581)
                ·
                  refine ⟨26066808454888254642803093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69511489213035345714141581 26066808454888254642803093)
                  ·
                    refine ⟨1221881646322886936381395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26066808454888254642803093 1221881646322886936381395)
                    ·
                      rfl

theorem cell22_3569409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3569409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569409 prefixEnd_3569409 := by exact prefixLift 3569409
  have htrace : WordTrace (prefixWord ++ tailWord_3569409) baseStart_3569409 baseEnd_3569409 := by
    simpa [prefixWord, tailWord_3569409, baseEnd_3569409] using wordTrace_append hprefix tailTrace_3569409
  have hstable : (prefixWord ++ tailWord_3569409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569409).length < 2 ^ (prefixWord ++ tailWord_3569409).sum := by decide
  have hdescent : baseEnd_3569409 < baseStart_3569409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569415 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3569415 : Nat := 118140960795 + 3569415 * 2 ^ 59
def prefixEnd_3569415 : Nat := 4983230072969 + 3 ^ 40 * 3569415 * 2
def baseEnd_3569415 : Nat := 1221883700245504920731377

theorem tailTrace_3569415 : CollatzResearch.WordTrace tailWord_3569415 prefixEnd_3569415 1221883700245504920731377 := by
  unfold tailWord_3569415
  simp only [CollatzResearch.WordTrace]
  refine ⟨130187260363626537393773699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86791506909084358262515799 130187260363626537393773699)
  ·
    refine ⟨195280890545439806090660549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130187260363626537393773699 195280890545439806090660549)
    ·
      refine ⟨36615166977269963641998853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195280890545439806090660549 36615166977269963641998853)
      ·
        refine ⟨6865343808238118182874785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36615166977269963641998853 6865343808238118182874785)
        ·
          refine ⟨5149007856178588637156089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865343808238118182874785 5149007856178588637156089)
          ·
            refine ⟨3861755892133941477867067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149007856178588637156089 3861755892133941477867067)
            ·
              refine ⟨5792633838200912216800601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861755892133941477867067 5792633838200912216800601)
              ·
                refine ⟨4344475378650684162600451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792633838200912216800601 4344475378650684162600451)
                ·
                  refine ⟨6516713067976026243900677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344475378650684162600451 6516713067976026243900677)
                  ·
                    refine ⟨1221883700245504920731377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516713067976026243900677 1221883700245504920731377)
                    ·
                      rfl

theorem cell22_3569415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3569415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569415 prefixEnd_3569415 := by exact prefixLift 3569415
  have htrace : WordTrace (prefixWord ++ tailWord_3569415) baseStart_3569415 baseEnd_3569415 := by
    simpa [prefixWord, tailWord_3569415, baseEnd_3569415] using wordTrace_append hprefix tailTrace_3569415
  have hstable : (prefixWord ++ tailWord_3569415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569415).length < 2 ^ (prefixWord ++ tailWord_3569415).sum := by decide
  have hdescent : baseEnd_3569415 < baseStart_3569415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569490 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_3569490 : Nat := 118140960795 + 3569490 * 2 ^ 59
def prefixEnd_3569490 : Nat := 4983230072969 + 3 ^ 40 * 3569490 * 2
def baseEnd_3569490 : Nat := 1221909374278229725106147

theorem tailTrace_3569490 : CollatzResearch.WordTrace tailWord_3569490 prefixEnd_3569490 1221909374278229725106147 := by
  unfold tailWord_3569490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547498959588706300688481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86793330558903216801835949 32547498959588706300688481)
  ·
    refine ⟨24410624219691529725516361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32547498959588706300688481 24410624219691529725516361)
    ·
      refine ⟨18307968164768647294137271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24410624219691529725516361 18307968164768647294137271)
      ·
        refine ⟨27461952247152970941205907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307968164768647294137271 27461952247152970941205907)
        ·
          refine ⟨41192928370729456411808861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27461952247152970941205907 41192928370729456411808861)
          ·
            refine ⟨15447348139023546154428323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41192928370729456411808861 15447348139023546154428323)
            ·
              refine ⟨23171022208535319231642485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15447348139023546154428323 23171022208535319231642485)
              ·
                refine ⟨2172283332050186177966483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23171022208535319231642485 2172283332050186177966483)
                ·
                  refine ⟨3258424998075279266949725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172283332050186177966483 3258424998075279266949725)
                  ·
                    refine ⟨1221909374278229725106147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258424998075279266949725 1221909374278229725106147)
                    ·
                      rfl

theorem cell22_3569490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_3569490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569490 prefixEnd_3569490 := by exact prefixLift 3569490
  have htrace : WordTrace (prefixWord ++ tailWord_3569490) baseStart_3569490 baseEnd_3569490 := by
    simpa [prefixWord, tailWord_3569490, baseEnd_3569490] using wordTrace_append hprefix tailTrace_3569490
  have hstable : (prefixWord ++ tailWord_3569490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569490).length < 2 ^ (prefixWord ++ tailWord_3569490).sum := by decide
  have hdescent : baseEnd_3569490 < baseStart_3569490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569503 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 5]
def baseStart_3569503 : Nat := 118140960795 + 3569503 * 2 ^ 59
def prefixEnd_3569503 : Nat := 4983230072969 + 3 ^ 40 * 3569503 * 2
def baseEnd_3569503 : Nat := 407304608147967341510369

theorem tailTrace_3569503 : CollatzResearch.WordTrace tailWord_3569503 prefixEnd_3569503 407304608147967341510369 := by
  unfold tailWord_3569503
  simp only [CollatzResearch.WordTrace]
  refine ⟨130190469987307728422977163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86793646658205152281984775 130190469987307728422977163)
  ·
    refine ⟨195285704980961592634465745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130190469987307728422977163 195285704980961592634465745)
    ·
      refine ⟨146464278735721194475849309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195285704980961592634465745 146464278735721194475849309)
      ·
        refine ⟨54924104525895447928443491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146464278735721194475849309 54924104525895447928443491)
        ·
          refine ⟨82386156788843171892665237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54924104525895447928443491 82386156788843171892665237)
          ·
            refine ⟨3861851099477023682468683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82386156788843171892665237 3861851099477023682468683)
            ·
              refine ⟨5792776649215535523703025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861851099477023682468683 5792776649215535523703025)
              ·
                refine ⟨4344582486911651642777269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792776649215535523703025 4344582486911651642777269)
                ·
                  refine ⟨407304608147967341510369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4344582486911651642777269 407304608147967341510369)
                  ·
                    rfl

theorem cell22_3569503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 5].length) (baseStart_3569503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569503 prefixEnd_3569503 := by exact prefixLift 3569503
  have htrace : WordTrace (prefixWord ++ tailWord_3569503) baseStart_3569503 baseEnd_3569503 := by
    simpa [prefixWord, tailWord_3569503, baseEnd_3569503] using wordTrace_append hprefix tailTrace_3569503
  have hstable : (prefixWord ++ tailWord_3569503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569503).length < 2 ^ (prefixWord ++ tailWord_3569503).sum := by decide
  have hdescent : baseEnd_3569503 < baseStart_3569503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569518 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3569518 : Nat := 118140960795 + 3569518 * 2 ^ 59
def prefixEnd_3569518 : Nat := 4983230072969 + 3 ^ 40 * 3569518 * 2
def baseEnd_3569518 : Nat := 1221918959250446985406061

theorem tailTrace_3569518 : CollatzResearch.WordTrace tailWord_3569518 prefixEnd_3569518 1221918959250446985406061 := by
  unfold tailWord_3569518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273877135281673248096651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86794011388168923989848805 16273877135281673248096651)
  ·
    refine ⟨24410815702922509872144977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16273877135281673248096651 24410815702922509872144977)
    ·
      refine ⟨18308111777191882404108733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24410815702922509872144977 18308111777191882404108733)
      ·
        refine ⟨6865541916446955901540775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18308111777191882404108733 6865541916446955901540775)
        ·
          refine ⟨10298312874670433852311163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865541916446955901540775 10298312874670433852311163)
          ·
            refine ⟨15447469312005650778466745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298312874670433852311163 15447469312005650778466745)
            ·
              refine ⟨11585601984004238083850059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15447469312005650778466745 11585601984004238083850059)
              ·
                refine ⟨17378402976006357125775089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11585601984004238083850059 17378402976006357125775089)
                ·
                  refine ⟨13033802232004767844331317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17378402976006357125775089 13033802232004767844331317)
                  ·
                    refine ⟨1221918959250446985406061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13033802232004767844331317 1221918959250446985406061)
                    ·
                      rfl

theorem cell22_3569518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3569518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569518 prefixEnd_3569518 := by exact prefixLift 3569518
  have htrace : WordTrace (prefixWord ++ tailWord_3569518) baseStart_3569518 baseEnd_3569518 := by
    simpa [prefixWord, tailWord_3569518, baseEnd_3569518] using wordTrace_append hprefix tailTrace_3569518
  have hstable : (prefixWord ++ tailWord_3569518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569518).length < 2 ^ (prefixWord ++ tailWord_3569518).sum := by decide
  have hdescent : baseEnd_3569518 < baseStart_3569518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569558 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3569558 : Nat := 118140960795 + 3569558 * 2 ^ 59
def prefixEnd_3569558 : Nat := 4983230072969 + 3 ^ 40 * 3569558 * 2
def baseEnd_3569558 : Nat := 1221932652067900214405939

theorem tailTrace_3569558 : CollatzResearch.WordTrace tailWord_3569558 prefixEnd_3569558 1221932652067900214405939 := by
  unfold tailWord_3569558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137029750131779551014333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86794984001405648544152885 8137029750131779551014333)
  ·
    refine ⟨3051386156299417331630375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8137029750131779551014333 3051386156299417331630375)
    ·
      refine ⟨4577079234449125997445563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051386156299417331630375 4577079234449125997445563)
      ·
        refine ⟨6865618851673688996168345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577079234449125997445563 6865618851673688996168345)
        ·
          refine ⟨5149214138755266747126259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865618851673688996168345 5149214138755266747126259)
          ·
            refine ⟨7723821208132900120689389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149214138755266747126259 7723821208132900120689389)
            ·
              refine ⟨2896432953049837545258521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7723821208132900120689389 2896432953049837545258521)
              ·
                refine ⟨2172324714787378158943891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896432953049837545258521 2172324714787378158943891)
                ·
                  refine ⟨3258487072181067238415837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172324714787378158943891 3258487072181067238415837)
                  ·
                    refine ⟨1221932652067900214405939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258487072181067238415837 1221932652067900214405939)
                    ·
                      rfl

theorem cell22_3569558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3569558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569558 prefixEnd_3569558 := by exact prefixLift 3569558
  have htrace : WordTrace (prefixWord ++ tailWord_3569558) baseStart_3569558 baseEnd_3569558 := by
    simpa [prefixWord, tailWord_3569558, baseEnd_3569558] using wordTrace_append hprefix tailTrace_3569558
  have hstable : (prefixWord ++ tailWord_3569558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569558).length < 2 ^ (prefixWord ++ tailWord_3569558).sum := by decide
  have hdescent : baseEnd_3569558 < baseStart_3569558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569561 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_3569561 : Nat := 118140960795 + 3569561 * 2 ^ 59
def prefixEnd_3569561 : Nat := 4983230072969 + 3 ^ 40 * 3569561 * 2
def baseEnd_3569561 : Nat := 1221933679029209206580929

theorem tailTrace_3569561 : CollatzResearch.WordTrace tailWord_3569561 prefixEnd_3569561 1221933679029209206580929 := by
  unfold tailWord_3569561
  simp only [CollatzResearch.WordTrace]
  refine ⟨130192585421097604328588537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86795056947398402885725691 130192585421097604328588537)
  ·
    refine ⟨97644439065823203246441403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130192585421097604328588537 97644439065823203246441403)
    ·
      refine ⟨146466658598734804869662105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97644439065823203246441403 146466658598734804869662105)
      ·
        refine ⟨109849993949051103652246579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146466658598734804869662105 109849993949051103652246579)
        ·
          refine ⟨164774990923576655478369869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109849993949051103652246579 164774990923576655478369869)
          ·
            refine ⟨61790621596341245804388701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164774990923576655478369869 61790621596341245804388701)
            ·
              refine ⟨23171483098627967176645763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61790621596341245804388701 23171483098627967176645763)
              ·
                refine ⟨34757224647941950764968645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23171483098627967176645763 34757224647941950764968645)
                ·
                  refine ⟨6516979621489115768431621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34757224647941950764968645 6516979621489115768431621)
                  ·
                    refine ⟨1221933679029209206580929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6516979621489115768431621 1221933679029209206580929)
                    ·
                      rfl

theorem cell22_3569561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_3569561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569561 prefixEnd_3569561 := by exact prefixLift 3569561
  have htrace : WordTrace (prefixWord ++ tailWord_3569561) baseStart_3569561 baseEnd_3569561 := by
    simpa [prefixWord, tailWord_3569561, baseEnd_3569561] using wordTrace_append hprefix tailTrace_3569561
  have hstable : (prefixWord ++ tailWord_3569561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569561).length < 2 ^ (prefixWord ++ tailWord_3569561).sum := by decide
  have hdescent : baseEnd_3569561 < baseStart_3569561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569681 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3569681 : Nat := 118140960795 + 3569681 * 2 ^ 59
def prefixEnd_3569681 : Nat := 4983230072969 + 3 ^ 40 * 3569681 * 2
def baseEnd_3569681 : Nat := 1221974757481568893580561

theorem tailTrace_3569681 : CollatzResearch.WordTrace tailWord_3569681 prefixEnd_3569681 1221974757481568893580561 := by
  unfold tailWord_3569681
  simp only [CollatzResearch.WordTrace]
  refine ⟨130196962180662864822956897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86797974787108576548637931 130196962180662864822956897)
  ·
    refine ⟨97647721635497148617217673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130196962180662864822956897 97647721635497148617217673)
    ·
      refine ⟨73235791226622861462913255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97647721635497148617217673 73235791226622861462913255)
      ·
        refine ⟨109853686839934292194369883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73235791226622861462913255 109853686839934292194369883)
        ·
          refine ⟨164780530259901438291554825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109853686839934292194369883 164780530259901438291554825)
          ·
            refine ⟨123585397694926078718666119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164780530259901438291554825 123585397694926078718666119)
            ·
              refine ⟨185378096542389118077999179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123585397694926078718666119 185378096542389118077999179)
              ·
                refine ⟨278067144813583677116998769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185378096542389118077999179 278067144813583677116998769)
                ·
                  refine ⟨208550358610187757837749077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278067144813583677116998769 208550358610187757837749077)
                  ·
                    refine ⟨1221974757481568893580561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208550358610187757837749077 1221974757481568893580561)
                    ·
                      rfl

theorem cell22_3569681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3569681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569681 prefixEnd_3569681 := by exact prefixLift 3569681
  have htrace : WordTrace (prefixWord ++ tailWord_3569681) baseStart_3569681 baseEnd_3569681 := by
    simpa [prefixWord, tailWord_3569681, baseEnd_3569681] using wordTrace_append hprefix tailTrace_3569681
  have hstable : (prefixWord ++ tailWord_3569681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569681).length < 2 ^ (prefixWord ++ tailWord_3569681).sum := by decide
  have hdescent : baseEnd_3569681 < baseStart_3569681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569713 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3569713 : Nat := 118140960795 + 3569713 * 2 ^ 59
def prefixEnd_3569713 : Nat := 4983230072969 + 3 ^ 40 * 3569713 * 2
def baseEnd_3569713 : Nat := 1221985711735531476780463

theorem tailTrace_3569713 : CollatzResearch.WordTrace tailWord_3569713 prefixEnd_3569713 1221985711735531476780463 := by
  unfold tailWord_3569713
  simp only [CollatzResearch.WordTrace]
  refine ⟨130198129316546934288121793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86798752877697956192081195 130198129316546934288121793)
  ·
    refine ⟨97648596987410200716091345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130198129316546934288121793 97648596987410200716091345)
    ·
      refine ⟨73236447740557650537068509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97648596987410200716091345 73236447740557650537068509)
      ·
        refine ⟨27463667902709118951400691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73236447740557650537068509 27463667902709118951400691)
        ·
          refine ⟨41195501854063678427101037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27463667902709118951400691 41195501854063678427101037)
          ·
            refine ⟨15448313195273879410162889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41195501854063678427101037 15448313195273879410162889)
            ·
              refine ⟨11586234896455409557622167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15448313195273879410162889 11586234896455409557622167)
              ·
                refine ⟨17379352344683114336433251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11586234896455409557622167 17379352344683114336433251)
                ·
                  refine ⟨26069028517024671504649877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17379352344683114336433251 26069028517024671504649877)
                  ·
                    refine ⟨1221985711735531476780463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26069028517024671504649877 1221985711735531476780463)
                    ·
                      rfl

theorem cell22_3569713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3569713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569713 prefixEnd_3569713 := by exact prefixLift 3569713
  have htrace : WordTrace (prefixWord ++ tailWord_3569713) baseStart_3569713 baseEnd_3569713 := by
    simpa [prefixWord, tailWord_3569713, baseEnd_3569713] using wordTrace_append hprefix tailTrace_3569713
  have hstable : (prefixWord ++ tailWord_3569713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569713).length < 2 ^ (prefixWord ++ tailWord_3569713).sum := by decide
  have hdescent : baseEnd_3569713 < baseStart_3569713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569728 : List Nat := [2, 1, 1, 2, 2, 6, 8]
def baseStart_3569728 : Nat := 118140960795 + 3569728 * 2 ^ 59
def prefixEnd_3569728 : Nat := 4983230072969 + 3 ^ 40 * 3569728 * 2
def baseEnd_3569728 : Nat := 45258920242299127320571

theorem tailTrace_3569728 : CollatzResearch.WordTrace tailWord_3569728 prefixEnd_3569728 45258920242299127320571 := by
  unfold tailWord_3569728
  simp only [CollatzResearch.WordTrace]
  refine ⟨65099338205746295924958919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86799117607661727899945225 65099338205746295924958919)
  ·
    refine ⟨97649007308619443887438379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65099338205746295924958919 97649007308619443887438379)
    ·
      refine ⟨146473510962929165831157569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97649007308619443887438379 146473510962929165831157569)
      ·
        refine ⟨109855133222196874373368177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146473510962929165831157569 109855133222196874373368177)
        ·
          refine ⟨82391349916647655780026133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109855133222196874373368177 82391349916647655780026133)
          ·
            refine ⟨3862094527342858864688725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82391349916647655780026133 3862094527342858864688725)
            ·
              refine ⟨45258920242299127320571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3862094527342858864688725 45258920242299127320571)
              ·
                rfl

theorem cell22_3569728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 8].length) (baseStart_3569728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569728 prefixEnd_3569728 := by exact prefixLift 3569728
  have htrace : WordTrace (prefixWord ++ tailWord_3569728) baseStart_3569728 baseEnd_3569728 := by
    simpa [prefixWord, tailWord_3569728, baseEnd_3569728] using wordTrace_append hprefix tailTrace_3569728
  have hstable : (prefixWord ++ tailWord_3569728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569728).length < 2 ^ (prefixWord ++ tailWord_3569728).sum := by decide
  have hdescent : baseEnd_3569728 < baseStart_3569728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569749 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3569749 : Nat := 118140960795 + 3569749 * 2 ^ 59
def prefixEnd_3569749 : Nat := 4983230072969 + 3 ^ 40 * 3569749 * 2
def baseEnd_3569749 : Nat := 1221998035271239382880353

theorem tailTrace_3569749 : CollatzResearch.WordTrace tailWord_3569749 prefixEnd_3569749 1221998035271239382880353 := by
  unfold tailWord_3569749
  simp only [CollatzResearch.WordTrace]
  refine ⟨130199442344416512436432301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86799628229611008290954867 130199442344416512436432301)
  ·
    refine ⟨48824790879156192163662113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130199442344416512436432301 48824790879156192163662113)
    ·
      refine ⟨36618593159367144122746585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48824790879156192163662113 36618593159367144122746585)
      ·
        refine ⟨27463944869525358092059939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36618593159367144122746585 27463944869525358092059939)
        ·
          refine ⟨41195917304288037138089909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27463944869525358092059939 41195917304288037138089909)
          ·
            refine ⟨3862117247277003481695929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41195917304288037138089909 3862117247277003481695929)
            ·
              refine ⟨2896587935457752611271947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862117247277003481695929 2896587935457752611271947)
              ·
                refine ⟨4344881903186628916907921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896587935457752611271947 4344881903186628916907921)
                ·
                  refine ⟨3258661427389971687680941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344881903186628916907921 3258661427389971687680941)
                  ·
                    refine ⟨1221998035271239382880353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258661427389971687680941 1221998035271239382880353)
                    ·
                      rfl

theorem cell22_3569749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3569749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569749 prefixEnd_3569749 := by exact prefixLift 3569749
  have htrace : WordTrace (prefixWord ++ tailWord_3569749) baseStart_3569749 baseEnd_3569749 := by
    simpa [prefixWord, tailWord_3569749, baseEnd_3569749] using wordTrace_append hprefix tailTrace_3569749
  have hstable : (prefixWord ++ tailWord_3569749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569749).length < 2 ^ (prefixWord ++ tailWord_3569749).sum := by decide
  have hdescent : baseEnd_3569749 < baseStart_3569749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569777 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_3569777 : Nat := 118140960795 + 3569777 * 2 ^ 59
def prefixEnd_3569777 : Nat := 4983230072969 + 3 ^ 40 * 3569777 * 2
def baseEnd_3569777 : Nat := 1222007620243456643180267

theorem tailTrace_3569777 : CollatzResearch.WordTrace tailWord_3569777 prefixEnd_3569777 1222007620243456643180267 := by
  unfold tailWord_3569777
  simp only [CollatzResearch.WordTrace]
  refine ⟨130200463588315073218451585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86800309058876715478967723 130200463588315073218451585)
  ·
    refine ⟨97650347691236304913838689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130200463588315073218451585 97650347691236304913838689)
    ·
      refine ⟨73237760768427228685379017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97650347691236304913838689 73237760768427228685379017)
      ·
        refine ⟨54928320576320421514034263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73237760768427228685379017 54928320576320421514034263)
        ·
          refine ⟨82392480864480632271051395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54928320576320421514034263 82392480864480632271051395)
          ·
            refine ⟨123588721296720948406577093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82392480864480632271051395 123588721296720948406577093)
            ·
              refine ⟨23172885243135177826233205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123588721296720948406577093 23172885243135177826233205)
              ·
                refine ⟨2172457991543922921209363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23172885243135177826233205 2172457991543922921209363)
                ·
                  refine ⟨3258686987315884381814045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172457991543922921209363 3258686987315884381814045)
                  ·
                    refine ⟨1222007620243456643180267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258686987315884381814045 1222007620243456643180267)
                    ·
                      rfl

theorem cell22_3569777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_3569777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569777 prefixEnd_3569777 := by exact prefixLift 3569777
  have htrace : WordTrace (prefixWord ++ tailWord_3569777) baseStart_3569777 baseEnd_3569777 := by
    simpa [prefixWord, tailWord_3569777, baseEnd_3569777] using wordTrace_append hprefix tailTrace_3569777
  have hstable : (prefixWord ++ tailWord_3569777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569777).length < 2 ^ (prefixWord ++ tailWord_3569777).sum := by decide
  have hdescent : baseEnd_3569777 < baseStart_3569777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569820 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3569820 : Nat := 118140960795 + 3569820 * 2 ^ 59
def prefixEnd_3569820 : Nat := 4983230072969 + 3 ^ 40 * 3569820 * 2
def baseEnd_3569820 : Nat := 1222022340022218864355135

theorem tailTrace_3569820 : CollatzResearch.WordTrace tailWord_3569820 prefixEnd_3569820 1222022340022218864355135 := by
  unfold tailWord_3569820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65101015963579645781133457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86801354618106194374844609 65101015963579645781133457)
  ·
    refine ⟨48825761972684734335850093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65101015963579645781133457 48825761972684734335850093)
    ·
      refine ⟨18309660739756775375943785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48825761972684734335850093 18309660739756775375943785)
      ·
        refine ⟨13732245554817581531957839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18309660739756775375943785 13732245554817581531957839)
        ·
          refine ⟨20598368332226372297936759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732245554817581531957839 20598368332226372297936759)
          ·
            refine ⟨30897552498339558446905139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20598368332226372297936759 30897552498339558446905139)
            ·
              refine ⟨46346328747509337670357709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30897552498339558446905139 46346328747509337670357709)
              ·
                refine ⟨17379873280316001626384141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46346328747509337670357709 17379873280316001626384141)
                ·
                  refine ⟨6517452480118500609894053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17379873280316001626384141 6517452480118500609894053)
                  ·
                    refine ⟨1222022340022218864355135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6517452480118500609894053 1222022340022218864355135)
                    ·
                      rfl

theorem cell22_3569820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3569820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569820 prefixEnd_3569820 := by exact prefixLift 3569820
  have htrace : WordTrace (prefixWord ++ tailWord_3569820) baseStart_3569820 baseEnd_3569820 := by
    simpa [prefixWord, tailWord_3569820, baseEnd_3569820] using wordTrace_append hprefix tailTrace_3569820
  have hstable : (prefixWord ++ tailWord_3569820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569820).length < 2 ^ (prefixWord ++ tailWord_3569820).sum := by decide
  have hdescent : baseEnd_3569820 < baseStart_3569820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569852 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_3569852 : Nat := 118140960795 + 3569852 * 2 ^ 59
def prefixEnd_3569852 : Nat := 4983230072969 + 3 ^ 40 * 3569852 * 2
def baseEnd_3569852 : Nat := 407344431425393815851679

theorem tailTrace_3569852 : CollatzResearch.WordTrace tailWord_3569852 prefixEnd_3569852 407344431425393815851679 := by
  unfold tailWord_3569852
  simp only [CollatzResearch.WordTrace]
  refine ⟨65101599531521680513715905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86802132708695574018287873 65101599531521680513715905)
  ·
    refine ⟨48826199648641260385286929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65101599531521680513715905 48826199648641260385286929)
    ·
      refine ⟨36619649736480945288965197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48826199648641260385286929 36619649736480945288965197)
      ·
        refine ⟨13732368651180354483361949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36619649736480945288965197 13732368651180354483361949)
        ·
          refine ⟨5149638244192632931260731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13732368651180354483361949 5149638244192632931260731)
          ·
            refine ⟨7724457366288949396891097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149638244192632931260731 7724457366288949396891097)
            ·
              refine ⟨5793343024716712047668323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724457366288949396891097 5793343024716712047668323)
              ·
                refine ⟨8690014537075068071502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793343024716712047668323 8690014537075068071502485)
                ·
                  refine ⟨407344431425393815851679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8690014537075068071502485 407344431425393815851679)
                  ·
                    rfl

theorem cell22_3569852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_3569852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569852 prefixEnd_3569852 := by exact prefixLift 3569852
  have htrace : WordTrace (prefixWord ++ tailWord_3569852) baseStart_3569852 baseEnd_3569852 := by
    simpa [prefixWord, tailWord_3569852, baseEnd_3569852] using wordTrace_append hprefix tailTrace_3569852
  have hstable : (prefixWord ++ tailWord_3569852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569852).length < 2 ^ (prefixWord ++ tailWord_3569852).sum := by decide
  have hdescent : baseEnd_3569852 < baseStart_3569852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3569880 : List Nat := [2, 1, 2, 2, 4, 2, 1, 8]
def baseStart_3569880 : Nat := 118140960795 + 3569880 * 2 ^ 59
def prefixEnd_3569880 : Nat := 4983230072969 + 3 ^ 40 * 3569880 * 2
def baseEnd_3569880 : Nat := 135782542138710967539439

theorem tailTrace_3569880 : CollatzResearch.WordTrace tailWord_3569880 prefixEnd_3569880 135782542138710967539439 := by
  unfold tailWord_3569880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65102110153470960904725547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86802813537961281206300729 65102110153470960904725547)
  ·
    refine ⟨97653165230206441357088321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65102110153470960904725547 97653165230206441357088321)
    ·
      refine ⟨73239873922654831017816241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97653165230206441357088321 73239873922654831017816241)
      ·
        refine ⟨54929905441991123263362181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73239873922654831017816241 54929905441991123263362181)
        ·
          refine ⟨10299357270373335611880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54929905441991123263362181 10299357270373335611880409)
          ·
            refine ⟨7724517952780001708910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10299357270373335611880409 7724517952780001708910307)
            ·
              refine ⟨11586776929170002563365461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724517952780001708910307 11586776929170002563365461)
              ·
                refine ⟨135782542138710967539439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11586776929170002563365461 135782542138710967539439)
                ·
                  rfl

theorem cell22_3569880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_3569880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3569880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3569880 prefixEnd_3569880 := by exact prefixLift 3569880
  have htrace : WordTrace (prefixWord ++ tailWord_3569880) baseStart_3569880 baseEnd_3569880 := by
    simpa [prefixWord, tailWord_3569880, baseEnd_3569880] using wordTrace_append hprefix tailTrace_3569880
  have hstable : (prefixWord ++ tailWord_3569880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3569880).length < 2 ^ (prefixWord ++ tailWord_3569880).sum := by decide
  have hdescent : baseEnd_3569880 < baseStart_3569880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3569880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570002 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3570002 : Nat := 118140960795 + 3570002 * 2 ^ 59
def prefixEnd_3570002 : Nat := 4983230072969 + 3 ^ 40 * 3570002 * 2
def baseEnd_3570002 : Nat := 1222084642341631056304577

theorem tailTrace_3570002 : CollatzResearch.WordTrace tailWord_3570002 prefixEnd_3570002 1222084642341631056304577 := by
  unfold tailWord_3570002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552167503124984161348065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86805780008333291096928173 32552167503124984161348065)
  ·
    refine ⟨24414125627343738121011049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32552167503124984161348065 24414125627343738121011049)
    ·
      refine ⟨18310594220507803590758287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24414125627343738121011049 18310594220507803590758287)
      ·
        refine ⟨27465891330761705386137431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18310594220507803590758287 27465891330761705386137431)
        ·
          refine ⟨41198836996142558079206147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27465891330761705386137431 41198836996142558079206147)
          ·
            refine ⟨61798255494213837118809221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41198836996142558079206147 61798255494213837118809221)
            ·
              refine ⟨11587172905165094459776729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61798255494213837118809221 11587172905165094459776729)
              ·
                refine ⟨8690379678873820844832547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587172905165094459776729 8690379678873820844832547)
                ·
                  refine ⟨13035569518310731267248821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690379678873820844832547 13035569518310731267248821)
                  ·
                    refine ⟨1222084642341631056304577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13035569518310731267248821 1222084642341631056304577)
                    ·
                      rfl

theorem cell22_3570002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3570002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570002 prefixEnd_3570002 := by exact prefixLift 3570002
  have htrace : WordTrace (prefixWord ++ tailWord_3570002) baseStart_3570002 baseEnd_3570002 := by
    simpa [prefixWord, tailWord_3570002, baseEnd_3570002] using wordTrace_append hprefix tailTrace_3570002
  have hstable : (prefixWord ++ tailWord_3570002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570002).length < 2 ^ (prefixWord ++ tailWord_3570002).sum := by decide
  have hdescent : baseEnd_3570002 < baseStart_3570002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570004 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3570004 : Nat := 118140960795 + 3570004 * 2 ^ 59
def prefixEnd_3570004 : Nat := 4983230072969 + 3 ^ 40 * 3570004 * 2
def baseEnd_3570004 : Nat := 407361775660834572584857

theorem tailTrace_3570004 : CollatzResearch.WordTrace tailWord_3570004 prefixEnd_3570004 407361775660834572584857 := by
  unfold tailWord_3570004
  simp only [CollatzResearch.WordTrace]
  refine ⟨65104371479246345493482533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86805828638995127324643377 65104371479246345493482533)
  ·
    refine ⟨12207069652358689780027975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65104371479246345493482533 12207069652358689780027975)
    ·
      refine ⟨18310604478538034670041963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207069652358689780027975 18310604478538034670041963)
      ·
        refine ⟨27465906717807052005062945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18310604478538034670041963 27465906717807052005062945)
        ·
          refine ⟨20599430038355289003797209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27465906717807052005062945 20599430038355289003797209)
          ·
            refine ⟨15449572528766466752847907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20599430038355289003797209 15449572528766466752847907)
            ·
              refine ⟨23174358793149700129271861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15449572528766466752847907 23174358793149700129271861)
              ·
                refine ⟨2172596136857784387119237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23174358793149700129271861 2172596136857784387119237)
                ·
                  refine ⟨407361775660834572584857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172596136857784387119237 407361775660834572584857)
                  ·
                    rfl

theorem cell22_3570004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3570004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570004 prefixEnd_3570004 := by exact prefixLift 3570004
  have htrace : WordTrace (prefixWord ++ tailWord_3570004) baseStart_3570004 baseEnd_3570004 := by
    simpa [prefixWord, tailWord_3570004, baseEnd_3570004] using wordTrace_append hprefix tailTrace_3570004
  have hstable : (prefixWord ++ tailWord_3570004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570004).length < 2 ^ (prefixWord ++ tailWord_3570004).sum := by decide
  have hdescent : baseEnd_3570004 < baseStart_3570004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570049 : List Nat := [1, 2, 4, 3, 1, 1, 4, 6]
def baseStart_3570049 : Nat := 118140960795 + 3570049 * 2 ^ 59
def prefixEnd_3570049 : Nat := 4983230072969 + 3 ^ 40 * 3570049 * 2
def baseEnd_3570049 : Nat := 135788970155793177819937

theorem tailTrace_3570049 : CollatzResearch.WordTrace tailWord_3570049 prefixEnd_3570049 135788970155793177819937 := by
  unfold tailWord_3570049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130210384243329663672353201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86806922828886442448235467 130210384243329663672353201)
  ·
    refine ⟨97657788182497247754264901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130210384243329663672353201 97657788182497247754264901)
    ·
      refine ⟨18310835284218233953924669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97657788182497247754264901 18310835284218233953924669)
      ·
        refine ⟨6866563231581837732721751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18310835284218233953924669 6866563231581837732721751)
        ·
          refine ⟨10299844847372756599082627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866563231581837732721751 10299844847372756599082627)
          ·
            refine ⟨15449767271059134898623941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10299844847372756599082627 15449767271059134898623941)
            ·
              refine ⟨2896831363323587793491989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15449767271059134898623941 2896831363323587793491989)
              ·
                refine ⟨135788970155793177819937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2896831363323587793491989 135788970155793177819937)
                ·
                  rfl

theorem cell22_3570049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 6].length) (baseStart_3570049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570049 prefixEnd_3570049 := by exact prefixLift 3570049
  have htrace : WordTrace (prefixWord ++ tailWord_3570049) baseStart_3570049 baseEnd_3570049 := by
    simpa [prefixWord, tailWord_3570049, baseEnd_3570049] using wordTrace_append hprefix tailTrace_3570049
  have hstable : (prefixWord ++ tailWord_3570049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570049).length < 2 ^ (prefixWord ++ tailWord_3570049).sum := by decide
  have hdescent : baseEnd_3570049 < baseStart_3570049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_3570075 : Nat := 118140960795 + 3570075 * 2 ^ 59
def prefixEnd_3570075 : Nat := 4983230072969 + 3 ^ 40 * 3570075 * 2
def baseEnd_3570075 : Nat := 1222109631733483199229353

theorem tailTrace_3570075 : CollatzResearch.WordTrace tailWord_3570075 prefixEnd_3570075 1222109631733483199229353 := by
  unfold tailWord_3570075
  simp only [CollatzResearch.WordTrace]
  refine ⟨130211332541235470112799679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86807555027490313408533119 130211332541235470112799679)
  ·
    refine ⟨195316998811853205169199519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130211332541235470112799679 195316998811853205169199519)
    ·
      refine ⟨292975498217779807753799279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195316998811853205169199519 292975498217779807753799279)
      ·
        refine ⟨439463247326669711630698919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292975498217779807753799279 439463247326669711630698919)
        ·
          refine ⟨659194870990004567446048379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439463247326669711630698919 659194870990004567446048379)
          ·
            refine ⟨988792306485006851169072569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659194870990004567446048379 988792306485006851169072569)
            ·
              refine ⟨741594229863755138376804427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988792306485006851169072569 741594229863755138376804427)
              ·
                refine ⟨1112391344795632707565206641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741594229863755138376804427 1112391344795632707565206641)
                ·
                  refine ⟨834293508596724530673904981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1112391344795632707565206641 834293508596724530673904981)
                  ·
                    refine ⟨1222109631733483199229353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 834293508596724530673904981 1222109631733483199229353)
                    ·
                      rfl

theorem cell22_3570075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_3570075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570075 prefixEnd_3570075 := by exact prefixLift 3570075
  have htrace : WordTrace (prefixWord ++ tailWord_3570075) baseStart_3570075 baseEnd_3570075 := by
    simpa [prefixWord, tailWord_3570075, baseEnd_3570075] using wordTrace_append hprefix tailTrace_3570075
  have hstable : (prefixWord ++ tailWord_3570075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570075).length < 2 ^ (prefixWord ++ tailWord_3570075).sum := by decide
  have hdescent : baseEnd_3570075 < baseStart_3570075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570137 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_3570137 : Nat := 118140960795 + 3570137 * 2 ^ 59
def prefixEnd_3570137 : Nat := 4983230072969 + 3 ^ 40 * 3570137 * 2
def baseEnd_3570137 : Nat := 1222130855600535704179163

theorem tailTrace_3570137 : CollatzResearch.WordTrace tailWord_3570137 prefixEnd_3570137 1222130855600535704179163 := by
  unfold tailWord_3570137
  simp only [CollatzResearch.WordTrace]
  refine ⟨130213593867010854701556665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86809062578007236467704443 130213593867010854701556665)
  ·
    refine ⟨97660195400258141026167499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130213593867010854701556665 97660195400258141026167499)
    ·
      refine ⟨146490293100387211539251249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97660195400258141026167499 146490293100387211539251249)
      ·
        refine ⟨109867719825290408654438437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146490293100387211539251249 109867719825290408654438437)
        ·
          refine ⟨20600197467241951622707207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109867719825290408654438437 20600197467241951622707207)
          ·
            refine ⟨30900296200862927434060811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600197467241951622707207 30900296200862927434060811)
            ·
              refine ⟨46350444301294391151091217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30900296200862927434060811 46350444301294391151091217)
              ·
                refine ⟨34762833225970793363318413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46350444301294391151091217 34762833225970793363318413)
                ·
                  refine ⟨13036062459739047511244405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34762833225970793363318413 13036062459739047511244405)
                  ·
                    refine ⟨1222130855600535704179163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13036062459739047511244405 1222130855600535704179163)
                    ·
                      rfl

theorem cell22_3570137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_3570137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570137 prefixEnd_3570137 := by exact prefixLift 3570137
  have htrace : WordTrace (prefixWord ++ tailWord_3570137) baseStart_3570137 baseEnd_3570137 := by
    simpa [prefixWord, tailWord_3570137, baseEnd_3570137] using wordTrace_append hprefix tailTrace_3570137
  have hstable : (prefixWord ++ tailWord_3570137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570137).length < 2 ^ (prefixWord ++ tailWord_3570137).sum := by decide
  have hdescent : baseEnd_3570137 < baseStart_3570137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570154 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3570154 : Nat := 118140960795 + 3570154 * 2 ^ 59
def prefixEnd_3570154 : Nat := 4983230072969 + 3 ^ 40 * 3570154 * 2
def baseEnd_3570154 : Nat := 1222136675047953326504111

theorem tailTrace_3570154 : CollatzResearch.WordTrace tailWord_3570154 prefixEnd_3570154 1222136675047953326504111 := by
  unfold tailWord_3570154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32553553476987316651231379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86809475938632844403283677 32553553476987316651231379)
  ·
    refine ⟨48830330215480974976847069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32553553476987316651231379 48830330215480974976847069)
    ·
      refine ⟨18311373830805365616317651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48830330215480974976847069 18311373830805365616317651)
      ·
        refine ⟨27467060746208048424476477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18311373830805365616317651 27467060746208048424476477)
        ·
          refine ⟨10300147779828018159178679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27467060746208048424476477 10300147779828018159178679)
          ·
            refine ⟨15450221669742027238768019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300147779828018159178679 15450221669742027238768019)
            ·
              refine ⟨23175332504613040858152029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15450221669742027238768019 23175332504613040858152029)
              ·
                refine ⟨8690749689229890321807011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23175332504613040858152029 8690749689229890321807011)
                ·
                  refine ⟨13036124533844835482710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8690749689229890321807011 13036124533844835482710517)
                  ·
                    refine ⟨1222136675047953326504111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13036124533844835482710517 1222136675047953326504111)
                    ·
                      rfl

theorem cell22_3570154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3570154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570154 prefixEnd_3570154 := by exact prefixLift 3570154
  have htrace : WordTrace (prefixWord ++ tailWord_3570154) baseStart_3570154 baseEnd_3570154 := by
    simpa [prefixWord, tailWord_3570154, baseEnd_3570154] using wordTrace_append hprefix tailTrace_3570154
  have hstable : (prefixWord ++ tailWord_3570154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570154).length < 2 ^ (prefixWord ++ tailWord_3570154).sum := by decide
  have hdescent : baseEnd_3570154 < baseStart_3570154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570169 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_3570169 : Nat := 118140960795 + 3570169 * 2 ^ 59
def prefixEnd_3570169 : Nat := 4983230072969 + 3 ^ 40 * 3570169 * 2
def baseEnd_3570169 : Nat := 1222141809854498287379065

theorem tailTrace_3570169 : CollatzResearch.WordTrace tailWord_3570169 prefixEnd_3570169 1222141809854498287379065 := by
  unfold tailWord_3570169
  simp only [CollatzResearch.WordTrace]
  refine ⟨130214761002894924166721561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86809840668596616111147707 130214761002894924166721561)
  ·
    refine ⟨97661070752171193125041171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130214761002894924166721561 97661070752171193125041171)
    ·
      refine ⟨146491606128256789687561757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97661070752171193125041171 146491606128256789687561757)
      ·
        refine ⟨54934352298096296132835659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146491606128256789687561757 54934352298096296132835659)
        ·
          refine ⟨82401528447144444199253489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54934352298096296132835659 82401528447144444199253489)
          ·
            refine ⟨61801146335358333149440117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82401528447144444199253489 61801146335358333149440117)
            ·
              refine ⟨5793857468939843732760011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61801146335358333149440117 5793857468939843732760011)
              ·
                refine ⟨8690786203409765599140017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793857468939843732760011 8690786203409765599140017)
                ·
                  refine ⟨6518089652557324199355013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8690786203409765599140017 6518089652557324199355013)
                  ·
                    refine ⟨1222141809854498287379065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6518089652557324199355013 1222141809854498287379065)
                    ·
                      rfl

theorem cell22_3570169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_3570169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570169 prefixEnd_3570169 := by exact prefixLift 3570169
  have htrace : WordTrace (prefixWord ++ tailWord_3570169) baseStart_3570169 baseEnd_3570169 := by
    simpa [prefixWord, tailWord_3570169, baseEnd_3570169] using wordTrace_append hprefix tailTrace_3570169
  have hstable : (prefixWord ++ tailWord_3570169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570169).length < 2 ^ (prefixWord ++ tailWord_3570169).sum := by decide
  have hdescent : baseEnd_3570169 < baseStart_3570169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570188 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_3570188 : Nat := 118140960795 + 3570188 * 2 ^ 59
def prefixEnd_3570188 : Nat := 4983230072969 + 3 ^ 40 * 3570188 * 2
def baseEnd_3570188 : Nat := 1222148313942788571154007

theorem tailTrace_3570188 : CollatzResearch.WordTrace tailWord_3570188 prefixEnd_3570188 1222148313942788571154007 := by
  unfold tailWord_3570188
  simp only [CollatzResearch.WordTrace]
  refine ⟨65107726994913045205831609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86810302659884060274442145 65107726994913045205831609)
  ·
    refine ⟨48830795246184783904373707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65107726994913045205831609 48830795246184783904373707)
    ·
      refine ⟨73246192869277175856560561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48830795246184783904373707 73246192869277175856560561)
      ·
        refine ⟨54934644651957881892420421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73246192869277175856560561 54934644651957881892420421)
        ·
          refine ⟨10300245872242102854828829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54934644651957881892420421 10300245872242102854828829)
          ·
            refine ⟨3862592202090788570560811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10300245872242102854828829 3862592202090788570560811)
            ·
              refine ⟨5793888303136182855841217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862592202090788570560811 5793888303136182855841217)
              ·
                refine ⟨4345416227352137141880913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793888303136182855841217 4345416227352137141880913)
                ·
                  refine ⟨3259062170514102856410685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4345416227352137141880913 3259062170514102856410685)
                  ·
                    refine ⟨1222148313942788571154007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259062170514102856410685 1222148313942788571154007)
                    ·
                      rfl

theorem cell22_3570188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_3570188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570188 prefixEnd_3570188 := by exact prefixLift 3570188
  have htrace : WordTrace (prefixWord ++ tailWord_3570188) baseStart_3570188 baseEnd_3570188 := by
    simpa [prefixWord, tailWord_3570188, baseEnd_3570188] using wordTrace_append hprefix tailTrace_3570188
  have hstable : (prefixWord ++ tailWord_3570188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570188).length < 2 ^ (prefixWord ++ tailWord_3570188).sum := by decide
  have hdescent : baseEnd_3570188 < baseStart_3570188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570250 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3570250 : Nat := 118140960795 + 3570250 * 2 ^ 59
def prefixEnd_3570250 : Nat := 4983230072969 + 3 ^ 40 * 3570250 * 2
def baseEnd_3570250 : Nat := 1222169537809841076103817

theorem tailTrace_3570250 : CollatzResearch.WordTrace tailWord_3570250 prefixEnd_3570250 1222169537809841076103817 := by
  unfold tailWord_3570250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554428828900368750105051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86811810210400983333613469 32554428828900368750105051)
  ·
    refine ⟨48831643243350553125157577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32554428828900368750105051 48831643243350553125157577)
    ·
      refine ⟨36623732432512914843868183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48831643243350553125157577 36623732432512914843868183)
      ·
        refine ⟨54935598648769372265802275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36623732432512914843868183 54935598648769372265802275)
        ·
          refine ⟨82403397973154058398703413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54935598648769372265802275 82403397973154058398703413)
          ·
            refine ⟨7725318559983192974878445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82403397973154058398703413 7725318559983192974878445)
            ·
              refine ⟨2896994459993697365579417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7725318559983192974878445 2896994459993697365579417)
              ·
                refine ⟨2172745844995273024184563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896994459993697365579417 2172745844995273024184563)
                ·
                  refine ⟨3259118767492909536276845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172745844995273024184563 3259118767492909536276845)
                  ·
                    refine ⟨1222169537809841076103817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259118767492909536276845 1222169537809841076103817)
                    ·
                      rfl

theorem cell22_3570250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3570250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570250 prefixEnd_3570250 := by exact prefixLift 3570250
  have htrace : WordTrace (prefixWord ++ tailWord_3570250) baseStart_3570250 baseEnd_3570250 := by
    simpa [prefixWord, tailWord_3570250, baseEnd_3570250] using wordTrace_append hprefix tailTrace_3570250
  have hstable : (prefixWord ++ tailWord_3570250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570250).length < 2 ^ (prefixWord ++ tailWord_3570250).sum := by decide
  have hdescent : baseEnd_3570250 < baseStart_3570250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570308 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_3570308 : Nat := 118140960795 + 3570308 * 2 ^ 59
def prefixEnd_3570308 : Nat := 4983230072969 + 3 ^ 40 * 3570308 * 2
def baseEnd_3570308 : Nat := 407396464131716086051213

theorem tailTrace_3570308 : CollatzResearch.WordTrace tailWord_3570308 prefixEnd_3570308 407396464131716086051213 := by
  unfold tailWord_3570308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109915374695675453015789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86813220499594233937354385 65109915374695675453015789)
  ·
    refine ⟨24416218265510878294880921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65109915374695675453015789 24416218265510878294880921)
    ·
      refine ⟨18312163699133158721160691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24416218265510878294880921 18312163699133158721160691)
      ·
        refine ⟨27468245548699738081741037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18312163699133158721160691 27468245548699738081741037)
        ·
          refine ⟨10300592080762401780652889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27468245548699738081741037 10300592080762401780652889)
          ·
            refine ⟨7725444060571801335489667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10300592080762401780652889 7725444060571801335489667)
            ·
              refine ⟨11588166090857702003234501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725444060571801335489667 11588166090857702003234501)
              ·
                refine ⟨2172781142035819125606469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11588166090857702003234501 2172781142035819125606469)
                ·
                  refine ⟨407396464131716086051213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172781142035819125606469 407396464131716086051213)
                  ·
                    rfl

theorem cell22_3570308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_3570308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570308 prefixEnd_3570308 := by exact prefixLift 3570308
  have htrace : WordTrace (prefixWord ++ tailWord_3570308) baseStart_3570308 baseEnd_3570308 := by
    simpa [prefixWord, tailWord_3570308, baseEnd_3570308] using wordTrace_append hprefix tailTrace_3570308
  have hstable : (prefixWord ++ tailWord_3570308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570308).length < 2 ^ (prefixWord ++ tailWord_3570308).sum := by decide
  have hdescent : baseEnd_3570308 < baseStart_3570308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570368 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_3570368 : Nat := 118140960795 + 3570368 * 2 ^ 59
def prefixEnd_3570368 : Nat := 4983230072969 + 3 ^ 40 * 3570368 * 2
def baseEnd_3570368 : Nat := 1222209931621328101653455

theorem tailTrace_3570368 : CollatzResearch.WordTrace tailWord_3570368 prefixEnd_3570368 1222209931621328101653455 := by
  unfold tailWord_3570368
  simp only [CollatzResearch.WordTrace]
  refine ⟨65111009564586990576607879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86814679419449320768810505 65111009564586990576607879)
  ·
    refine ⟨97666514346880485864911819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65111009564586990576607879 97666514346880485864911819)
    ·
      refine ⟨146499771520320728797367729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97666514346880485864911819 146499771520320728797367729)
      ·
        refine ⟨109874828640240546598025797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146499771520320728797367729 109874828640240546598025797)
        ·
          refine ⟨20601530370045102487129837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109874828640240546598025797 20601530370045102487129837)
          ·
            refine ⟨7725573888766913432673689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20601530370045102487129837 7725573888766913432673689)
            ·
              refine ⟨5794180416575185074505267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725573888766913432673689 5794180416575185074505267)
              ·
                refine ⟨8691270624862777611757901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794180416575185074505267 8691270624862777611757901)
                ·
                  refine ⟨3259226484323541604409213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8691270624862777611757901 3259226484323541604409213)
                  ·
                    refine ⟨1222209931621328101653455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259226484323541604409213 1222209931621328101653455)
                    ·
                      rfl

theorem cell22_3570368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_3570368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570368 prefixEnd_3570368 := by exact prefixLift 3570368
  have htrace : WordTrace (prefixWord ++ tailWord_3570368) baseStart_3570368 baseEnd_3570368 := by
    simpa [prefixWord, tailWord_3570368, baseEnd_3570368] using wordTrace_append hprefix tailTrace_3570368
  have hstable : (prefixWord ++ tailWord_3570368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570368).length < 2 ^ (prefixWord ++ tailWord_3570368).sum := by decide
  have hdescent : baseEnd_3570368 < baseStart_3570368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570374 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3570374 : Nat := 118140960795 + 3570374 * 2 ^ 59
def prefixEnd_3570374 : Nat := 4983230072969 + 3 ^ 40 * 3570374 * 2
def baseEnd_3570374 : Nat := 1222211985543946086003437

theorem tailTrace_3570374 : CollatzResearch.WordTrace tailWord_3570374 prefixEnd_3570374 1222211985543946086003437 := by
  unfold tailWord_3570374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069444936473507630560443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86814825311434829451956117 4069444936473507630560443)
  ·
    refine ⟨6104167404710261445840665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069444936473507630560443 6104167404710261445840665)
    ·
      refine ⟨4578125553532696084380499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6104167404710261445840665 4578125553532696084380499)
      ·
        refine ⟨6867188330299044126570749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578125553532696084380499 6867188330299044126570749)
        ·
          refine ⟨2575195623862141547464031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6867188330299044126570749 2575195623862141547464031)
          ·
            refine ⟨3862793435793212321196047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575195623862141547464031 3862793435793212321196047)
            ·
              refine ⟨5794190153689818481794071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862793435793212321196047 5794190153689818481794071)
              ·
                refine ⟨8691285230534727722691107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794190153689818481794071 8691285230534727722691107)
                ·
                  refine ⟨13036927845802091584036661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691285230534727722691107 13036927845802091584036661)
                  ·
                    refine ⟨1222211985543946086003437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13036927845802091584036661 1222211985543946086003437)
                    ·
                      rfl

theorem cell22_3570374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3570374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570374 prefixEnd_3570374 := by exact prefixLift 3570374
  have htrace : WordTrace (prefixWord ++ tailWord_3570374) baseStart_3570374 baseEnd_3570374 := by
    simpa [prefixWord, tailWord_3570374, baseEnd_3570374] using wordTrace_append hprefix tailTrace_3570374
  have hstable : (prefixWord ++ tailWord_3570374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570374).length < 2 ^ (prefixWord ++ tailWord_3570374).sum := by decide
  have hdescent : baseEnd_3570374 < baseStart_3570374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570409 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 8]
def baseStart_3570409 : Nat := 118140960795 + 3570409 * 2 ^ 59
def prefixEnd_3570409 : Nat := 4983230072969 + 3 ^ 40 * 3570409 * 2
def baseEnd_3570409 : Nat := 407407988919739220459443

theorem tailTrace_3570409 : CollatzResearch.WordTrace tailWord_3570409 prefixEnd_3570409 407407988919739220459443 := by
  unfold tailWord_3570409
  simp only [CollatzResearch.WordTrace]
  refine ⟨130223514522025445155458281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86815676348016963436972187 130223514522025445155458281)
  ·
    refine ⟨97667635891519083866593711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130223514522025445155458281 97667635891519083866593711)
    ·
      refine ⟨146501453837278625799890567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97667635891519083866593711 146501453837278625799890567)
      ·
        refine ⟨219752180755917938699835851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146501453837278625799890567 219752180755917938699835851)
        ·
          refine ⟨329628271133876908049753777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219752180755917938699835851 329628271133876908049753777)
          ·
            refine ⟨247221203350407681037315333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329628271133876908049753777 247221203350407681037315333)
            ·
              refine ⟨46353975628201440194496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247221203350407681037315333 46353975628201440194496625)
              ·
                refine ⟨34765481721151080145872469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46353975628201440194496625 34765481721151080145872469)
                ·
                  refine ⟨407407988919739220459443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34765481721151080145872469 407407988919739220459443)
                  ·
                    rfl

theorem cell22_3570409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_3570409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570409 prefixEnd_3570409 := by exact prefixLift 3570409
  have htrace : WordTrace (prefixWord ++ tailWord_3570409) baseStart_3570409 baseEnd_3570409 := by
    simpa [prefixWord, tailWord_3570409, baseEnd_3570409] using wordTrace_append hprefix tailTrace_3570409
  have hstable : (prefixWord ++ tailWord_3570409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570409).length < 2 ^ (prefixWord ++ tailWord_3570409).sum := by decide
  have hdescent : baseEnd_3570409 < baseStart_3570409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570426 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_3570426 : Nat := 118140960795 + 3570426 * 2 ^ 59
def prefixEnd_3570426 : Nat := 4983230072969 + 3 ^ 40 * 3570426 * 2
def baseEnd_3570426 : Nat := 407409928735545094567759

theorem tailTrace_3570426 : CollatzResearch.WordTrace tailWord_3570426 prefixEnd_3570426 407409928735545094567759 := by
  unfold tailWord_3570426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32556033640740964264706783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86816089708642571372551421 32556033640740964264706783)
  ·
    refine ⟨48834050461111446397060175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32556033640740964264706783 48834050461111446397060175)
    ·
      refine ⟨73251075691667169595590263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48834050461111446397060175 73251075691667169595590263)
      ·
        refine ⟨109876613537500754393385395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73251075691667169595590263 109876613537500754393385395)
        ·
          refine ⟨164814920306251131590078093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109876613537500754393385395 164814920306251131590078093)
          ·
            refine ⟨61805595114844174346279285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164814920306251131590078093 61805595114844174346279285)
            ·
              refine ⟨5794274542016641344963683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61805595114844174346279285 5794274542016641344963683)
              ·
                refine ⟨8691411813024962017445525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794274542016641344963683 8691411813024962017445525)
                ·
                  refine ⟨407409928735545094567759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8691411813024962017445525 407409928735545094567759)
                  ·
                    rfl

theorem cell22_3570426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_3570426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570426 prefixEnd_3570426 := by exact prefixLift 3570426
  have htrace : WordTrace (prefixWord ++ tailWord_3570426) baseStart_3570426 baseEnd_3570426 := by
    simpa [prefixWord, tailWord_3570426, baseEnd_3570426] using wordTrace_append hprefix tailTrace_3570426
  have hstable : (prefixWord ++ tailWord_3570426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570426).length < 2 ^ (prefixWord ++ tailWord_3570426).sum := by decide
  have hdescent : baseEnd_3570426 < baseStart_3570426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570533 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 5]
def baseStart_3570533 : Nat := 118140960795 + 3570533 * 2 ^ 59
def prefixEnd_3570533 : Nat := 4983230072969 + 3 ^ 40 * 3570533 * 2
def baseEnd_3570533 : Nat := 407422138164440890425983

theorem tailTrace_3570533 : CollatzResearch.WordTrace tailWord_3570533 prefixEnd_3570533 407422138164440890425983 := by
  unfold tailWord_3570533
  simp only [CollatzResearch.WordTrace]
  refine ⟨130228037173576214332972253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86818691449050809555314835 130228037173576214332972253)
  ·
    refine ⟨48835513940091080374864595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130228037173576214332972253 48835513940091080374864595)
    ·
      refine ⟨73253270910136620562296893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48835513940091080374864595 73253270910136620562296893)
      ·
        refine ⟨27469976591301232710861335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73253270910136620562296893 27469976591301232710861335)
        ·
          refine ⟨41204964886951849066292003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27469976591301232710861335 41204964886951849066292003)
          ·
            refine ⟨61807447330427773599438005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41204964886951849066292003 61807447330427773599438005)
            ·
              refine ⟨5794448187227603774947313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61807447330427773599438005 5794448187227603774947313)
              ·
                refine ⟨4345836140420702831210485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794448187227603774947313 4345836140420702831210485)
                ·
                  refine ⟨407422138164440890425983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4345836140420702831210485 407422138164440890425983)
                  ·
                    rfl

theorem cell22_3570533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_3570533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570533 prefixEnd_3570533 := by exact prefixLift 3570533
  have htrace : WordTrace (prefixWord ++ tailWord_3570533) baseStart_3570533 baseEnd_3570533 := by
    simpa [prefixWord, tailWord_3570533, baseEnd_3570533] using wordTrace_append hprefix tailTrace_3570533
  have hstable : (prefixWord ++ tailWord_3570533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570533).length < 2 ^ (prefixWord ++ tailWord_3570533).sum := by decide
  have hdescent : baseEnd_3570533 < baseStart_3570533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570580 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3570580 : Nat := 118140960795 + 3570580 * 2 ^ 59
def prefixEnd_3570580 : Nat := 4983230072969 + 3 ^ 40 * 3570580 * 2
def baseEnd_3570580 : Nat := 1222282503553830215352805

theorem tailTrace_3570580 : CollatzResearch.WordTrace tailWord_3570580 prefixEnd_3570580 1222282503553830215352805 := by
  unfold tailWord_3570580
  simp only [CollatzResearch.WordTrace]
  refine ⟨65114875702202970679966597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86819834269603960906622129 65114875702202970679966597)
  ·
    refine ⟨12209039194163057002493737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65114875702202970679966597 12209039194163057002493737)
    ·
      refine ⟨9156779395622292751870303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12209039194163057002493737 9156779395622292751870303)
      ·
        refine ⟨13735169093433439127805455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156779395622292751870303 13735169093433439127805455)
        ·
          refine ⟨20602753640150158691708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13735169093433439127805455 20602753640150158691708183)
          ·
            refine ⟨30904130460225238037562275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20602753640150158691708183 30904130460225238037562275)
            ·
              refine ⟨46356195690337857056343413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30904130460225238037562275 46356195690337857056343413)
              ·
                refine ⟨4345893345969174099032195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46356195690337857056343413 4345893345969174099032195)
                ·
                  refine ⟨6518840018953761148548293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345893345969174099032195 6518840018953761148548293)
                  ·
                    refine ⟨1222282503553830215352805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6518840018953761148548293 1222282503553830215352805)
                    ·
                      rfl

theorem cell22_3570580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3570580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570580 prefixEnd_3570580 := by exact prefixLift 3570580
  have htrace : WordTrace (prefixWord ++ tailWord_3570580) baseStart_3570580 baseEnd_3570580 := by
    simpa [prefixWord, tailWord_3570580, baseEnd_3570580] using wordTrace_append hprefix tailTrace_3570580
  have hstable : (prefixWord ++ tailWord_3570580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570580).length < 2 ^ (prefixWord ++ tailWord_3570580).sum := by decide
  have hdescent : baseEnd_3570580 < baseStart_3570580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570646 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3570646 : Nat := 118140960795 + 3570646 * 2 ^ 59
def prefixEnd_3570646 : Nat := 4983230072969 + 3 ^ 40 * 3570646 * 2
def baseEnd_3570646 : Nat := 407435032234209347734201

theorem tailTrace_3570646 : CollatzResearch.WordTrace tailWord_3570646 prefixEnd_3570646 407435032234209347734201 := by
  unfold tailWord_3570646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139509913885427164489737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86821439081444556421223861 8139509913885427164489737)
  ·
    refine ⟨6104632435414070373367303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8139509913885427164489737 6104632435414070373367303)
    ·
      refine ⟨9156948653121105560050955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104632435414070373367303 9156948653121105560050955)
      ·
        refine ⟨13735422979681658340076433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156948653121105560050955 13735422979681658340076433)
        ·
          refine ⟨10301567234761243755057325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735422979681658340076433 10301567234761243755057325)
          ·
            refine ⟨3863087713035466408146497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10301567234761243755057325 3863087713035466408146497)
            ·
              refine ⟨2897315784776599806109873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863087713035466408146497 2897315784776599806109873)
              ·
                refine ⟨2172986838582449854582405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897315784776599806109873 2172986838582449854582405)
                ·
                  refine ⟨407435032234209347734201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2172986838582449854582405 407435032234209347734201)
                  ·
                    rfl

theorem cell22_3570646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3570646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570646 prefixEnd_3570646 := by exact prefixLift 3570646
  have htrace : WordTrace (prefixWord ++ tailWord_3570646) baseStart_3570646 baseEnd_3570646 := by
    simpa [prefixWord, tailWord_3570646, baseEnd_3570646] using wordTrace_append hprefix tailTrace_3570646
  have hstable : (prefixWord ++ tailWord_3570646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570646).length < 2 ^ (prefixWord ++ tailWord_3570646).sum := by decide
  have hdescent : baseEnd_3570646 < baseStart_3570646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570676 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3570676 : Nat := 118140960795 + 3570676 * 2 ^ 59
def prefixEnd_3570676 : Nat := 4983230072969 + 3 ^ 40 * 3570676 * 2
def baseEnd_3570676 : Nat := 1222315366315717964952511

theorem tailTrace_3570676 : CollatzResearch.WordTrace tailWord_3570676 prefixEnd_3570676 1222315366315717964952511 := by
  unfold tailWord_3570676
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116626406029074877713941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86822168541372099836951921 65116626406029074877713941)
  ·
    refine ⟨3052341862782612884892841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65116626406029074877713941 3052341862782612884892841)
    ·
      refine ⟨2289256397086959663669631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3052341862782612884892841 2289256397086959663669631)
      ·
        refine ⟨3433884595630439495504447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289256397086959663669631 3433884595630439495504447)
        ·
          refine ⟨5150826893445659243256671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433884595630439495504447 5150826893445659243256671)
          ·
            refine ⟨7726240340168488864885007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150826893445659243256671 7726240340168488864885007)
            ·
              refine ⟨11589360510252733297327511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7726240340168488864885007 11589360510252733297327511)
              ·
                refine ⟨17384040765379099945991267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11589360510252733297327511 17384040765379099945991267)
                ·
                  refine ⟨26076061148068649918986901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17384040765379099945991267 26076061148068649918986901)
                  ·
                    refine ⟨1222315366315717964952511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26076061148068649918986901 1222315366315717964952511)
                    ·
                      rfl

theorem cell22_3570676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3570676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570676 prefixEnd_3570676 := by exact prefixLift 3570676
  have htrace : WordTrace (prefixWord ++ tailWord_3570676) baseStart_3570676 baseEnd_3570676 := by
    simpa [prefixWord, tailWord_3570676, baseEnd_3570676] using wordTrace_append hprefix tailTrace_3570676
  have hstable : (prefixWord ++ tailWord_3570676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570676).length < 2 ^ (prefixWord ++ tailWord_3570676).sum := by decide
  have hdescent : baseEnd_3570676 < baseStart_3570676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570689 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3570689 : Nat := 118140960795 + 3570689 * 2 ^ 59
def prefixEnd_3570689 : Nat := 4983230072969 + 3 ^ 40 * 3570689 * 2
def baseEnd_3570689 : Nat := 1222319816481390264377471

theorem tailTrace_3570689 : CollatzResearch.WordTrace tailWord_3570689 prefixEnd_3570689 1222319816481390264377471 := by
  unfold tailWord_3570689
  simp only [CollatzResearch.WordTrace]
  refine ⟨130233726961011052975651121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86822484640674035317100747 130233726961011052975651121)
  ·
    refine ⟨97675295220758289731738341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130233726961011052975651121 97675295220758289731738341)
    ·
      refine ⟨18314117853892179324700939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97675295220758289731738341 18314117853892179324700939)
      ·
        refine ⟨27471176780838268987051409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18314117853892179324700939 27471176780838268987051409)
        ·
          refine ⟨20603382585628701740288557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27471176780838268987051409 20603382585628701740288557)
          ·
            refine ⟨7726268469610763152608209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20603382585628701740288557 7726268469610763152608209)
            ·
              refine ⟨5794701352208072364456157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7726268469610763152608209 5794701352208072364456157)
              ·
                refine ⟨2173013007078027136671059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5794701352208072364456157 2173013007078027136671059)
                ·
                  refine ⟨3259519510617040705006589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173013007078027136671059 3259519510617040705006589)
                  ·
                    refine ⟨1222319816481390264377471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259519510617040705006589 1222319816481390264377471)
                    ·
                      rfl

theorem cell22_3570689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3570689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570689 prefixEnd_3570689 := by exact prefixLift 3570689
  have htrace : WordTrace (prefixWord ++ tailWord_3570689) baseStart_3570689 baseEnd_3570689 := by
    simpa [prefixWord, tailWord_3570689, baseEnd_3570689] using wordTrace_append hprefix tailTrace_3570689
  have hstable : (prefixWord ++ tailWord_3570689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570689).length < 2 ^ (prefixWord ++ tailWord_3570689).sum := by decide
  have hdescent : baseEnd_3570689 < baseStart_3570689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570702 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_3570702 : Nat := 118140960795 + 3570702 * 2 ^ 59
def prefixEnd_3570702 : Nat := 4983230072969 + 3 ^ 40 * 3570702 * 2
def baseEnd_3570702 : Nat := 407441422215687521267477

theorem tailTrace_3570702 : CollatzResearch.WordTrace tailWord_3570702 prefixEnd_3570702 407441422215687521267477 := by
  unfold tailWord_3570702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16279275138745494524484295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86822800739975970797249573 16279275138745494524484295)
  ·
    refine ⟨24418912708118241786726443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16279275138745494524484295 24418912708118241786726443)
    ·
      refine ⟨36628369062177362680089665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24418912708118241786726443 36628369062177362680089665)
      ·
        refine ⟨27471276796633022010067249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36628369062177362680089665 27471276796633022010067249)
        ·
          refine ⟨20603457597474766507550437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27471276796633022010067249 20603457597474766507550437)
          ·
            refine ⟨3863148299526518720165707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20603457597474766507550437 3863148299526518720165707)
            ·
              refine ⟨5794722449289778080248561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863148299526518720165707 5794722449289778080248561)
              ·
                refine ⟨4346041836967333560186421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794722449289778080248561 4346041836967333560186421)
                ·
                  refine ⟨407441422215687521267477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4346041836967333560186421 407441422215687521267477)
                  ·
                    rfl

theorem cell22_3570702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_3570702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570702 prefixEnd_3570702 := by exact prefixLift 3570702
  have htrace : WordTrace (prefixWord ++ tailWord_3570702) baseStart_3570702 baseEnd_3570702 := by
    simpa [prefixWord, tailWord_3570702, baseEnd_3570702] using wordTrace_append hprefix tailTrace_3570702
  have hstable : (prefixWord ++ tailWord_3570702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570702).length < 2 ^ (prefixWord ++ tailWord_3570702).sum := by decide
  have hdescent : baseEnd_3570702 < baseStart_3570702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570713 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 6]
def baseStart_3570713 : Nat := 118140960795 + 3570713 * 2 ^ 59
def prefixEnd_3570713 : Nat := 4983230072969 + 3 ^ 40 * 3570713 * 2
def baseEnd_3570713 : Nat := 407442677390620733925799

theorem tailTrace_3570713 : CollatzResearch.WordTrace tailWord_3570713 prefixEnd_3570713 407442677390620733925799 := by
  unfold tailWord_3570713
  simp only [CollatzResearch.WordTrace]
  refine ⟨130234602312924105074524793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86823068208616070049683195 130234602312924105074524793)
  ·
    refine ⟨97675951734693078805893595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130234602312924105074524793 97675951734693078805893595)
    ·
      refine ⟨146513927602039618208840393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97675951734693078805893595 146513927602039618208840393)
      ·
        refine ⟨109885445701529713656630295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146513927602039618208840393 109885445701529713656630295)
        ·
          refine ⟨164828168552294570484945443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109885445701529713656630295 164828168552294570484945443)
          ·
            refine ⟨247242252828441855727418165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164828168552294570484945443 247242252828441855727418165)
            ·
              refine ⟨23178961202666423974445453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 247242252828441855727418165 23178961202666423974445453)
              ·
                refine ⟨8692110450999908990417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23178961202666423974445453 8692110450999908990417045)
                ·
                  refine ⟨407442677390620733925799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8692110450999908990417045 407442677390620733925799)
                  ·
                    rfl

theorem cell22_3570713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_3570713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570713 prefixEnd_3570713 := by exact prefixLift 3570713
  have htrace : WordTrace (prefixWord ++ tailWord_3570713) baseStart_3570713 baseEnd_3570713 := by
    simpa [prefixWord, tailWord_3570713, baseEnd_3570713] using wordTrace_append hprefix tailTrace_3570713
  have hstable : (prefixWord ++ tailWord_3570713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570713).length < 2 ^ (prefixWord ++ tailWord_3570713).sum := by decide
  have hdescent : baseEnd_3570713 < baseStart_3570713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570760 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_3570760 : Nat := 118140960795 + 3570760 * 2 ^ 59
def prefixEnd_3570760 : Nat := 4983230072969 + 3 ^ 40 * 3570760 * 2
def baseEnd_3570760 : Nat := 1222344121232369745852253

theorem tailTrace_3570760 : CollatzResearch.WordTrace tailWord_3570760 prefixEnd_3570760 1222344121232369745852253 := by
  unfold tailWord_3570760
  simp only [CollatzResearch.WordTrace]
  refine ⟨65118158271876916050742867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86824211029169221400990489 65118158271876916050742867)
  ·
    refine ⟨97677237407815374076114301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65118158271876916050742867 97677237407815374076114301)
    ·
      refine ⟨36628964027930765278542863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97677237407815374076114301 36628964027930765278542863)
      ·
        refine ⟨54943446041896147917814295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36628964027930765278542863 54943446041896147917814295)
        ·
          refine ⟨82415169062844221876721443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54943446041896147917814295 82415169062844221876721443)
          ·
            refine ⟨123622753594266332815082165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82415169062844221876721443 123622753594266332815082165)
            ·
              refine ⟨11589633149462468701413953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123622753594266332815082165 11589633149462468701413953)
              ·
                refine ⟨8692224862096851526060465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11589633149462468701413953 8692224862096851526060465)
                ·
                  refine ⟨6519168646572638644545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8692224862096851526060465 6519168646572638644545349)
                  ·
                    refine ⟨1222344121232369745852253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519168646572638644545349 1222344121232369745852253)
                    ·
                      rfl

theorem cell22_3570760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_3570760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570760 prefixEnd_3570760 := by exact prefixLift 3570760
  have htrace : WordTrace (prefixWord ++ tailWord_3570760) baseStart_3570760 baseEnd_3570760 := by
    simpa [prefixWord, tailWord_3570760, baseEnd_3570760] using wordTrace_append hprefix tailTrace_3570760
  have hstable : (prefixWord ++ tailWord_3570760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570760).length < 2 ^ (prefixWord ++ tailWord_3570760).sum := by decide
  have hdescent : baseEnd_3570760 < baseStart_3570760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570858 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3570858 : Nat := 118140960795 + 3570858 * 2 ^ 59
def prefixEnd_3570858 : Nat := 4983230072969 + 3 ^ 40 * 3570858 * 2
def baseEnd_3570858 : Nat := 1222377668635130156901953

theorem tailTrace_3570858 : CollatzResearch.WordTrace tailWord_3570858 prefixEnd_3570858 1222377668635130156901953 := by
  unfold tailWord_3570858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32559972724349698709638307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86826593931599196559035485 32559972724349698709638307)
  ·
    refine ⟨48839959086524548064457461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32559972724349698709638307 48839959086524548064457461)
    ·
      refine ⟨4578746164361676381042887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48839959086524548064457461 4578746164361676381042887)
      ·
        refine ⟨6868119246542514571564331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578746164361676381042887 6868119246542514571564331)
        ·
          refine ⟨10302178869813771857346497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868119246542514571564331 10302178869813771857346497)
          ·
            refine ⟨7726634152360328893009873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10302178869813771857346497 7726634152360328893009873)
            ·
              refine ⟨5794975614270246669757405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7726634152360328893009873 5794975614270246669757405)
              ·
                refine ⟨2173115855351342501159027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5794975614270246669757405 2173115855351342501159027)
                ·
                  refine ⟨3259673783027013751738541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173115855351342501159027 3259673783027013751738541)
                  ·
                    refine ⟨1222377668635130156901953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259673783027013751738541 1222377668635130156901953)
                    ·
                      rfl

theorem cell22_3570858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3570858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570858 prefixEnd_3570858 := by exact prefixLift 3570858
  have htrace : WordTrace (prefixWord ++ tailWord_3570858) baseStart_3570858 baseEnd_3570858 := by
    simpa [prefixWord, tailWord_3570858, baseEnd_3570858] using wordTrace_append hprefix tailTrace_3570858
  have hstable : (prefixWord ++ tailWord_3570858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570858).length < 2 ^ (prefixWord ++ tailWord_3570858).sum := by decide
  have hdescent : baseEnd_3570858 < baseStart_3570858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3570895 : Nat := 118140960795 + 3570895 * 2 ^ 59
def prefixEnd_3570895 : Nat := 4983230072969 + 3 ^ 40 * 3570895 * 2
def baseEnd_3570895 : Nat := 1222390334491274393726839

theorem tailTrace_3570895 : CollatzResearch.WordTrace tailWord_3570895 prefixEnd_3570895 1222390334491274393726839 := by
  unfold tailWord_3570895
  simp only [CollatzResearch.WordTrace]
  refine ⟨130241240398264750157650139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86827493598843166771766759 130241240398264750157650139)
  ·
    refine ⟨195361860597397125236475209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130241240398264750157650139 195361860597397125236475209)
    ·
      refine ⟨146521395448047843927356407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195361860597397125236475209 146521395448047843927356407)
      ·
        refine ⟨219782093172071765891034611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146521395448047843927356407 219782093172071765891034611)
        ·
          refine ⟨329673139758107648836551917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219782093172071765891034611 329673139758107648836551917)
          ·
            refine ⟨123627427409290368313706969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329673139758107648836551917 123627427409290368313706969)
            ·
              refine ⟨92720570556967776235280227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123627427409290368313706969 92720570556967776235280227)
              ·
                refine ⟨139080855835451664352920341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92720570556967776235280227 139080855835451664352920341)
                ·
                  refine ⟨6519415117286796766543141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139080855835451664352920341 6519415117286796766543141)
                  ·
                    refine ⟨1222390334491274393726839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519415117286796766543141 1222390334491274393726839)
                    ·
                      rfl

theorem cell22_3570895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3570895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570895 prefixEnd_3570895 := by exact prefixLift 3570895
  have htrace : WordTrace (prefixWord ++ tailWord_3570895) baseStart_3570895 baseEnd_3570895 := by
    simpa [prefixWord, tailWord_3570895, baseEnd_3570895] using wordTrace_append hprefix tailTrace_3570895
  have hstable : (prefixWord ++ tailWord_3570895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570895).length < 2 ^ (prefixWord ++ tailWord_3570895).sum := by decide
  have hdescent : baseEnd_3570895 < baseStart_3570895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570927 : List Nat := [1, 1, 2, 1, 7, 2, 8]
def baseStart_3570927 : Nat := 118140960795 + 3570927 * 2 ^ 59
def prefixEnd_3570927 : Nat := 4983230072969 + 3 ^ 40 * 3570927 * 2
def baseEnd_3570927 : Nat := 45274121805379147293583

theorem tailTrace_3570927 : CollatzResearch.WordTrace tailWord_3570927 prefixEnd_3570927 45274121805379147293583 := by
  unfold tailWord_3570927
  simp only [CollatzResearch.WordTrace]
  refine ⟨130242407534148819622815035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86828271689432546415210023 130242407534148819622815035)
  ·
    refine ⟨195363611301223229434222553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130242407534148819622815035 195363611301223229434222553)
    ·
      refine ⟨146522708475917422075666915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195363611301223229434222553 146522708475917422075666915)
      ·
        refine ⟨219784062713876133113500373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146522708475917422075666915 219784062713876133113500373)
        ·
          refine ⟨5151188969856471869847665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 219784062713876133113500373 5151188969856471869847665)
          ·
            refine ⟨3863391727392353902385749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151188969856471869847665 3863391727392353902385749)
            ·
              refine ⟨45274121805379147293583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3863391727392353902385749 45274121805379147293583)
              ·
                rfl

theorem cell22_3570927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 8].length) (baseStart_3570927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570927 prefixEnd_3570927 := by exact prefixLift 3570927
  have htrace : WordTrace (prefixWord ++ tailWord_3570927) baseStart_3570927 baseEnd_3570927 := by
    simpa [prefixWord, tailWord_3570927, baseEnd_3570927] using wordTrace_append hprefix tailTrace_3570927
  have hstable : (prefixWord ++ tailWord_3570927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570927).length < 2 ^ (prefixWord ++ tailWord_3570927).sum := by decide
  have hdescent : baseEnd_3570927 < baseStart_3570927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570948 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3570948 : Nat := 118140960795 + 3570948 * 2 ^ 59
def prefixEnd_3570948 : Nat := 4983230072969 + 3 ^ 40 * 3570948 * 2
def baseEnd_3570948 : Nat := 1222408477474399922151677

theorem tailTrace_3570948 : CollatzResearch.WordTrace tailWord_3570948 prefixEnd_3570948 1222408477474399922151677 := by
  unfold tailWord_3570948
  simp only [CollatzResearch.WordTrace]
  refine ⟨65121586733536370104664749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86828782311381826806219665 65121586733536370104664749)
  ·
    refine ⟨24420595025076138789249281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65121586733536370104664749 24420595025076138789249281)
    ·
      refine ⟨18315446268807104091936961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24420595025076138789249281 18315446268807104091936961)
      ·
        refine ⟨13736584701605328068952721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18315446268807104091936961 13736584701605328068952721)
        ·
          refine ⟨10302438526203996051714541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13736584701605328068952721 10302438526203996051714541)
          ·
            refine ⟨3863414447326498519392953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10302438526203996051714541 3863414447326498519392953)
            ·
              refine ⟨2897560835494873889544715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863414447326498519392953 2897560835494873889544715)
              ·
                refine ⟨4346341253242310834317073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897560835494873889544715 4346341253242310834317073)
                ·
                  refine ⟨3259755939931733125737805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346341253242310834317073 3259755939931733125737805)
                  ·
                    refine ⟨1222408477474399922151677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259755939931733125737805 1222408477474399922151677)
                    ·
                      rfl

theorem cell22_3570948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3570948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570948 prefixEnd_3570948 := by exact prefixLift 3570948
  have htrace : WordTrace (prefixWord ++ tailWord_3570948) baseStart_3570948 baseEnd_3570948 := by
    simpa [prefixWord, tailWord_3570948, baseEnd_3570948] using wordTrace_append hprefix tailTrace_3570948
  have hstable : (prefixWord ++ tailWord_3570948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570948).length < 2 ^ (prefixWord ++ tailWord_3570948).sum := by decide
  have hdescent : baseEnd_3570948 < baseStart_3570948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_3570985 : Nat := 118140960795 + 3570985 * 2 ^ 59
def prefixEnd_3570985 : Nat := 4983230072969 + 3 ^ 40 * 3570985 * 2
def baseEnd_3570985 : Nat := 1222421143330544158976563

theorem tailTrace_3570985 : CollatzResearch.WordTrace tailWord_3570985 prefixEnd_3570985 1222421143330544158976563 := by
  unfold tailWord_3570985
  simp only [CollatzResearch.WordTrace]
  refine ⟨130244522967938695528426409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86829681978625797018950939 130244522967938695528426409)
  ·
    refine ⟨97683392225954021646319807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130244522967938695528426409 97683392225954021646319807)
    ·
      refine ⟨146525088338931032469479711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97683392225954021646319807 146525088338931032469479711)
      ·
        refine ⟨219787632508396548704219567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146525088338931032469479711 219787632508396548704219567)
        ·
          refine ⟨329681448762594823056329351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219787632508396548704219567 329681448762594823056329351)
          ·
            refine ⟨494522173143892234584494027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329681448762594823056329351 494522173143892234584494027)
            ·
              refine ⟨741783259715838351876741041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494522173143892234584494027 741783259715838351876741041)
              ·
                refine ⟨556337444786878763907555781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741783259715838351876741041 556337444786878763907555781)
                ·
                  refine ⟨104313270897539768232666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556337444786878763907555781 104313270897539768232666709)
                  ·
                    refine ⟨1222421143330544158976563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104313270897539768232666709 1222421143330544158976563)
                    ·
                      rfl

theorem cell22_3570985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_3570985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570985 prefixEnd_3570985 := by exact prefixLift 3570985
  have htrace : WordTrace (prefixWord ++ tailWord_3570985) baseStart_3570985 baseEnd_3570985 := by
    simpa [prefixWord, tailWord_3570985, baseEnd_3570985] using wordTrace_append hprefix tailTrace_3570985
  have hstable : (prefixWord ++ tailWord_3570985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570985).length < 2 ^ (prefixWord ++ tailWord_3570985).sum := by decide
  have hdescent : baseEnd_3570985 < baseStart_3570985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3570993 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3570993 : Nat := 118140960795 + 3570993 * 2 ^ 59
def prefixEnd_3570993 : Nat := 4983230072969 + 3 ^ 40 * 3570993 * 2
def baseEnd_3570993 : Nat := 1222423881894034804776539

theorem tailTrace_3570993 : CollatzResearch.WordTrace tailWord_3570993 prefixEnd_3570993 1222423881894034804776539 := by
  unfold tailWord_3570993
  simp only [CollatzResearch.WordTrace]
  refine ⟨130244814751909712894717633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86829876501273141929811755 130244814751909712894717633)
  ·
    refine ⟨97683611063932284671038225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130244814751909712894717633 97683611063932284671038225)
    ·
      refine ⟨73262708297949213503278669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97683611063932284671038225 73262708297949213503278669)
      ·
        refine ⟨27473515611730955063729501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73262708297949213503278669 27473515611730955063729501)
        ·
          refine ⟨10302568354399108148898563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27473515611730955063729501 10302568354399108148898563)
          ·
            refine ⟨15453852531598662223347845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10302568354399108148898563 15453852531598662223347845)
            ·
              refine ⟨2897597349674749166877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15453852531598662223347845 2897597349674749166877721)
              ·
                refine ⟨2173198012256061875158291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897597349674749166877721 2173198012256061875158291)
                ·
                  refine ⟨3259797018384092812737437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173198012256061875158291 3259797018384092812737437)
                  ·
                    refine ⟨1222423881894034804776539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259797018384092812737437 1222423881894034804776539)
                    ·
                      rfl

theorem cell22_3570993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3570993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3570993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3570993 prefixEnd_3570993 := by exact prefixLift 3570993
  have htrace : WordTrace (prefixWord ++ tailWord_3570993) baseStart_3570993 baseEnd_3570993 := by
    simpa [prefixWord, tailWord_3570993, baseEnd_3570993] using wordTrace_append hprefix tailTrace_3570993
  have hstable : (prefixWord ++ tailWord_3570993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3570993).length < 2 ^ (prefixWord ++ tailWord_3570993).sum := by decide
  have hdescent : baseEnd_3570993 < baseStart_3570993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3570993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571002 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3571002 : Nat := 118140960795 + 3571002 * 2 ^ 59
def prefixEnd_3571002 : Nat := 4983230072969 + 3 ^ 40 * 3571002 * 2
def baseEnd_3571002 : Nat := 1222426962777961781301511

theorem tailTrace_3571002 : CollatzResearch.WordTrace tailWord_3571002 prefixEnd_3571002 1222426962777961781301511 := by
  unfold tailWord_3571002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561285752219276857948815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86830095339251404954530173 32561285752219276857948815)
  ·
    refine ⟨48841928628328915286923223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32561285752219276857948815 48841928628328915286923223)
    ·
      refine ⟨73262892942493372930384835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48841928628328915286923223 73262892942493372930384835)
      ·
        refine ⟨109894339413740059395577253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73262892942493372930384835 109894339413740059395577253)
        ·
          refine ⟨20605188640076261136670735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109894339413740059395577253 20605188640076261136670735)
          ·
            refine ⟨30907782960114391705006103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20605188640076261136670735 30907782960114391705006103)
            ·
              refine ⟨46361674440171587557509155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30907782960114391705006103 46361674440171587557509155)
              ·
                refine ⟨69542511660257381336263733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46361674440171587557509155 69542511660257381336263733)
                ·
                  refine ⟨6519610468149129500274725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69542511660257381336263733 6519610468149129500274725)
                  ·
                    refine ⟨1222426962777961781301511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519610468149129500274725 1222426962777961781301511)
                    ·
                      rfl

theorem cell22_3571002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3571002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571002 prefixEnd_3571002 := by exact prefixLift 3571002
  have htrace : WordTrace (prefixWord ++ tailWord_3571002) baseStart_3571002 baseEnd_3571002 := by
    simpa [prefixWord, tailWord_3571002, baseEnd_3571002] using wordTrace_append hprefix tailTrace_3571002
  have hstable : (prefixWord ++ tailWord_3571002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571002).length < 2 ^ (prefixWord ++ tailWord_3571002).sum := by decide
  have hdescent : baseEnd_3571002 < baseStart_3571002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571032 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_3571032 : Nat := 118140960795 + 3571032 * 2 ^ 59
def prefixEnd_3571032 : Nat := 4983230072969 + 3 ^ 40 * 3571032 * 2
def baseEnd_3571032 : Nat := 1222437232391051703051419

theorem tailTrace_3571032 : CollatzResearch.WordTrace tailWord_3571032 prefixEnd_3571032 1222437232391051703051419 := by
  unfold tailWord_3571032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65123118599384211277693675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86830824799178948370258233 65123118599384211277693675)
  ·
    refine ⟨97684677899076316916540513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65123118599384211277693675 97684677899076316916540513)
    ·
      refine ⟨73263508424307237687405385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97684677899076316916540513 73263508424307237687405385)
      ·
        refine ⟨54947631318230428265554039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73263508424307237687405385 54947631318230428265554039)
        ·
          refine ⟨82421446977345642398331059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54947631318230428265554039 82421446977345642398331059)
          ·
            refine ⟨123632170466018463597496589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82421446977345642398331059 123632170466018463597496589)
            ·
              refine ⟨46362063924756923849061221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123632170466018463597496589 46362063924756923849061221)
              ·
                refine ⟨8692886985891923221698979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46362063924756923849061221 8692886985891923221698979)
                ·
                  refine ⟨13039330478837884832548469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8692886985891923221698979 13039330478837884832548469)
                  ·
                    refine ⟨1222437232391051703051419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13039330478837884832548469 1222437232391051703051419)
                    ·
                      rfl

theorem cell22_3571032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_3571032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571032 prefixEnd_3571032 := by exact prefixLift 3571032
  have htrace : WordTrace (prefixWord ++ tailWord_3571032) baseStart_3571032 baseEnd_3571032 := by
    simpa [prefixWord, tailWord_3571032, baseEnd_3571032] using wordTrace_append hprefix tailTrace_3571032
  have hstable : (prefixWord ++ tailWord_3571032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571032).length < 2 ^ (prefixWord ++ tailWord_3571032).sum := by decide
  have hdescent : baseEnd_3571032 < baseStart_3571032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571034 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_3571034 : Nat := 118140960795 + 3571034 * 2 ^ 59
def prefixEnd_3571034 : Nat := 4983230072969 + 3 ^ 40 * 3571034 * 2
def baseEnd_3571034 : Nat := 407479305677308121500471

theorem tailTrace_3571034 : CollatzResearch.WordTrace tailWord_3571034 prefixEnd_3571034 407479305677308121500471 := by
  unfold tailWord_3571034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561577536190294224240039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86830873429840784597973437 32561577536190294224240039)
  ·
    refine ⟨48842366304285441336360059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32561577536190294224240039 48842366304285441336360059)
    ·
      refine ⟨73263549456428162004540089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48842366304285441336360059 73263549456428162004540089)
      ·
        refine ⟨54947662092321121503405067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73263549456428162004540089 54947662092321121503405067)
        ·
          refine ⟨82421493138481682255107601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54947662092321121503405067 82421493138481682255107601)
          ·
            refine ⟨61816119853861261691330701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82421493138481682255107601 61816119853861261691330701)
            ·
              refine ⟨23181044945197973134249013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61816119853861261691330701 23181044945197973134249013)
              ·
                refine ⟨2173222963612309981335845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23181044945197973134249013 2173222963612309981335845)
                ·
                  refine ⟨407479305677308121500471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173222963612309981335845 407479305677308121500471)
                  ·
                    rfl

theorem cell22_3571034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_3571034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571034 prefixEnd_3571034 := by exact prefixLift 3571034
  have htrace : WordTrace (prefixWord ++ tailWord_3571034) baseStart_3571034 baseEnd_3571034 := by
    simpa [prefixWord, tailWord_3571034, baseEnd_3571034] using wordTrace_append hprefix tailTrace_3571034
  have hstable : (prefixWord ++ tailWord_3571034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571034).length < 2 ^ (prefixWord ++ tailWord_3571034).sum := by decide
  have hdescent : baseEnd_3571034 < baseStart_3571034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571049 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_3571049 : Nat := 118140960795 + 3571049 * 2 ^ 59
def prefixEnd_3571049 : Nat := 4983230072969 + 3 ^ 40 * 3571049 * 2
def baseEnd_3571049 : Nat := 1222443051838469325376367

theorem tailTrace_3571049 : CollatzResearch.WordTrace tailWord_3571049 prefixEnd_3571049 1222443051838469325376367 := by
  unfold tailWord_3571049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130246857239706834458756201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86831238159804556305837467 130246857239706834458756201)
  ·
    refine ⟨97685142929780125844067151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130246857239706834458756201 97685142929780125844067151)
    ·
      refine ⟨146527714394670188766100727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97685142929780125844067151 146527714394670188766100727)
      ·
        refine ⟨219791571592005283149151091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146527714394670188766100727 219791571592005283149151091)
        ·
          refine ⟨329687357388007924723726637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219791571592005283149151091 329687357388007924723726637)
          ·
            refine ⟨123632759020502971771397489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329687357388007924723726637 123632759020502971771397489)
            ·
              refine ⟨92724569265377228828548117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123632759020502971771397489 92724569265377228828548117)
              ·
                refine ⟨4346464184314557601338193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92724569265377228828548117 4346464184314557601338193)
                ·
                  refine ⟨3259848138235918201003645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346464184314557601338193 3259848138235918201003645)
                  ·
                    refine ⟨1222443051838469325376367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3259848138235918201003645 1222443051838469325376367)
                    ·
                      rfl

theorem cell22_3571049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_3571049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571049 prefixEnd_3571049 := by exact prefixLift 3571049
  have htrace : WordTrace (prefixWord ++ tailWord_3571049) baseStart_3571049 baseEnd_3571049 := by
    simpa [prefixWord, tailWord_3571049, baseEnd_3571049] using wordTrace_append hprefix tailTrace_3571049
  have hstable : (prefixWord ++ tailWord_3571049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571049).length < 2 ^ (prefixWord ++ tailWord_3571049).sum := by decide
  have hdescent : baseEnd_3571049 < baseStart_3571049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571070 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3571070 : Nat := 118140960795 + 3571070 * 2 ^ 59
def prefixEnd_3571070 : Nat := 4983230072969 + 3 ^ 40 * 3571070 * 2
def baseEnd_3571070 : Nat := 1222450240567632270601303

theorem tailTrace_3571070 : CollatzResearch.WordTrace tailWord_3571070 prefixEnd_3571070 1222450240567632270601303 := by
  unfold tailWord_3571070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280952896578844380658833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86831748781753836696847109 16280952896578844380658833)
  ·
    refine ⟨12210714672434133285494125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16280952896578844380658833 12210714672434133285494125)
    ·
      refine ⟨4579018002162799982060297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12210714672434133285494125 4579018002162799982060297)
      ·
        refine ⟨3434263501622099986545223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4579018002162799982060297 3434263501622099986545223)
        ·
          refine ⟨5151395252433149979817835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434263501622099986545223 5151395252433149979817835)
          ·
            refine ⟨7727092878649724969726753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151395252433149979817835 7727092878649724969726753)
            ·
              refine ⟨5795319658987293727295065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727092878649724969726753 5795319658987293727295065)
              ·
                refine ⟨4346489744240470295471299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795319658987293727295065 4346489744240470295471299)
                ·
                  refine ⟨6519734616360705443206949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346489744240470295471299 6519734616360705443206949)
                  ·
                    refine ⟨1222450240567632270601303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519734616360705443206949 1222450240567632270601303)
                    ·
                      rfl

theorem cell22_3571070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3571070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571070 prefixEnd_3571070 := by exact prefixLift 3571070
  have htrace : WordTrace (prefixWord ++ tailWord_3571070) baseStart_3571070 baseEnd_3571070 := by
    simpa [prefixWord, tailWord_3571070, baseEnd_3571070] using wordTrace_append hprefix tailTrace_3571070
  have hstable : (prefixWord ++ tailWord_3571070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571070).length < 2 ^ (prefixWord ++ tailWord_3571070).sum := by decide
  have hdescent : baseEnd_3571070 < baseStart_3571070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571079 : List Nat := [1, 1, 4, 2, 2, 2, 4, 6]
def baseStart_3571079 : Nat := 118140960795 + 3571079 * 2 ^ 59
def prefixEnd_3571079 : Nat := 4983230072969 + 3 ^ 40 * 3571079 * 2
def baseEnd_3571079 : Nat := 135828146827951027458475

theorem tailTrace_3571079 : CollatzResearch.WordTrace tailWord_3571079 prefixEnd_3571079 135828146827951027458475 := by
  unfold tailWord_3571079
  simp only [CollatzResearch.WordTrace]
  refine ⟨130247951429598149582348291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86831967619732099721565527 130247951429598149582348291)
  ·
    refine ⟨195371927144397224373522437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130247951429598149582348291 195371927144397224373522437)
    ·
      refine ⟨36632236339574479570035457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195371927144397224373522437 36632236339574479570035457)
      ·
        refine ⟨27474177254680859677526593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36632236339574479570035457 27474177254680859677526593)
        ·
          refine ⟨20605632941010644758144945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27474177254680859677526593 20605632941010644758144945)
          ·
            refine ⟨15454224705757983568608709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20605632941010644758144945 15454224705757983568608709)
            ·
              refine ⟨2897667132329621919114133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15454224705757983568608709 2897667132329621919114133)
              ·
                refine ⟨135828146827951027458475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2897667132329621919114133 135828146827951027458475)
                ·
                  rfl

theorem cell22_3571079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 6].length) (baseStart_3571079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571079 prefixEnd_3571079 := by exact prefixLift 3571079
  have htrace : WordTrace (prefixWord ++ tailWord_3571079) baseStart_3571079 baseEnd_3571079 := by
    simpa [prefixWord, tailWord_3571079, baseEnd_3571079] using wordTrace_append hprefix tailTrace_3571079
  have hstable : (prefixWord ++ tailWord_3571079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571079).length < 2 ^ (prefixWord ++ tailWord_3571079).sum := by decide
  have hdescent : baseEnd_3571079 < baseStart_3571079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571096 : List Nat := [2, 1, 2, 5, 3, 1, 8]
def baseStart_3571096 : Nat := 118140960795 + 3571096 * 2 ^ 59
def prefixEnd_3571096 : Nat := 4983230072969 + 3 ^ 40 * 3571096 * 2
def baseEnd_3571096 : Nat := 45276264477739884053749

theorem tailTrace_3571096 : CollatzResearch.WordTrace tailWord_3571096 prefixEnd_3571096 45276264477739884053749 := by
  unfold tailWord_3571096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124285735268280742858571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86832380980357707657144761 65124285735268280742858571)
  ·
    refine ⟨97686428602902421114287857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65124285735268280742858571 97686428602902421114287857)
    ·
      refine ⟨73264821452176815835715893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97686428602902421114287857 73264821452176815835715893)
      ·
        refine ⟨6868577011141576484598365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73264821452176815835715893 6868577011141576484598365)
        ·
          refine ⟨2575716379178091181724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6868577011141576484598365 2575716379178091181724387)
          ·
            refine ⟨3863574568767136772586581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575716379178091181724387 3863574568767136772586581)
            ·
              refine ⟨45276264477739884053749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3863574568767136772586581 45276264477739884053749)
              ·
                rfl

theorem cell22_3571096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 8].length) (baseStart_3571096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571096 prefixEnd_3571096 := by exact prefixLift 3571096
  have htrace : WordTrace (prefixWord ++ tailWord_3571096) baseStart_3571096 baseEnd_3571096 := by
    simpa [prefixWord, tailWord_3571096, baseEnd_3571096] using wordTrace_append hprefix tailTrace_3571096
  have hstable : (prefixWord ++ tailWord_3571096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571096).length < 2 ^ (prefixWord ++ tailWord_3571096).sum := by decide
  have hdescent : baseEnd_3571096 < baseStart_3571096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571107 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 7]
def baseStart_3571107 : Nat := 118140960795 + 3571107 * 2 ^ 59
def prefixEnd_3571107 : Nat := 4983230072969 + 3 ^ 40 * 3571107 * 2
def baseEnd_3571107 : Nat := 407487635474592169142063

theorem tailTrace_3571107 : CollatzResearch.WordTrace tailWord_3571107 prefixEnd_3571107 407487635474592169142063 := by
  unfold tailWord_3571107
  simp only [CollatzResearch.WordTrace]
  refine ⟨130248972673496710364367575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86832648448997806909578383 130248972673496710364367575)
  ·
    refine ⟨195373459010245065546551363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130248972673496710364367575 195373459010245065546551363)
    ·
      refine ⟨293060188515367598319827045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195373459010245065546551363 293060188515367598319827045)
      ·
        refine ⟨54948785346631424684967571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293060188515367598319827045 54948785346631424684967571)
        ·
          refine ⟨82423178019947137027451357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54948785346631424684967571 82423178019947137027451357)
          ·
            refine ⟨30908691757480176385294259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82423178019947137027451357 30908691757480176385294259)
            ·
              refine ⟨46363037636220264577941389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30908691757480176385294259 46363037636220264577941389)
              ·
                refine ⟨17386139113582599216728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46363037636220264577941389 17386139113582599216728021)
                ·
                  refine ⟨407487635474592169142063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17386139113582599216728021 407487635474592169142063)
                  ·
                    rfl

theorem cell22_3571107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_3571107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571107 prefixEnd_3571107 := by exact prefixLift 3571107
  have htrace : WordTrace (prefixWord ++ tailWord_3571107) baseStart_3571107 baseEnd_3571107 := by
    simpa [prefixWord, tailWord_3571107, baseEnd_3571107] using wordTrace_append hprefix tailTrace_3571107
  have hstable : (prefixWord ++ tailWord_3571107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571107).length < 2 ^ (prefixWord ++ tailWord_3571107).sum := by decide
  have hdescent : baseEnd_3571107 < baseStart_3571107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571152 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_3571152 : Nat := 118140960795 + 3571152 * 2 ^ 59
def prefixEnd_3571152 : Nat := 4983230072969 + 3 ^ 40 * 3571152 * 2
def baseEnd_3571152 : Nat := 407492770281137130017017

theorem tailTrace_3571152 : CollatzResearch.WordTrace tailWord_3571152 prefixEnd_3571152 407492770281137130017017 := by
  unfold tailWord_3571152
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125306979166841524877855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86833742638889122033170473 65125306979166841524877855)
  ·
    refine ⟨97687960468750262287316783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65125306979166841524877855 97687960468750262287316783)
    ·
      refine ⟨146531940703125393430975175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97687960468750262287316783 146531940703125393430975175)
      ·
        refine ⟨219797911054688090146462763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146531940703125393430975175 219797911054688090146462763)
        ·
          refine ⟨329696866582032135219694145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219797911054688090146462763 329696866582032135219694145)
          ·
            refine ⟨247272649936524101414770609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329696866582032135219694145 247272649936524101414770609)
            ·
              refine ⟨185454487452393076061077957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247272649936524101414770609 185454487452393076061077957)
              ·
                refine ⟨34772716397323701761452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185454487452393076061077957 34772716397323701761452117)
                ·
                  refine ⟨407492770281137130017017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34772716397323701761452117 407492770281137130017017)
                  ·
                    rfl

theorem cell22_3571152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_3571152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571152 prefixEnd_3571152 := by exact prefixLift 3571152
  have htrace : WordTrace (prefixWord ++ tailWord_3571152) baseStart_3571152 baseEnd_3571152 := by
    simpa [prefixWord, tailWord_3571152, baseEnd_3571152] using wordTrace_append hprefix tailTrace_3571152
  have hstable : (prefixWord ++ tailWord_3571152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571152).length < 2 ^ (prefixWord ++ tailWord_3571152).sum := by decide
  have hdescent : baseEnd_3571152 < baseStart_3571152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571158 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3571158 : Nat := 118140960795 + 3571158 * 2 ^ 59
def prefixEnd_3571158 : Nat := 4983230072969 + 3 ^ 40 * 3571158 * 2
def baseEnd_3571158 : Nat := 407493454922009791467011

theorem tailTrace_3571158 : CollatzResearch.WordTrace tailWord_3571158 prefixEnd_3571158 407493454922009791467011 := by
  unfold tailWord_3571158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140677049769496629654633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86833888530874630716316085 8140677049769496629654633)
  ·
    refine ⟨6105507787327122472240975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140677049769496629654633 6105507787327122472240975)
    ·
      refine ⟨9158261680990683708361463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105507787327122472240975 9158261680990683708361463)
      ·
        refine ⟨13737392521486025562542195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158261680990683708361463 13737392521486025562542195)
        ·
          refine ⟨20606088782229038343813293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737392521486025562542195 20606088782229038343813293)
          ·
            refine ⟨7727283293335889378929985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20606088782229038343813293 7727283293335889378929985)
            ·
              refine ⟨5795462470001917034197489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727283293335889378929985 5795462470001917034197489)
              ·
                refine ⟨4346596852501437775648117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795462470001917034197489 4346596852501437775648117)
                ·
                  refine ⟨407493454922009791467011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4346596852501437775648117 407493454922009791467011)
                  ·
                    rfl

theorem cell22_3571158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3571158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571158 prefixEnd_3571158 := by exact prefixLift 3571158
  have htrace : WordTrace (prefixWord ++ tailWord_3571158) baseStart_3571158 baseEnd_3571158 := by
    simpa [prefixWord, tailWord_3571158, baseEnd_3571158] using wordTrace_append hprefix tailTrace_3571158
  have hstable : (prefixWord ++ tailWord_3571158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571158).length < 2 ^ (prefixWord ++ tailWord_3571158).sum := by decide
  have hdescent : baseEnd_3571158 < baseStart_3571158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571184 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_3571184 : Nat := 118140960795 + 3571184 * 2 ^ 59
def prefixEnd_3571184 : Nat := 4983230072969 + 3 ^ 40 * 3571184 * 2
def baseEnd_3571184 : Nat := 1222489265097373973250953

theorem tailTrace_3571184 : CollatzResearch.WordTrace tailWord_3571184 prefixEnd_3571184 1222489265097373973250953 := by
  unfold tailWord_3571184
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125890547108876257460303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86834520729478501676613737 65125890547108876257460303)
  ·
    refine ⟨97688835820663314386190455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65125890547108876257460303 97688835820663314386190455)
    ·
      refine ⟨146533253730994971579285683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97688835820663314386190455 146533253730994971579285683)
      ·
        refine ⟨219799880596492457368928525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146533253730994971579285683 219799880596492457368928525)
        ·
          refine ⟨82424955223684671513348197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219799880596492457368928525 82424955223684671513348197)
          ·
            refine ⟨15454679104440875908752787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82424955223684671513348197 15454679104440875908752787)
            ·
              refine ⟨23182018656661313863129181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15454679104440875908752787 23182018656661313863129181)
              ·
                refine ⟨8693256996247992698673443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23182018656661313863129181 8693256996247992698673443)
                ·
                  refine ⟨13039885494371989048010165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693256996247992698673443 13039885494371989048010165)
                  ·
                    refine ⟨1222489265097373973250953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13039885494371989048010165 1222489265097373973250953)
                    ·
                      rfl

theorem cell22_3571184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_3571184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571184 prefixEnd_3571184 := by exact prefixLift 3571184
  have htrace : WordTrace (prefixWord ++ tailWord_3571184) baseStart_3571184 baseEnd_3571184 := by
    simpa [prefixWord, tailWord_3571184, baseEnd_3571184] using wordTrace_append hprefix tailTrace_3571184
  have hstable : (prefixWord ++ tailWord_3571184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571184).length < 2 ^ (prefixWord ++ tailWord_3571184).sum := by decide
  have hdescent : baseEnd_3571184 < baseStart_3571184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571186 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3571186 : Nat := 118140960795 + 3571186 * 2 ^ 59
def prefixEnd_3571186 : Nat := 4983230072969 + 3 ^ 40 * 3571186 * 2
def baseEnd_3571186 : Nat := 407496649912748878233649

theorem tailTrace_3571186 : CollatzResearch.WordTrace tailWord_3571186 prefixEnd_3571186 407496649912748878233649 := by
  unfold tailWord_3571186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562963510052626714123353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86834569360140337904328941 32562963510052626714123353)
  ·
    refine ⟨24422222632539470035592515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32562963510052626714123353 24422222632539470035592515)
    ·
      refine ⟨36633333948809205053388773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24422222632539470035592515 36633333948809205053388773)
      ·
        refine ⟨6868750115401725947510395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36633333948809205053388773 6868750115401725947510395)
        ·
          refine ⟨10303125173102588921265593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868750115401725947510395 10303125173102588921265593)
          ·
            refine ⟨7727343879826941690949195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10303125173102588921265593 7727343879826941690949195)
            ·
              refine ⟨11591015819740412536423793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727343879826941690949195 11591015819740412536423793)
              ·
                refine ⟨8693261864805309402317845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11591015819740412536423793 8693261864805309402317845)
                ·
                  refine ⟨407496649912748878233649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8693261864805309402317845 407496649912748878233649)
                  ·
                    rfl

theorem cell22_3571186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3571186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571186 prefixEnd_3571186 := by exact prefixLift 3571186
  have htrace : WordTrace (prefixWord ++ tailWord_3571186) baseStart_3571186 baseEnd_3571186 := by
    simpa [prefixWord, tailWord_3571186, baseEnd_3571186] using wordTrace_append hprefix tailTrace_3571186
  have hstable : (prefixWord ++ tailWord_3571186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571186).length < 2 ^ (prefixWord ++ tailWord_3571186).sum := by decide
  have hdescent : baseEnd_3571186 < baseStart_3571186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571199 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3571199 : Nat := 118140960795 + 3571199 * 2 ^ 59
def prefixEnd_3571199 : Nat := 4983230072969 + 3 ^ 40 * 3571199 * 2
def baseEnd_3571199 : Nat := 1222494399903918934125907

theorem tailTrace_3571199 : CollatzResearch.WordTrace tailWord_3571199 prefixEnd_3571199 1222494399903918934125907 := by
  unfold tailWord_3571199
  simp only [CollatzResearch.WordTrace]
  refine ⟨130252328189163410076716651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86834885459442273384477767 130252328189163410076716651)
  ·
    refine ⟨195378492283745115115074977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130252328189163410076716651 195378492283745115115074977)
    ·
      refine ⟨146533869212808836336306233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195378492283745115115074977 146533869212808836336306233)
      ·
        refine ⟨109900401909606627252229675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146533869212808836336306233 109900401909606627252229675)
        ·
          refine ⟨164850602864409940878344513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109900401909606627252229675 164850602864409940878344513)
          ·
            refine ⟨123637952148307455658758385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164850602864409940878344513 123637952148307455658758385)
            ·
              refine ⟨92728464111230591744068789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123637952148307455658758385 92728464111230591744068789)
              ·
                refine ⟨8693293510427867976006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92728464111230591744068789 8693293510427867976006449)
                ·
                  refine ⟨6519970132820900982004837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693293510427867976006449 6519970132820900982004837)
                  ·
                    refine ⟨1222494399903918934125907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6519970132820900982004837 1222494399903918934125907)
                    ·
                      rfl

theorem cell22_3571199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3571199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571199 prefixEnd_3571199 := by exact prefixLift 3571199
  have htrace : WordTrace (prefixWord ++ tailWord_3571199) baseStart_3571199 baseEnd_3571199 := by
    simpa [prefixWord, tailWord_3571199, baseEnd_3571199] using wordTrace_append hprefix tailTrace_3571199
  have hstable : (prefixWord ++ tailWord_3571199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571199).length < 2 ^ (prefixWord ++ tailWord_3571199).sum := by decide
  have hdescent : baseEnd_3571199 < baseStart_3571199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571235 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 2, 3]
def baseStart_3571235 : Nat := 118140960795 + 3571235 * 2 ^ 59
def prefixEnd_3571235 : Nat := 4983230072969 + 3 ^ 40 * 3571235 * 2
def baseEnd_3571235 : Nat := 1222506723439626840225797

theorem tailTrace_3571235 : CollatzResearch.WordTrace tailWord_3571235 prefixEnd_3571235 1222506723439626840225797 := by
  unfold tailWord_3571235
  simp only [CollatzResearch.WordTrace]
  refine ⟨130253641217032988225027159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86835760811355325483351439 130253641217032988225027159)
  ·
    refine ⟨195380461825549482337540739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130253641217032988225027159 195380461825549482337540739)
    ·
      refine ⟨293070692738324223506311109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195380461825549482337540739 293070692738324223506311109)
      ·
        refine ⟨54950754888435791907433333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293070692738324223506311109 54950754888435791907433333)
        ·
          refine ⟨5151633270790855491321875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54950754888435791907433333 5151633270790855491321875)
          ·
            refine ⟨7727449906186283236982813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151633270790855491321875 7727449906186283236982813)
            ·
              refine ⟨2897793714819856213868555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7727449906186283236982813 2897793714819856213868555)
              ·
                refine ⟨4346690572229784320802833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897793714819856213868555 4346690572229784320802833)
                ·
                  refine ⟨3260017929172338240602125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346690572229784320802833 3260017929172338240602125)
                  ·
                    refine ⟨1222506723439626840225797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260017929172338240602125 1222506723439626840225797)
                    ·
                      rfl

theorem cell22_3571235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 3].length) (baseStart_3571235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571235 prefixEnd_3571235 := by exact prefixLift 3571235
  have htrace : WordTrace (prefixWord ++ tailWord_3571235) baseStart_3571235 baseEnd_3571235 := by
    simpa [prefixWord, tailWord_3571235, baseEnd_3571235] using wordTrace_append hprefix tailTrace_3571235
  have hstable : (prefixWord ++ tailWord_3571235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571235).length < 2 ^ (prefixWord ++ tailWord_3571235).sum := by decide
  have hdescent : baseEnd_3571235 < baseStart_3571235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571280 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_3571280 : Nat := 118140960795 + 3571280 * 2 ^ 59
def prefixEnd_3571280 : Nat := 4983230072969 + 3 ^ 40 * 3571280 * 2
def baseEnd_3571280 : Nat := 1222522127859261722850659

theorem tailTrace_3571280 : CollatzResearch.WordTrace tailWord_3571280 prefixEnd_3571280 1222522127859261722850659 := by
  unfold tailWord_3571280
  simp only [CollatzResearch.WordTrace]
  refine ⟨65127641250934980455207647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86836855001246640606943529 65127641250934980455207647)
  ·
    refine ⟨97691461876402470682811471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65127641250934980455207647 97691461876402470682811471)
    ·
      refine ⟨146537192814603706024217207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97691461876402470682811471 146537192814603706024217207)
      ·
        refine ⟨219805789221905559036325811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146537192814603706024217207 219805789221905559036325811)
        ·
          refine ⟨329708683832858338554488717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219805789221905559036325811 329708683832858338554488717)
          ·
            refine ⟨123640756437321876957933269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329708683832858338554488717 123640756437321876957933269)
            ·
              refine ⟨2897830228999731491201561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123640756437321876957933269 2897830228999731491201561)
              ·
                refine ⟨2173372671749798618401171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897830228999731491201561 2173372671749798618401171)
                ·
                  refine ⟨3260059007624697927601757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173372671749798618401171 3260059007624697927601757)
                  ·
                    refine ⟨1222522127859261722850659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260059007624697927601757 1222522127859261722850659)
                    ·
                      rfl

theorem cell22_3571280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_3571280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571280 prefixEnd_3571280 := by exact prefixLift 3571280
  have htrace : WordTrace (prefixWord ++ tailWord_3571280) baseStart_3571280 baseEnd_3571280 := by
    simpa [prefixWord, tailWord_3571280, baseEnd_3571280] using wordTrace_append hprefix tailTrace_3571280
  have hstable : (prefixWord ++ tailWord_3571280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571280).length < 2 ^ (prefixWord ++ tailWord_3571280).sum := by decide
  have hdescent : baseEnd_3571280 < baseStart_3571280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571286 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3571286 : Nat := 118140960795 + 3571286 * 2 ^ 59
def prefixEnd_3571286 : Nat := 4983230072969 + 3 ^ 40 * 3571286 * 2
def baseEnd_3571286 : Nat := 1222524181781879707200641

theorem tailTrace_3571286 : CollatzResearch.WordTrace tailWord_3571286 prefixEnd_3571286 1222524181781879707200641 := by
  unfold tailWord_3571286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140968833740513995945857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86837000893232149290089141 8140968833740513995945857)
  ·
    refine ⟨6105726625305385496959393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8140968833740513995945857 6105726625305385496959393)
    ·
      refine ⟨4579294968979039122719545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6105726625305385496959393 4579294968979039122719545)
      ·
        refine ⟨3434471226734279342039659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4579294968979039122719545 3434471226734279342039659)
        ·
          refine ⟨5151706840101419013059489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434471226734279342039659 5151706840101419013059489)
          ·
            refine ⟨3863780130076064259794617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151706840101419013059489 3863780130076064259794617)
            ·
              refine ⟨2897835097557048194845963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863780130076064259794617 2897835097557048194845963)
              ·
                refine ⟨4346752646335572292268945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897835097557048194845963 4346752646335572292268945)
                ·
                  refine ⟨3260064484751679219201709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346752646335572292268945 3260064484751679219201709)
                  ·
                    refine ⟨1222524181781879707200641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260064484751679219201709 1222524181781879707200641)
                    ·
                      rfl

theorem cell22_3571286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3571286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571286 prefixEnd_3571286 := by exact prefixLift 3571286
  have htrace : WordTrace (prefixWord ++ tailWord_3571286) baseStart_3571286 baseEnd_3571286 := by
    simpa [prefixWord, tailWord_3571286, baseEnd_3571286] using wordTrace_append hprefix tailTrace_3571286
  have hstable : (prefixWord ++ tailWord_3571286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571286).length < 2 ^ (prefixWord ++ tailWord_3571286).sum := by decide
  have hdescent : baseEnd_3571286 < baseStart_3571286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571323 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 1, 4]
def baseStart_3571323 : Nat := 118140960795 + 3571323 * 2 ^ 59
def prefixEnd_3571323 : Nat := 4983230072969 + 3 ^ 40 * 3571323 * 2
def baseEnd_3571323 : Nat := 1222536847638023944025527

theorem tailTrace_3571323 : CollatzResearch.WordTrace tailWord_3571323 prefixEnd_3571323 1222536847638023944025527 := by
  unfold tailWord_3571323
  simp only [CollatzResearch.WordTrace]
  refine ⟨130256850840714179254230623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86837900560476119502820415 130256850840714179254230623)
  ·
    refine ⟨195385276261071268881345935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130256850840714179254230623 195385276261071268881345935)
    ·
      refine ⟨293077914391606903322018903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195385276261071268881345935 293077914391606903322018903)
      ·
        refine ⟨439616871587410354983028355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293077914391606903322018903 439616871587410354983028355)
        ·
          refine ⟨659425307381115532474542533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439616871587410354983028355 659425307381115532474542533)
          ·
            refine ⟨123642245133959162338976725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 659425307381115532474542533 123642245133959162338976725)
            ·
              refine ⟨2897865120327167867319767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123642245133959162338976725 2897865120327167867319767)
              ·
                refine ⟨4346797680490751800979651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897865120327167867319767 4346797680490751800979651)
                ·
                  refine ⟨6520196520736127701469477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346797680490751800979651 6520196520736127701469477)
                  ·
                    refine ⟨1222536847638023944025527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520196520736127701469477 1222536847638023944025527)
                    ·
                      rfl

theorem cell22_3571323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 4].length) (baseStart_3571323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571323 prefixEnd_3571323 := by exact prefixLift 3571323
  have htrace : WordTrace (prefixWord ++ tailWord_3571323) baseStart_3571323 baseEnd_3571323 := by
    simpa [prefixWord, tailWord_3571323, baseEnd_3571323] using wordTrace_append hprefix tailTrace_3571323
  have hstable : (prefixWord ++ tailWord_3571323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571323).length < 2 ^ (prefixWord ++ tailWord_3571323).sum := by decide
  have hdescent : baseEnd_3571323 < baseStart_3571323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571374 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3571374 : Nat := 118140960795 + 3571374 * 2 ^ 59
def prefixEnd_3571374 : Nat := 4983230072969 + 3 ^ 40 * 3571374 * 2
def baseEnd_3571374 : Nat := 1222554305980276811000371

theorem tailTrace_3571374 : CollatzResearch.WordTrace tailWord_3571374 prefixEnd_3571374 1222554305980276811000371 := by
  unfold tailWord_3571374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282338870441176870542147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86839140642352943309558117 16282338870441176870542147)
  ·
    refine ⟨24423508305661765305813221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282338870441176870542147 24423508305661765305813221)
    ·
      refine ⟨4579407807311580994839979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24423508305661765305813221 4579407807311580994839979)
      ·
        refine ⟨6869111710967371492259969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579407807311580994839979 6869111710967371492259969)
        ·
          refine ⟨5151833783225528619194977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6869111710967371492259969 5151833783225528619194977)
          ·
            refine ⟨3863875337419146464396233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151833783225528619194977 3863875337419146464396233)
            ·
              refine ⟨2897906503064359848297175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863875337419146464396233 2897906503064359848297175)
              ·
                refine ⟨4346859754596539772445763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897906503064359848297175 4346859754596539772445763)
                ·
                  refine ⟨6520289631894809658668645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346859754596539772445763 6520289631894809658668645)
                  ·
                    refine ⟨1222554305980276811000371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520289631894809658668645 1222554305980276811000371)
                    ·
                      rfl

theorem cell22_3571374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3571374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571374 prefixEnd_3571374 := by exact prefixLift 3571374
  have htrace : WordTrace (prefixWord ++ tailWord_3571374) baseStart_3571374 baseEnd_3571374 := by
    simpa [prefixWord, tailWord_3571374, baseEnd_3571374] using wordTrace_append hprefix tailTrace_3571374
  have hstable : (prefixWord ++ tailWord_3571374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571374).length < 2 ^ (prefixWord ++ tailWord_3571374).sum := by decide
  have hdescent : baseEnd_3571374 < baseStart_3571374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571432 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3571432 : Nat := 118140960795 + 3571432 * 2 ^ 59
def prefixEnd_3571432 : Nat := 4983230072969 + 3 ^ 40 * 3571432 * 2
def baseEnd_3571432 : Nat := 1222574160565583993050193

theorem tailTrace_3571432 : CollatzResearch.WordTrace tailWord_3571432 prefixEnd_3571432 1222574160565583993050193 := by
  unfold tailWord_3571432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65130413198659645434974275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86840550931546193913299033 65130413198659645434974275)
  ·
    refine ⟨97695619797989468152461413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65130413198659645434974275 97695619797989468152461413)
    ·
      refine ⟨18317928712123025278586515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97695619797989468152461413 18317928712123025278586515)
      ·
        refine ⟨27476893068184537917879773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317928712123025278586515 27476893068184537917879773)
        ·
          refine ⟨10303834900569201719204915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27476893068184537917879773 10303834900569201719204915)
          ·
            refine ⟨15455752350853802578807373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303834900569201719204915 15455752350853802578807373)
            ·
              refine ⟨5795907131570175967052765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15455752350853802578807373 5795907131570175967052765)
              ·
                refine ⟨2173465174338815987644787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5795907131570175967052765 2173465174338815987644787)
                ·
                  refine ⟨3260197761508223981467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173465174338815987644787 3260197761508223981467181)
                  ·
                    refine ⟨1222574160565583993050193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260197761508223981467181 1222574160565583993050193)
                    ·
                      rfl

theorem cell22_3571432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3571432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571432 prefixEnd_3571432 := by exact prefixLift 3571432
  have htrace : WordTrace (prefixWord ++ tailWord_3571432) baseStart_3571432 baseEnd_3571432 := by
    simpa [prefixWord, tailWord_3571432, baseEnd_3571432] using wordTrace_append hprefix tailTrace_3571432
  have hstable : (prefixWord ++ tailWord_3571432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571432).length < 2 ^ (prefixWord ++ tailWord_3571432).sum := by decide
  have hdescent : baseEnd_3571432 < baseStart_3571432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571488 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_3571488 : Nat := 118140960795 + 3571488 * 2 ^ 59
def prefixEnd_3571488 : Nat := 4983230072969 + 3 ^ 40 * 3571488 * 2
def baseEnd_3571488 : Nat := 1222593330510018513650021

theorem tailTrace_3571488 : CollatzResearch.WordTrace tailWord_3571488 prefixEnd_3571488 1222593330510018513650021 := by
  unfold tailWord_3571488
  simp only [CollatzResearch.WordTrace]
  refine ⟨65131434442558206216993559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86841912590077608289324745 65131434442558206216993559)
  ·
    refine ⟨97697151663837309325490339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65131434442558206216993559 97697151663837309325490339)
    ·
      refine ⟨146545727495755963988235509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97697151663837309325490339 146545727495755963988235509)
      ·
        refine ⟨13738661952727121623897079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146545727495755963988235509 13738661952727121623897079)
        ·
          refine ⟨20607992929090682435845619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13738661952727121623897079 20607992929090682435845619)
          ·
            refine ⟨30911989393636023653768429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20607992929090682435845619 30911989393636023653768429)
            ·
              refine ⟨11591996022613508870163161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30911989393636023653768429 11591996022613508870163161)
              ·
                refine ⟨8693997016960131652622371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11591996022613508870163161 8693997016960131652622371)
                ·
                  refine ⟨13040995525440197478933557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693997016960131652622371 13040995525440197478933557)
                  ·
                    refine ⟨1222593330510018513650021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13040995525440197478933557 1222593330510018513650021)
                    ·
                      rfl

theorem cell22_3571488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_3571488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571488 prefixEnd_3571488 := by exact prefixLift 3571488
  have htrace : WordTrace (prefixWord ++ tailWord_3571488) baseStart_3571488 baseEnd_3571488 := by
    simpa [prefixWord, tailWord_3571488, baseEnd_3571488] using wordTrace_append hprefix tailTrace_3571488
  have hstable : (prefixWord ++ tailWord_3571488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571488).length < 2 ^ (prefixWord ++ tailWord_3571488).sum := by decide
  have hdescent : baseEnd_3571488 < baseStart_3571488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571490 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3571490 : Nat := 118140960795 + 3571490 * 2 ^ 59
def prefixEnd_3571490 : Nat := 4983230072969 + 3 ^ 40 * 3571490 * 2
def baseEnd_3571490 : Nat := 407531338383630391700005

theorem tailTrace_3571490 : CollatzResearch.WordTrace tailWord_3571490 prefixEnd_3571490 407531338383630391700005 := by
  unfold tailWord_3571490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32565735457777291693889981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86841961220739444517039949 32565735457777291693889981)
  ·
    refine ⟨12212150796666484385208743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32565735457777291693889981 12212150796666484385208743)
    ·
      refine ⟨18318226194999726577813115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12212150796666484385208743 18318226194999726577813115)
      ·
        refine ⟨27477339292499589866719673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318226194999726577813115 27477339292499589866719673)
        ·
          refine ⟨20608004469374692400039755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477339292499589866719673 20608004469374692400039755)
          ·
            refine ⟨30912006704062038600059633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20608004469374692400039755 30912006704062038600059633)
            ·
              refine ⟨23184005028046528950044725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30912006704062038600059633 23184005028046528950044725)
              ·
                refine ⟨2173500471379362089066693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23184005028046528950044725 2173500471379362089066693)
                ·
                  refine ⟨407531338383630391700005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173500471379362089066693 407531338383630391700005)
                  ·
                    rfl

theorem cell22_3571490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3571490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571490 prefixEnd_3571490 := by exact prefixLift 3571490
  have htrace : WordTrace (prefixWord ++ tailWord_3571490) baseStart_3571490 baseEnd_3571490 := by
    simpa [prefixWord, tailWord_3571490, baseEnd_3571490] using wordTrace_append hprefix tailTrace_3571490
  have hstable : (prefixWord ++ tailWord_3571490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571490).length < 2 ^ (prefixWord ++ tailWord_3571490).sum := by decide
  have hdescent : baseEnd_3571490 < baseStart_3571490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571492 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3571492 : Nat := 118140960795 + 3571492 * 2 ^ 59
def prefixEnd_3571492 : Nat := 4983230072969 + 3 ^ 40 * 3571492 * 2
def baseEnd_3571492 : Nat := 1222594699791763836550009

theorem tailTrace_3571492 : CollatzResearch.WordTrace tailWord_3571492 prefixEnd_3571492 1222594699791763836550009 := by
  unfold tailWord_3571492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65131507388550960558566365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86842009851401280744755153 65131507388550960558566365)
  ·
    refine ⟨24424315270706610209462387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65131507388550960558566365 24424315270706610209462387)
    ·
      refine ⟨36636472906059915314193581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24424315270706610209462387 36636472906059915314193581)
      ·
        refine ⟨13738677339772468242822593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36636472906059915314193581 13738677339772468242822593)
        ·
          refine ⟨10304008004829351182116945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13738677339772468242822593 10304008004829351182116945)
          ·
            refine ⟨7728006003622013386587709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304008004829351182116945 7728006003622013386587709)
            ·
              refine ⟨2898002251358255019970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7728006003622013386587709 2898002251358255019970391)
              ·
                refine ⟨4347003377037382529955587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898002251358255019970391 4347003377037382529955587)
                ·
                  refine ⟨6520505065556073794933381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347003377037382529955587 6520505065556073794933381)
                  ·
                    refine ⟨1222594699791763836550009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520505065556073794933381 1222594699791763836550009)
                    ·
                      rfl

theorem cell22_3571492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3571492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571492 prefixEnd_3571492 := by exact prefixLift 3571492
  have htrace : WordTrace (prefixWord ++ tailWord_3571492) baseStart_3571492 baseEnd_3571492 := by
    simpa [prefixWord, tailWord_3571492, baseEnd_3571492] using wordTrace_append hprefix tailTrace_3571492
  have hstable : (prefixWord ++ tailWord_3571492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571492).length < 2 ^ (prefixWord ++ tailWord_3571492).sum := by decide
  have hdescent : baseEnd_3571492 < baseStart_3571492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571505 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_3571505 : Nat := 118140960795 + 3571505 * 2 ^ 59
def prefixEnd_3571505 : Nat := 4983230072969 + 3 ^ 40 * 3571505 * 2
def baseEnd_3571505 : Nat := 1222599149957436135974969

theorem tailTrace_3571505 : CollatzResearch.WordTrace tailWord_3571505 prefixEnd_3571505 1222599149957436135974969 := by
  unfold tailWord_3571505
  simp only [CollatzResearch.WordTrace]
  refine ⟨130263488926054824337355969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86842325950703216224903979 130263488926054824337355969)
  ·
    refine ⟨97697616694541118253016977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130263488926054824337355969 97697616694541118253016977)
    ·
      refine ⟨73273212520905838689762733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97697616694541118253016977 73273212520905838689762733)
      ·
        refine ⟨27477454695339689508661025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73273212520905838689762733 27477454695339689508661025)
        ·
          refine ⟨20608091021504767131495769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27477454695339689508661025 20608091021504767131495769)
          ·
            refine ⟨15456068266128575348621827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20608091021504767131495769 15456068266128575348621827)
            ·
              refine ⟨23184102399192863022932741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456068266128575348621827 23184102399192863022932741)
              ·
                refine ⟨4347019199848661816799889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23184102399192863022932741 4347019199848661816799889)
                ·
                  refine ⟨3260264399886496362599917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347019199848661816799889 3260264399886496362599917)
                  ·
                    refine ⟨1222599149957436135974969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260264399886496362599917 1222599149957436135974969)
                    ·
                      rfl

theorem cell22_3571505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_3571505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571505 prefixEnd_3571505 := by exact prefixLift 3571505
  have htrace : WordTrace (prefixWord ++ tailWord_3571505) baseStart_3571505 baseEnd_3571505 := by
    simpa [prefixWord, tailWord_3571505, baseEnd_3571505] using wordTrace_append hprefix tailTrace_3571505
  have hstable : (prefixWord ++ tailWord_3571505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571505).length < 2 ^ (prefixWord ++ tailWord_3571505).sum := by decide
  have hdescent : baseEnd_3571505 < baseStart_3571505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571578 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3571578 : Nat := 118140960795 + 3571578 * 2 ^ 59
def prefixEnd_3571578 : Nat := 4983230072969 + 3 ^ 40 * 3571578 * 2
def baseEnd_3571578 : Nat := 1222624139349288278899745

theorem tailTrace_3571578 : CollatzResearch.WordTrace tailWord_3571578 prefixEnd_3571578 1222624139349288278899745 := by
  unfold tailWord_3571578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32566537863697589451190847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86844100969860238536508925 32566537863697589451190847)
  ·
    refine ⟨48849806795546384176786271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32566537863697589451190847 48849806795546384176786271)
    ·
      refine ⟨73274710193319576265179407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48849806795546384176786271 73274710193319576265179407)
      ·
        refine ⟨109912065289979364397769111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73274710193319576265179407 109912065289979364397769111)
        ·
          refine ⟨164868097934969046596653667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109912065289979364397769111 164868097934969046596653667)
          ·
            refine ⟨247302146902453569894980501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164868097934969046596653667 247302146902453569894980501)
            ·
              refine ⟨11592288136052511088827211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247302146902453569894980501 11592288136052511088827211)
              ·
                refine ⟨17388432204078766633240817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592288136052511088827211 17388432204078766633240817)
                ·
                  refine ⟨13041324153059074974930613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17388432204078766633240817 13041324153059074974930613)
                  ·
                    refine ⟨1222624139349288278899745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13041324153059074974930613 1222624139349288278899745)
                    ·
                      rfl

theorem cell22_3571578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3571578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571578 prefixEnd_3571578 := by exact prefixLift 3571578
  have htrace : WordTrace (prefixWord ++ tailWord_3571578) baseStart_3571578 baseEnd_3571578 := by
    simpa [prefixWord, tailWord_3571578, baseEnd_3571578] using wordTrace_append hprefix tailTrace_3571578
  have hstable : (prefixWord ++ tailWord_3571578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571578).length < 2 ^ (prefixWord ++ tailWord_3571578).sum := by decide
  have hdescent : baseEnd_3571578 < baseStart_3571578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571670 : List Nat := [5, 2, 1, 1, 13]
def baseStart_3571670 : Nat := 118140960795 + 3571670 * 2 ^ 59
def prefixEnd_3571670 : Nat := 4983230072969 + 3 ^ 40 * 3571670 * 2
def baseEnd_3571670 : Nat := 5031504661849509076541

theorem tailTrace_3571670 : CollatzResearch.WordTrace tailWord_3571670 prefixEnd_3571670 5031504661849509076541 := by
  unfold tailWord_3571670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141844185653566094819529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86846337980304705011408309 8141844185653566094819529)
  ·
    refine ⟨6106383139240174571114647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8141844185653566094819529 6106383139240174571114647)
    ·
      refine ⟨9159574708860261856671971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106383139240174571114647 9159574708860261856671971)
      ·
        refine ⟨13739362063290392785007957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159574708860261856671971 13739362063290392785007957)
        ·
          refine ⟨5031504661849509076541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13739362063290392785007957 5031504661849509076541)
          ·
            rfl

theorem cell22_3571670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 13].length) (baseStart_3571670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571670 prefixEnd_3571670 := by exact prefixLift 3571670
  have htrace : WordTrace (prefixWord ++ tailWord_3571670) baseStart_3571670 baseEnd_3571670 := by
    simpa [prefixWord, tailWord_3571670, baseEnd_3571670] using wordTrace_append hprefix tailTrace_3571670
  have hstable : (prefixWord ++ tailWord_3571670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571670).length < 2 ^ (prefixWord ++ tailWord_3571670).sum := by decide
  have hdescent : baseEnd_3571670 < baseStart_3571670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571674 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_3571674 : Nat := 118140960795 + 3571674 * 2 ^ 59
def prefixEnd_3571674 : Nat := 4983230072969 + 3 ^ 40 * 3571674 * 2
def baseEnd_3571674 : Nat := 1222657002111176028499451

theorem tailTrace_3571674 : CollatzResearch.WordTrace tailWord_3571674 prefixEnd_3571674 1222657002111176028499451 := by
  unfold tailWord_3571674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567413215610641550064519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86846435241628377466838717 32567413215610641550064519)
  ·
    refine ⟨48851119823415962325096779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32567413215610641550064519 48851119823415962325096779)
    ·
      refine ⟨73276679735123943487645169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48851119823415962325096779 73276679735123943487645169)
      ·
        refine ⟨54957509801342957615733877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73276679735123943487645169 54957509801342957615733877)
        ·
          refine ⟨5152266543875902276475051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54957509801342957615733877 5152266543875902276475051)
          ·
            refine ⟨7728399815813853414712577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152266543875902276475051 7728399815813853414712577)
            ·
              refine ⟨5796299861860390061034433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7728399815813853414712577 5796299861860390061034433)
              ·
                refine ⟨4347224896395292545775825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796299861860390061034433 4347224896395292545775825)
                ·
                  refine ⟨3260418672296469409331869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347224896395292545775825 3260418672296469409331869)
                  ·
                    refine ⟨1222657002111176028499451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260418672296469409331869 1222657002111176028499451)
                    ·
                      rfl

theorem cell22_3571674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_3571674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571674 prefixEnd_3571674 := by exact prefixLift 3571674
  have htrace : WordTrace (prefixWord ++ tailWord_3571674) baseStart_3571674 baseEnd_3571674 := by
    simpa [prefixWord, tailWord_3571674, baseEnd_3571674] using wordTrace_append hprefix tailTrace_3571674
  have hstable : (prefixWord ++ tailWord_3571674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571674).length < 2 ^ (prefixWord ++ tailWord_3571674).sum := by decide
  have hdescent : baseEnd_3571674 < baseStart_3571674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571687 : List Nat := [1, 1, 5, 2, 3, 2, 1, 7]
def baseStart_3571687 : Nat := 118140960795 + 3571687 * 2 ^ 59
def prefixEnd_3571687 : Nat := 4983230072969 + 3 ^ 40 * 3571687 * 2
def baseEnd_3571687 : Nat := 135851272475205369769379

theorem tailTrace_3571687 : CollatzResearch.WordTrace tailWord_3571687 prefixEnd_3571687 135851272475205369769379 := by
  unfold tailWord_3571687
  simp only [CollatzResearch.WordTrace]
  refine ⟨130270127011395469420481315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86846751340930312946987543 130270127011395469420481315)
  ·
    refine ⟨195405190517093204130721973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130270127011395469420481315 195405190517093204130721973)
    ·
      refine ⟨18319236610977487887255185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195405190517093204130721973 18319236610977487887255185)
      ·
        refine ⟨13739427458233115915441389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18319236610977487887255185 13739427458233115915441389)
        ·
          refine ⟨5152285296837418468290521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13739427458233115915441389 5152285296837418468290521)
          ·
            refine ⟨3864213972628063851217891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152285296837418468290521 3864213972628063851217891)
            ·
              refine ⟨5796320958942095776826837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864213972628063851217891 5796320958942095776826837)
              ·
                refine ⟨135851272475205369769379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5796320958942095776826837 135851272475205369769379)
                ·
                  rfl

theorem cell22_3571687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 7].length) (baseStart_3571687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571687 prefixEnd_3571687 := by exact prefixLift 3571687
  have htrace : WordTrace (prefixWord ++ tailWord_3571687) baseStart_3571687 baseEnd_3571687 := by
    simpa [prefixWord, tailWord_3571687, baseEnd_3571687] using wordTrace_append hprefix tailTrace_3571687
  have hstable : (prefixWord ++ tailWord_3571687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571687).length < 2 ^ (prefixWord ++ tailWord_3571687).sum := by decide
  have hdescent : baseEnd_3571687 < baseStart_3571687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571719 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3571719 : Nat := 118140960795 + 3571719 * 2 ^ 59
def prefixEnd_3571719 : Nat := 4983230072969 + 3 ^ 40 * 3571719 * 2
def baseEnd_3571719 : Nat := 1222672406530810911124313

theorem tailTrace_3571719 : CollatzResearch.WordTrace tailWord_3571719 prefixEnd_3571719 1222672406530810911124313 := by
  unfold tailWord_3571719
  simp only [CollatzResearch.WordTrace]
  refine ⟨130271294147279538885646211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86847529431519692590430807 130271294147279538885646211)
  ·
    refine ⟨195406941220919308328469317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130271294147279538885646211 195406941220919308328469317)
    ·
      refine ⟨36638801478922370311587997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195406941220919308328469317 36638801478922370311587997)
      ·
        refine ⟨13739550554595888866845499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36638801478922370311587997 13739550554595888866845499)
        ·
          refine ⟨20609325831893833300268249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739550554595888866845499 20609325831893833300268249)
          ·
            refine ⟨15456994373920374975201187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20609325831893833300268249 15456994373920374975201187)
            ·
              refine ⟨23185491560880562462801781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456994373920374975201187 23185491560880562462801781)
              ·
                refine ⟨2173639833832552730887667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23185491560880562462801781 2173639833832552730887667)
                ·
                  refine ⟨3260459750748829096331501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173639833832552730887667 3260459750748829096331501)
                  ·
                    refine ⟨1222672406530810911124313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260459750748829096331501 1222672406530810911124313)
                    ·
                      rfl

theorem cell22_3571719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3571719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571719 prefixEnd_3571719 := by exact prefixLift 3571719
  have htrace : WordTrace (prefixWord ++ tailWord_3571719) baseStart_3571719 baseEnd_3571719 := by
    simpa [prefixWord, tailWord_3571719, baseEnd_3571719] using wordTrace_append hprefix tailTrace_3571719
  have hstable : (prefixWord ++ tailWord_3571719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571719).length < 2 ^ (prefixWord ++ tailWord_3571719).sum := by decide
  have hdescent : baseEnd_3571719 < baseStart_3571719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571725 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3571725 : Nat := 118140960795 + 3571725 * 2 ^ 59
def prefixEnd_3571725 : Nat := 4983230072969 + 3 ^ 40 * 3571725 * 2
def baseEnd_3571725 : Nat := 1222674460453428895474295

theorem tailTrace_3571725 : CollatzResearch.WordTrace tailWord_3571725 prefixEnd_3571725 1222674460453428895474295 := by
  unfold tailWord_3571725
  simp only [CollatzResearch.WordTrace]
  refine ⟨130271512985257801910364629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86847675323505201273576419 130271512985257801910364629)
  ·
    refine ⟨3053238585591979732274171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130271512985257801910364629 3053238585591979732274171)
    ·
      refine ⟨4579857878387969598411257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053238585591979732274171 4579857878387969598411257)
      ·
        refine ⟨3434893408790977198808443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4579857878387969598411257 3434893408790977198808443)
        ·
          refine ⟨5152340113186465798212665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434893408790977198808443 5152340113186465798212665)
          ·
            refine ⟨3864255084889849348659499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152340113186465798212665 3864255084889849348659499)
            ·
              refine ⟨5796382627334774022989249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864255084889849348659499 5796382627334774022989249)
              ·
                refine ⟨4347286970501080517241937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796382627334774022989249 4347286970501080517241937)
                ·
                  refine ⟨3260465227875810387931453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4347286970501080517241937 3260465227875810387931453)
                  ·
                    refine ⟨1222674460453428895474295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260465227875810387931453 1222674460453428895474295)
                    ·
                      rfl

theorem cell22_3571725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3571725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571725 prefixEnd_3571725 := by exact prefixLift 3571725
  have htrace : WordTrace (prefixWord ++ tailWord_3571725) baseStart_3571725 baseEnd_3571725 := by
    simpa [prefixWord, tailWord_3571725, baseEnd_3571725] using wordTrace_append hprefix tailTrace_3571725
  have hstable : (prefixWord ++ tailWord_3571725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571725).length < 2 ^ (prefixWord ++ tailWord_3571725).sum := by decide
  have hdescent : baseEnd_3571725 < baseStart_3571725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571760 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_3571760 : Nat := 118140960795 + 3571760 * 2 ^ 59
def prefixEnd_3571760 : Nat := 4983230072969 + 3 ^ 40 * 3571760 * 2
def baseEnd_3571760 : Nat := 407562147222900156949729

theorem tailTrace_3571760 : CollatzResearch.WordTrace tailWord_3571760 prefixEnd_3571760 407562147222900156949729 := by
  unfold tailWord_3571760
  simp only [CollatzResearch.WordTrace]
  refine ⟨65136394770065501443944367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86848526360087335258592489 65136394770065501443944367)
  ·
    refine ⟨97704592155098252165916551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65136394770065501443944367 97704592155098252165916551)
    ·
      refine ⟨146556888232647378248874827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97704592155098252165916551 146556888232647378248874827)
      ·
        refine ⟨219835332348971067373312241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146556888232647378248874827 219835332348971067373312241)
        ·
          refine ⟨164876499261728300529984181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219835332348971067373312241 164876499261728300529984181)
          ·
            refine ⟨15457171805787028174686017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164876499261728300529984181 15457171805787028174686017)
            ·
              refine ⟨11592878854340271131014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15457171805787028174686017 11592878854340271131014513)
              ·
                refine ⟨8694659140755203348260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11592878854340271131014513 8694659140755203348260885)
                ·
                  refine ⟨407562147222900156949729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8694659140755203348260885 407562147222900156949729)
                  ·
                    rfl

theorem cell22_3571760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_3571760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571760 prefixEnd_3571760 := by exact prefixLift 3571760
  have htrace : WordTrace (prefixWord ++ tailWord_3571760) baseStart_3571760 baseEnd_3571760 := by
    simpa [prefixWord, tailWord_3571760, baseEnd_3571760] using wordTrace_append hprefix tailTrace_3571760
  have hstable : (prefixWord ++ tailWord_3571760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571760).length < 2 ^ (prefixWord ++ tailWord_3571760).sum := by decide
  have hdescent : baseEnd_3571760 < baseStart_3571760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571762 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3571762 : Nat := 118140960795 + 3571762 * 2 ^ 59
def prefixEnd_3571762 : Nat := 4983230072969 + 3 ^ 40 * 3571762 * 2
def baseEnd_3571762 : Nat := 1222687126309573132299181

theorem tailTrace_3571762 : CollatzResearch.WordTrace tailWord_3571762 prefixEnd_3571762 1222687126309573132299181 := by
  unfold tailWord_3571762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568215621530939307365385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86848574990749171486307693 32568215621530939307365385)
  ·
    refine ⟨24426161716148204480524039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32568215621530939307365385 24426161716148204480524039)
    ·
      refine ⟨36639242574222306720786059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24426161716148204480524039 36639242574222306720786059)
      ·
        refine ⟨54958863861333460081179089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36639242574222306720786059 54958863861333460081179089)
        ·
          refine ⟨41219147896000095060884317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54958863861333460081179089 41219147896000095060884317)
          ·
            refine ⟨15457180461000035647831619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41219147896000095060884317 15457180461000035647831619)
            ·
              refine ⟨23185770691500053471747429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457180461000035647831619 23185770691500053471747429)
              ·
                refine ⟨4347332004656260025952643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23185770691500053471747429 4347332004656260025952643)
                ·
                  refine ⟨6520998006984390038928965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347332004656260025952643 6520998006984390038928965)
                  ·
                    refine ⟨1222687126309573132299181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520998006984390038928965 1222687126309573132299181)
                    ·
                      rfl

theorem cell22_3571762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3571762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571762 prefixEnd_3571762 := by exact prefixLift 3571762
  have htrace : WordTrace (prefixWord ++ tailWord_3571762) baseStart_3571762 baseEnd_3571762 := by
    simpa [prefixWord, tailWord_3571762, baseEnd_3571762] using wordTrace_append hprefix tailTrace_3571762
  have hstable : (prefixWord ++ tailWord_3571762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571762).length < 2 ^ (prefixWord ++ tailWord_3571762).sum := by decide
  have hdescent : baseEnd_3571762 < baseStart_3571762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571775 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3571775 : Nat := 118140960795 + 3571775 * 2 ^ 59
def prefixEnd_3571775 : Nat := 4983230072969 + 3 ^ 40 * 3571775 * 2
def baseEnd_3571775 : Nat := 1222691576475245431724141

theorem tailTrace_3571775 : CollatzResearch.WordTrace tailWord_3571775 prefixEnd_3571775 1222691576475245431724141 := by
  unfold tailWord_3571775
  simp only [CollatzResearch.WordTrace]
  refine ⟨130273336635076660449684779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86848891090051106966456519 130273336635076660449684779)
  ·
    refine ⟨195410004952614990674527169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130273336635076660449684779 195410004952614990674527169)
    ·
      refine ⟨146557503714461243005895377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195410004952614990674527169 146557503714461243005895377)
      ·
        refine ⟨109918127785845932254421533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146557503714461243005895377 109918127785845932254421533)
        ·
          refine ⟨41219297919692224595408075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109918127785845932254421533 41219297919692224595408075)
          ·
            refine ⟨61828946879538336893112113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41219297919692224595408075 61828946879538336893112113)
            ·
              refine ⟨46371710159653752669834085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61828946879538336893112113 46371710159653752669834085)
              ·
                refine ⟨8694695654935078625593891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46371710159653752669834085 8694695654935078625593891)
                ·
                  refine ⟨13042043482402617938390837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694695654935078625593891 13042043482402617938390837)
                  ·
                    refine ⟨1222691576475245431724141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13042043482402617938390837 1222691576475245431724141)
                    ·
                      rfl

theorem cell22_3571775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3571775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571775 prefixEnd_3571775 := by exact prefixLift 3571775
  have htrace : WordTrace (prefixWord ++ tailWord_3571775) baseStart_3571775 baseEnd_3571775 := by
    simpa [prefixWord, tailWord_3571775, baseEnd_3571775] using wordTrace_append hprefix tailTrace_3571775
  have hstable : (prefixWord ++ tailWord_3571775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571775).length < 2 ^ (prefixWord ++ tailWord_3571775).sum := by decide
  have hdescent : baseEnd_3571775 < baseStart_3571775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571794 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3571794 : Nat := 118140960795 + 3571794 * 2 ^ 59
def prefixEnd_3571794 : Nat := 4983230072969 + 3 ^ 40 * 3571794 * 2
def baseEnd_3571794 : Nat := 407566026854511905166361

theorem tailTrace_3571794 : CollatzResearch.WordTrace tailWord_3571794 prefixEnd_3571794 407566026854511905166361 := by
  unfold tailWord_3571794
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568507405501956673656609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86849353081338551129750957 32568507405501956673656609)
  ·
    refine ⟨24426380554126467505242457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32568507405501956673656609 24426380554126467505242457)
    ·
      refine ⟨18319785415594850628931843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24426380554126467505242457 18319785415594850628931843)
      ·
        refine ⟨27479678123392275943397765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18319785415594850628931843 27479678123392275943397765)
        ·
          refine ⟨5152439648136051739387081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27479678123392275943397765 5152439648136051739387081)
          ·
            refine ⟨3864329736102038804540311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152439648136051739387081 3864329736102038804540311)
            ·
              refine ⟨5796494604153058206810467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864329736102038804540311 5796494604153058206810467)
              ·
                refine ⟨8694741906229587310215701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796494604153058206810467 8694741906229587310215701)
                ·
                  refine ⟨407566026854511905166361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8694741906229587310215701 407566026854511905166361)
                  ·
                    rfl

theorem cell22_3571794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3571794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571794 prefixEnd_3571794 := by exact prefixLift 3571794
  have htrace : WordTrace (prefixWord ++ tailWord_3571794) baseStart_3571794 baseEnd_3571794 := by
    simpa [prefixWord, tailWord_3571794, baseEnd_3571794] using wordTrace_append hprefix tailTrace_3571794
  have hstable : (prefixWord ++ tailWord_3571794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571794).length < 2 ^ (prefixWord ++ tailWord_3571794).sum := by decide
  have hdescent : baseEnd_3571794 < baseStart_3571794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571944 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3571944 : Nat := 118140960795 + 3571944 * 2 ^ 59
def prefixEnd_3571944 : Nat := 4983230072969 + 3 ^ 40 * 3571944 * 2
def baseEnd_3571944 : Nat := 1222749428628985324248623

theorem tailTrace_3571944 : CollatzResearch.WordTrace tailWord_3571944 prefixEnd_3571944 1222749428628985324248623 := by
  unfold tailWord_3571944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65139750285732201156293443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86853000380976268208391257 65139750285732201156293443)
  ·
    refine ⟨97709625428598301734440165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65139750285732201156293443 97709625428598301734440165)
    ·
      refine ⟨18320554767862181575207531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97709625428598301734440165 18320554767862181575207531)
      ·
        refine ⟨27480832151793272362811297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18320554767862181575207531 27480832151793272362811297)
        ·
          refine ⟨20610624113844954272108473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27480832151793272362811297 20610624113844954272108473)
          ·
            refine ⟨15457968085383715704081355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20610624113844954272108473 15457968085383715704081355)
            ·
              refine ⟨23186952128075573556122033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15457968085383715704081355 23186952128075573556122033)
              ·
                refine ⟨17390214096056680167091525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23186952128075573556122033 17390214096056680167091525)
                ·
                  refine ⟨3260665143010627531329661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17390214096056680167091525 3260665143010627531329661)
                  ·
                    refine ⟨1222749428628985324248623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260665143010627531329661 1222749428628985324248623)
                    ·
                      rfl

theorem cell22_3571944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3571944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571944 prefixEnd_3571944 := by exact prefixLift 3571944
  have htrace : WordTrace (prefixWord ++ tailWord_3571944) baseStart_3571944 baseEnd_3571944 := by
    simpa [prefixWord, tailWord_3571944, baseEnd_3571944] using wordTrace_append hprefix tailTrace_3571944
  have hstable : (prefixWord ++ tailWord_3571944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571944).length < 2 ^ (prefixWord ++ tailWord_3571944).sum := by decide
  have hdescent : baseEnd_3571944 < baseStart_3571944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3571989 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3571989 : Nat := 118140960795 + 3571989 * 2 ^ 59
def prefixEnd_3571989 : Nat := 4983230072969 + 3 ^ 40 * 3571989 * 2
def baseEnd_3571989 : Nat := 1222764833048620206873485

theorem tailTrace_3571989 : CollatzResearch.WordTrace tailWord_3571989 prefixEnd_3571989 1222764833048620206873485 := by
  unfold tailWord_3571989
  simp only [CollatzResearch.WordTrace]
  refine ⟨130281141856301374997975021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86854094570867583331983347 130281141856301374997975021)
  ·
    refine ⟨48855428196113015624240633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130281141856301374997975021 48855428196113015624240633)
    ·
      refine ⟨36641571147084761718180475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48855428196113015624240633 36641571147084761718180475)
      ·
        refine ⟨54962356720627142577270713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36641571147084761718180475 54962356720627142577270713)
        ·
          refine ⟨41221767540470356932953035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54962356720627142577270713 41221767540470356932953035)
          ·
            refine ⟨61832651310705535399429553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41221767540470356932953035 61832651310705535399429553)
            ·
              refine ⟨46374488483029151549572165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61832651310705535399429553 46374488483029151549572165)
              ·
                refine ⟨8695216590567965915544781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46374488483029151549572165 8695216590567965915544781)
                ·
                  refine ⟨3260706221462987218329293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8695216590567965915544781 3260706221462987218329293)
                  ·
                    refine ⟨1222764833048620206873485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260706221462987218329293 1222764833048620206873485)
                    ·
                      rfl

theorem cell22_3571989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3571989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3571989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3571989 prefixEnd_3571989 := by exact prefixLift 3571989
  have htrace : WordTrace (prefixWord ++ tailWord_3571989) baseStart_3571989 baseEnd_3571989 := by
    simpa [prefixWord, tailWord_3571989, baseEnd_3571989] using wordTrace_append hprefix tailTrace_3571989
  have hstable : (prefixWord ++ tailWord_3571989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3571989).length < 2 ^ (prefixWord ++ tailWord_3571989).sum := by decide
  have hdescent : baseEnd_3571989 < baseStart_3571989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3571989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572019 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 5]
def baseStart_3572019 : Nat := 118140960795 + 3572019 * 2 ^ 59
def prefixEnd_3572019 : Nat := 4983230072969 + 3 ^ 40 * 3572019 * 2
def baseEnd_3572019 : Nat := 407591700887236709541131

theorem tailTrace_3572019 : CollatzResearch.WordTrace tailWord_3572019 prefixEnd_3572019 407591700887236709541131 := by
  unfold tailWord_3572019
  simp only [CollatzResearch.WordTrace]
  refine ⟨130282236046192690121567111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86854824030795126747711407 130282236046192690121567111)
  ·
    refine ⟨195423354069289035182350667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130282236046192690121567111 195423354069289035182350667)
    ·
      refine ⟨293135031103933552773526001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195423354069289035182350667 293135031103933552773526001)
      ·
        refine ⟨219851273327950164580144501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293135031103933552773526001 219851273327950164580144501)
        ·
          refine ⟨20611056874495327929388547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219851273327950164580144501 20611056874495327929388547)
          ·
            refine ⟨30916585311742991894082821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20611056874495327929388547 30916585311742991894082821)
            ·
              refine ⟨5796859745951810980140529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30916585311742991894082821 5796859745951810980140529)
              ·
                refine ⟨4347644809463858235105397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796859745951810980140529 4347644809463858235105397)
                ·
                  refine ⟨407591700887236709541131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4347644809463858235105397 407591700887236709541131)
                  ·
                    rfl

theorem cell22_3572019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 5].length) (baseStart_3572019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572019 prefixEnd_3572019 := by exact prefixLift 3572019
  have htrace : WordTrace (prefixWord ++ tailWord_3572019) baseStart_3572019 baseEnd_3572019 := by
    simpa [prefixWord, tailWord_3572019, baseEnd_3572019] using wordTrace_append hprefix tailTrace_3572019
  have hstable : (prefixWord ++ tailWord_3572019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572019).length < 2 ^ (prefixWord ++ tailWord_3572019).sum := by decide
  have hdescent : baseEnd_3572019 < baseStart_3572019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572049 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3572049 : Nat := 118140960795 + 3572049 * 2 ^ 59
def prefixEnd_3572049 : Nat := 4983230072969 + 3 ^ 40 * 3572049 * 2
def baseEnd_3572049 : Nat := 1222785372274800050373301

theorem tailTrace_3572049 : CollatzResearch.WordTrace tailWord_3572049 prefixEnd_3572049 1222785372274800050373301 := by
  unfold tailWord_3572049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130283330236084005245159201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86855553490722670163439467 130283330236084005245159201)
  ·
    refine ⟨97712497677063003933869401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130283330236084005245159201 97712497677063003933869401)
    ·
      refine ⟨73284373257797252950402051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97712497677063003933869401 73284373257797252950402051)
      ·
        refine ⟨109926559886695879425603077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73284373257797252950402051 109926559886695879425603077)
        ·
          refine ⟨20611229978755477392300577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109926559886695879425603077 20611229978755477392300577)
          ·
            refine ⟨15458422484066608044225433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20611229978755477392300577 15458422484066608044225433)
            ·
              refine ⟨11593816863049956033169075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15458422484066608044225433 11593816863049956033169075)
              ·
                refine ⟨17390725294574934049753613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593816863049956033169075 17390725294574934049753613)
                ·
                  refine ⟨6521521985465600268657605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17390725294574934049753613 6521521985465600268657605)
                  ·
                    refine ⟨1222785372274800050373301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6521521985465600268657605 1222785372274800050373301)
                    ·
                      rfl

theorem cell22_3572049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3572049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572049 prefixEnd_3572049 := by exact prefixLift 3572049
  have htrace : WordTrace (prefixWord ++ tailWord_3572049) baseStart_3572049 baseEnd_3572049 := by
    simpa [prefixWord, tailWord_3572049, baseEnd_3572049] using wordTrace_append hprefix tailTrace_3572049
  have hstable : (prefixWord ++ tailWord_3572049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572049).length < 2 ^ (prefixWord ++ tailWord_3572049).sum := by decide
  have hdescent : baseEnd_3572049 < baseStart_3572049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572126 : List Nat := [4, 3, 1, 2, 1, 1, 10]
def baseStart_3572126 : Nat := 118140960795 + 3572126 * 2 ^ 59
def prefixEnd_3572126 : Nat := 4983230072969 + 3 ^ 40 * 3572126 * 2
def baseEnd_3572126 : Nat := 45289323368459167266595

theorem tailTrace_3572126 : CollatzResearch.WordTrace tailWord_3572126 prefixEnd_3572126 45289323368459167266595 := by
  unfold tailWord_3572126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285767332100630924464029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86857425771203364930474821 16285767332100630924464029)
  ·
    refine ⟨6107162749537736596674011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16285767332100630924464029 6107162749537736596674011)
    ·
      refine ⟨9160744124306604895011017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6107162749537736596674011 9160744124306604895011017)
      ·
        refine ⟨6870558093229953671258263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9160744124306604895011017 6870558093229953671258263)
        ·
          refine ⟨10305837139844930506887395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870558093229953671258263 10305837139844930506887395)
          ·
            refine ⟨15458755709767395760331093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305837139844930506887395 15458755709767395760331093)
            ·
              refine ⟨45289323368459167266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15458755709767395760331093 45289323368459167266595)
              ·
                rfl

theorem cell22_3572126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 10].length) (baseStart_3572126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572126 prefixEnd_3572126 := by exact prefixLift 3572126
  have htrace : WordTrace (prefixWord ++ tailWord_3572126) baseStart_3572126 baseEnd_3572126 := by
    simpa [prefixWord, tailWord_3572126, baseEnd_3572126] using wordTrace_append hprefix tailTrace_3572126
  have hstable : (prefixWord ++ tailWord_3572126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572126).length < 2 ^ (prefixWord ++ tailWord_3572126).sum := by decide
  have hdescent : baseEnd_3572126 < baseStart_3572126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572235 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 1, 4]
def baseStart_3572235 : Nat := 118140960795 + 3572235 * 2 ^ 59
def prefixEnd_3572235 : Nat := 4983230072969 + 3 ^ 40 * 3572235 * 2
def baseEnd_3572235 : Nat := 1222849043875957565222731

theorem tailTrace_3572235 : CollatzResearch.WordTrace tailWord_3572235 prefixEnd_3572235 1222849043875957565222731 := by
  unfold tailWord_3572235
  simp only [CollatzResearch.WordTrace]
  refine ⟨130290114213410159011430159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86860076142273439340953439 130290114213410159011430159)
  ·
    refine ⟨195435171320115238517145239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130290114213410159011430159 195435171320115238517145239)
    ·
      refine ⟨293152756980172857775717859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195435171320115238517145239 293152756980172857775717859)
      ·
        refine ⟨439729135470259286663576789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293152756980172857775717859 439729135470259286663576789)
        ·
          refine ⟨10306151612584202031177581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 439729135470259286663576789 10306151612584202031177581)
          ·
            refine ⟨3864806854719075761691593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10306151612584202031177581 3864806854719075761691593)
            ·
              refine ⟨2898605141039306821268695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864806854719075761691593 2898605141039306821268695)
              ·
                refine ⟨4347907711558960231903043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898605141039306821268695 4347907711558960231903043)
                ·
                  refine ⟨6521861567338440347854565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347907711558960231903043 6521861567338440347854565)
                  ·
                    refine ⟨1222849043875957565222731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6521861567338440347854565 1222849043875957565222731)
                    ·
                      rfl

theorem cell22_3572235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 4].length) (baseStart_3572235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572235 prefixEnd_3572235 := by exact prefixLift 3572235
  have htrace : WordTrace (prefixWord ++ tailWord_3572235) baseStart_3572235 baseEnd_3572235 := by
    simpa [prefixWord, tailWord_3572235, baseEnd_3572235] using wordTrace_append hprefix tailTrace_3572235
  have hstable : (prefixWord ++ tailWord_3572235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572235).length < 2 ^ (prefixWord ++ tailWord_3572235).sum := by decide
  have hdescent : baseEnd_3572235 < baseStart_3572235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572248 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_3572248 : Nat := 118140960795 + 3572248 * 2 ^ 59
def prefixEnd_3572248 : Nat := 4983230072969 + 3 ^ 40 * 3572248 * 2
def baseEnd_3572248 : Nat := 1222853494041629864647691

theorem tailTrace_3572248 : CollatzResearch.WordTrace tailWord_3572248 prefixEnd_3572248 1222853494041629864647691 := by
  unfold tailWord_3572248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65145294181181531115826699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86860392241575374821102265 65145294181181531115826699)
  ·
    refine ⟨97717941271772296673740049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65145294181181531115826699 97717941271772296673740049)
    ·
      refine ⟨73288455953829222505305037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97717941271772296673740049 73288455953829222505305037)
      ·
        refine ⟨27483170982685958439489389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73288455953829222505305037 27483170982685958439489389)
        ·
          refine ⟨10306189118507234414808521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27483170982685958439489389 10306189118507234414808521)
          ·
            refine ⟨7729641838880425811106391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10306189118507234414808521 7729641838880425811106391)
            ·
              refine ⟨11594462758320638716659587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729641838880425811106391 11594462758320638716659587)
              ·
                refine ⟨17391694137480958074989381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11594462758320638716659587 17391694137480958074989381)
                ·
                  refine ⟨3260942650777679639060509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17391694137480958074989381 3260942650777679639060509)
                  ·
                    refine ⟨1222853494041629864647691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260942650777679639060509 1222853494041629864647691)
                    ·
                      rfl

theorem cell22_3572248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_3572248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572248 prefixEnd_3572248 := by exact prefixLift 3572248
  have htrace : WordTrace (prefixWord ++ tailWord_3572248) baseStart_3572248 baseEnd_3572248 := by
    simpa [prefixWord, tailWord_3572248, baseEnd_3572248] using wordTrace_append hprefix tailTrace_3572248
  have hstable : (prefixWord ++ tailWord_3572248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572248).length < 2 ^ (prefixWord ++ tailWord_3572248).sum := by decide
  have hdescent : baseEnd_3572248 < baseStart_3572248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572269 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3572269 : Nat := 118140960795 + 3572269 * 2 ^ 59
def prefixEnd_3572269 : Nat := 4983230072969 + 3 ^ 40 * 3572269 * 2
def baseEnd_3572269 : Nat := 1222860682770792809872627

theorem tailTrace_3572269 : CollatzResearch.WordTrace tailWord_3572269 prefixEnd_3572269 1222860682770792809872627 := by
  unfold tailWord_3572269
  simp only [CollatzResearch.WordTrace]
  refine ⟨130291354295286982818167861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86860902863524655212111907 130291354295286982818167861)
  ·
    refine ⟨12214814465183154639203237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130291354295286982818167861 12214814465183154639203237)
    ·
      refine ⟨2290277712221841494850607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12214814465183154639203237 2290277712221841494850607)
      ·
        refine ⟨3435416568332762242275911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290277712221841494850607 3435416568332762242275911)
        ·
          refine ⟨5153124852499143363413867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435416568332762242275911 5153124852499143363413867)
          ·
            refine ⟨7729687278748715045120801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153124852499143363413867 7729687278748715045120801)
            ·
              refine ⟨5797265459061536283840601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729687278748715045120801 5797265459061536283840601)
              ·
                refine ⟨4347949094296152212880451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797265459061536283840601 4347949094296152212880451)
                ·
                  refine ⟨6521923641444228319320677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347949094296152212880451 6521923641444228319320677)
                  ·
                    refine ⟨1222860682770792809872627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6521923641444228319320677 1222860682770792809872627)
                    ·
                      rfl

theorem cell22_3572269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3572269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572269 prefixEnd_3572269 := by exact prefixLift 3572269
  have htrace : WordTrace (prefixWord ++ tailWord_3572269) baseStart_3572269 baseEnd_3572269 := by
    simpa [prefixWord, tailWord_3572269, baseEnd_3572269] using wordTrace_append hprefix tailTrace_3572269
  have hstable : (prefixWord ++ tailWord_3572269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572269).length < 2 ^ (prefixWord ++ tailWord_3572269).sum := by decide
  have hdescent : baseEnd_3572269 < baseStart_3572269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572278 : List Nat := [5, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3572278 : Nat := 118140960795 + 3572278 * 2 ^ 59
def prefixEnd_3572278 : Nat := 4983230072969 + 3 ^ 40 * 3572278 * 2
def baseEnd_3572278 : Nat := 135873751517191087377511

theorem tailTrace_3572278 : CollatzResearch.WordTrace tailWord_3572278 prefixEnd_3572278 135873751517191087377511 := by
  unfold tailWord_3572278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8143230159515898584702843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86861121701502918236830325 8143230159515898584702843)
  ·
    refine ⟨12214845239273847877054265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8143230159515898584702843 12214845239273847877054265)
    ·
      refine ⟨9161133929455385907790699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12214845239273847877054265 9161133929455385907790699)
      ·
        refine ⟨13741700894183078861686049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161133929455385907790699 13741700894183078861686049)
        ·
          refine ⟨10306275670637309146264537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13741700894183078861686049 10306275670637309146264537)
          ·
            refine ⟨7729706752977981859698403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10306275670637309146264537 7729706752977981859698403)
            ·
              refine ⟨11594560129466972789547605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729706752977981859698403 11594560129466972789547605)
              ·
                refine ⟨135873751517191087377511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11594560129466972789547605 135873751517191087377511)
                ·
                  rfl

theorem cell22_3572278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3572278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572278 prefixEnd_3572278 := by exact prefixLift 3572278
  have htrace : WordTrace (prefixWord ++ tailWord_3572278) baseStart_3572278 baseEnd_3572278 := by
    simpa [prefixWord, tailWord_3572278, baseEnd_3572278] using wordTrace_append hprefix tailTrace_3572278
  have hstable : (prefixWord ++ tailWord_3572278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572278).length < 2 ^ (prefixWord ++ tailWord_3572278).sum := by decide
  have hdescent : baseEnd_3572278 < baseStart_3572278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572306 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_3572306 : Nat := 118140960795 + 3572306 * 2 ^ 59
def prefixEnd_3572306 : Nat := 4983230072969 + 3 ^ 40 * 3572306 * 2
def baseEnd_3572306 : Nat := 407624449542312348899171

theorem tailTrace_3572306 : CollatzResearch.WordTrace tailWord_3572306 prefixEnd_3572306 407624449542312348899171 := by
  unfold tailWord_3572306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32573175949038234534316193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86861802530768625424843181 32573175949038234534316193)
  ·
    refine ⟨24429881961778675900737145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32573175949038234534316193 24429881961778675900737145)
    ·
      refine ⟨18322411471334006925552859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24429881961778675900737145 18322411471334006925552859)
      ·
        refine ⟨27483617207001010388329289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322411471334006925552859 27483617207001010388329289)
        ·
          refine ⟨20612712905250757791246967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27483617207001010388329289 20612712905250757791246967)
          ·
            refine ⟨30919069357876136686870451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20612712905250757791246967 30919069357876136686870451)
            ·
              refine ⟨46378604036814205030305677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30919069357876136686870451 46378604036814205030305677)
              ·
                refine ⟨17391976513805326886364629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46378604036814205030305677 17391976513805326886364629)
                ·
                  refine ⟨407624449542312348899171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17391976513805326886364629 407624449542312348899171)
                  ·
                    rfl

theorem cell22_3572306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_3572306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572306 prefixEnd_3572306 := by exact prefixLift 3572306
  have htrace : WordTrace (prefixWord ++ tailWord_3572306) baseStart_3572306 baseEnd_3572306 := by
    simpa [prefixWord, tailWord_3572306, baseEnd_3572306] using wordTrace_append hprefix tailTrace_3572306
  have hstable : (prefixWord ++ tailWord_3572306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572306).length < 2 ^ (prefixWord ++ tailWord_3572306).sum := by decide
  have hdescent : baseEnd_3572306 < baseStart_3572306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572434 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3572434 : Nat := 118140960795 + 3572434 * 2 ^ 59
def prefixEnd_3572434 : Nat := 4983230072969 + 3 ^ 40 * 3572434 * 2
def baseEnd_3572434 : Nat := 1222917165642787379497121

theorem tailTrace_3572434 : CollatzResearch.WordTrace tailWord_3572434 prefixEnd_3572434 1222917165642787379497121 := by
  unfold tailWord_3572434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32574343084922303999481089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86864914893126143998616237 32574343084922303999481089)
  ·
    refine ⟨24430757313691727999610817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32574343084922303999481089 24430757313691727999610817)
    ·
      refine ⟨18323067985268795999708113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24430757313691727999610817 18323067985268795999708113)
      ·
        refine ⟨13742300988951596999781085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18323067985268795999708113 13742300988951596999781085)
        ·
          refine ⟨5153362870856848874917907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13742300988951596999781085 5153362870856848874917907)
          ·
            refine ⟨7730044306285273312376861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153362870856848874917907 7730044306285273312376861)
            ·
              refine ⟨2898766614856977492141323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7730044306285273312376861 2898766614856977492141323)
              ·
                refine ⟨4348149922285466238211985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898766614856977492141323 4348149922285466238211985)
                ·
                  refine ⟨3261112441714099678658989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4348149922285466238211985 3261112441714099678658989)
                  ·
                    refine ⟨1222917165642787379497121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261112441714099678658989 1222917165642787379497121)
                    ·
                      rfl

theorem cell22_3572434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3572434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572434 prefixEnd_3572434 := by exact prefixLift 3572434
  have htrace : WordTrace (prefixWord ++ tailWord_3572434) baseStart_3572434 baseEnd_3572434 := by
    simpa [prefixWord, tailWord_3572434, baseEnd_3572434] using wordTrace_append hprefix tailTrace_3572434
  have hstable : (prefixWord ++ tailWord_3572434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572434).length < 2 ^ (prefixWord ++ tailWord_3572434).sum := by decide
  have hdescent : baseEnd_3572434 < baseStart_3572434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572565 : List Nat := [1, 3, 2, 2, 2, 1, 5, 6]
def baseStart_3572565 : Nat := 118140960795 + 3572565 * 2 ^ 59
def prefixEnd_3572565 : Nat := 4983230072969 + 3 ^ 40 * 3572565 * 2
def baseEnd_3572565 : Nat := 135884667735549633830191

theorem tailTrace_3572565 : CollatzResearch.WordTrace tailWord_3572565 prefixEnd_3572565 135884667735549633830191 := by
  unfold tailWord_3572565
  simp only [CollatzResearch.WordTrace]
  refine ⟨130302150302214625370943149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86868100201476416913962099 130302150302214625370943149)
  ·
    refine ⟨48863306363330484514103681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130302150302214625370943149 48863306363330484514103681)
    ·
      refine ⟨36647479772497863385577761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48863306363330484514103681 36647479772497863385577761)
      ·
        refine ⟨27485609829373397539183321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36647479772497863385577761 27485609829373397539183321)
        ·
          refine ⟨20614207372030048154387491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27485609829373397539183321 20614207372030048154387491)
          ·
            refine ⟨30921311058045072231581237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20614207372030048154387491 30921311058045072231581237)
            ·
              refine ⟨2898872911691725521710741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30921311058045072231581237 2898872911691725521710741)
              ·
                refine ⟨135884667735549633830191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2898872911691725521710741 135884667735549633830191)
                ·
                  rfl

theorem cell22_3572565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 6].length) (baseStart_3572565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572565 prefixEnd_3572565 := by exact prefixLift 3572565
  have htrace : WordTrace (prefixWord ++ tailWord_3572565) baseStart_3572565 baseEnd_3572565 := by
    simpa [prefixWord, tailWord_3572565, baseEnd_3572565] using wordTrace_append hprefix tailTrace_3572565
  have hstable : (prefixWord ++ tailWord_3572565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572565).length < 2 ^ (prefixWord ++ tailWord_3572565).sum := by decide
  have hdescent : baseEnd_3572565 < baseStart_3572565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572567 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 2, 4]
def baseStart_3572567 : Nat := 118140960795 + 3572567 * 2 ^ 59
def prefixEnd_3572567 : Nat := 4983230072969 + 3 ^ 40 * 3572567 * 2
def baseEnd_3572567 : Nat := 1222962694260819365921713

theorem tailTrace_3572567 : CollatzResearch.WordTrace tailWord_3572567 prefixEnd_3572567 1222962694260819365921713 := by
  unfold tailWord_3572567
  simp only [CollatzResearch.WordTrace]
  refine ⟨130302223248207379712515955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86868148832138253141677303 130302223248207379712515955)
  ·
    refine ⟨195453334872311069568773933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130302223248207379712515955 195453334872311069568773933)
    ·
      refine ⟨73295000577116651088290225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195453334872311069568773933 73295000577116651088290225)
      ·
        refine ⟨54971250432837488316217669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73295000577116651088290225 54971250432837488316217669)
        ·
          refine ⟨10307109456157029059290813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54971250432837488316217669 10307109456157029059290813)
          ·
            refine ⟨3865166046058885897234055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10307109456157029059290813 3865166046058885897234055)
            ·
              refine ⟨5797749069088328845851083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865166046058885897234055 5797749069088328845851083)
              ·
                refine ⟨8696623603632493268776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797749069088328845851083 8696623603632493268776625)
                ·
                  refine ⟨6522467702724369951582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8696623603632493268776625 6522467702724369951582469)
                  ·
                    refine ⟨1222962694260819365921713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6522467702724369951582469 1222962694260819365921713)
                    ·
                      rfl

theorem cell22_3572567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_3572567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572567 prefixEnd_3572567 := by exact prefixLift 3572567
  have htrace : WordTrace (prefixWord ++ tailWord_3572567) baseStart_3572567 baseEnd_3572567 := by
    simpa [prefixWord, tailWord_3572567, baseEnd_3572567] using wordTrace_append hprefix tailTrace_3572567
  have hstable : (prefixWord ++ tailWord_3572567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572567).length < 2 ^ (prefixWord ++ tailWord_3572567).sum := by decide
  have hdescent : baseEnd_3572567 < baseStart_3572567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572597 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3572597 : Nat := 118140960795 + 3572597 * 2 ^ 59
def prefixEnd_3572597 : Nat := 4983230072969 + 3 ^ 40 * 3572597 * 2
def baseEnd_3572597 : Nat := 1222972963873909287671621

theorem tailTrace_3572597 : CollatzResearch.WordTrace tailWord_3572597 prefixEnd_3572597 1222972963873909287671621 := by
  unfold tailWord_3572597
  simp only [CollatzResearch.WordTrace]
  refine ⟨130303317438098694836108045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86868878292065796557405363 130303317438098694836108045)
  ·
    refine ⟨48863744039287010563540517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130303317438098694836108045 48863744039287010563540517)
    ·
      refine ⟨9161952007366314480663847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48863744039287010563540517 9161952007366314480663847)
      ·
        refine ⟨13742928011049471720995771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161952007366314480663847 13742928011049471720995771)
        ·
          refine ⟨20614392016574207581493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13742928011049471720995771 20614392016574207581493657)
          ·
            refine ⟨15460794012430655686120243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20614392016574207581493657 15460794012430655686120243)
            ·
              refine ⟨23191191018645983529180365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15460794012430655686120243 23191191018645983529180365)
              ·
                refine ⟨8696696631992243823442637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23191191018645983529180365 8696696631992243823442637)
                ·
                  refine ⟨3261261236997091433790989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8696696631992243823442637 3261261236997091433790989)
                  ·
                    refine ⟨1222972963873909287671621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261261236997091433790989 1222972963873909287671621)
                    ·
                      rfl

theorem cell22_3572597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3572597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572597 prefixEnd_3572597 := by exact prefixLift 3572597
  have htrace : WordTrace (prefixWord ++ tailWord_3572597) baseStart_3572597 baseEnd_3572597 := by
    simpa [prefixWord, tailWord_3572597, baseEnd_3572597] using wordTrace_append hprefix tailTrace_3572597
  have hstable : (prefixWord ++ tailWord_3572597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572597).length < 2 ^ (prefixWord ++ tailWord_3572597).sum := by decide
  have hdescent : baseEnd_3572597 < baseStart_3572597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572608 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_3572608 : Nat := 118140960795 + 3572608 * 2 ^ 59
def prefixEnd_3572608 : Nat := 4983230072969 + 3 ^ 40 * 3572608 * 2
def baseEnd_3572608 : Nat := 1222976729398708925646587

theorem tailTrace_3572608 : CollatzResearch.WordTrace tailWord_3572608 prefixEnd_3572608 1222976729398708925646587 := by
  unfold tailWord_3572608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65151859320529421857379239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86869145760705895809838985 65151859320529421857379239)
  ·
    refine ⟨97727788980794132786068859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65151859320529421857379239 97727788980794132786068859)
    ·
      refine ⟨146591683471191199179103289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97727788980794132786068859 146591683471191199179103289)
      ·
        refine ⟨109943762603393399384327467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146591683471191199179103289 109943762603393399384327467)
        ·
          refine ⟨164915643905090099076491201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109943762603393399384327467 164915643905090099076491201)
          ·
            refine ⟨123686732928817574307368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164915643905090099076491201 123686732928817574307368401)
            ·
              refine ⟨92765049696613180730526301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123686732928817574307368401 92765049696613180730526301)
              ·
                refine ⟨34786893636229942773947363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92765049696613180730526301 34786893636229942773947363)
                ·
                  refine ⟨52180340454344914160921045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34786893636229942773947363 52180340454344914160921045)
                  ·
                    refine ⟨1222976729398708925646587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52180340454344914160921045 1222976729398708925646587)
                    ·
                      rfl

theorem cell22_3572608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_3572608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572608 prefixEnd_3572608 := by exact prefixLift 3572608
  have htrace : WordTrace (prefixWord ++ tailWord_3572608) baseStart_3572608 baseEnd_3572608 := by
    simpa [prefixWord, tailWord_3572608, baseEnd_3572608] using wordTrace_append hprefix tailTrace_3572608
  have hstable : (prefixWord ++ tailWord_3572608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572608).length < 2 ^ (prefixWord ++ tailWord_3572608).sum := by decide
  have hdescent : baseEnd_3572608 < baseStart_3572608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572706 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3572706 : Nat := 118140960795 + 3572706 * 2 ^ 59
def prefixEnd_3572706 : Nat := 4983230072969 + 3 ^ 40 * 3572706 * 2
def baseEnd_3572706 : Nat := 407670092267156445565429

theorem tailTrace_3572706 : CollatzResearch.WordTrace tailWord_3572706 prefixEnd_3572706 407670092267156445565429 := by
  unfold tailWord_3572706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32576823248675951612956493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86871528663135870967883981 32576823248675951612956493)
  ·
    refine ⟨12216308718253481854858685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32576823248675951612956493 12216308718253481854858685)
    ·
      refine ⟨4581115769345055695572007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12216308718253481854858685 4581115769345055695572007)
      ·
        refine ⟨6871673654017583543358011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581115769345055695572007 6871673654017583543358011)
        ·
          refine ⟨10307510481026375315037017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871673654017583543358011 10307510481026375315037017)
          ·
            refine ⟨7730632860769781486277763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307510481026375315037017 7730632860769781486277763)
            ·
              refine ⟨11595949291154672229416645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730632860769781486277763 11595949291154672229416645)
              ·
                refine ⟨2174240492091501043015621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11595949291154672229416645 2174240492091501043015621)
                ·
                  refine ⟨407670092267156445565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174240492091501043015621 407670092267156445565429)
                  ·
                    rfl

theorem cell22_3572706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3572706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572706 prefixEnd_3572706 := by exact prefixLift 3572706
  have htrace : WordTrace (prefixWord ++ tailWord_3572706) baseStart_3572706 baseEnd_3572706 := by
    simpa [prefixWord, tailWord_3572706, baseEnd_3572706] using wordTrace_append hprefix tailTrace_3572706
  have hstable : (prefixWord ++ tailWord_3572706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572706).length < 2 ^ (prefixWord ++ tailWord_3572706).sum := by decide
  have hdescent : baseEnd_3572706 < baseStart_3572706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572732 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_3572732 : Nat := 118140960795 + 3572732 * 2 ^ 59
def prefixEnd_3572732 : Nat := 4983230072969 + 3 ^ 40 * 3572732 * 2
def baseEnd_3572732 : Nat := 1223019177132813935546207

theorem tailTrace_3572732 : CollatzResearch.WordTrace tailWord_3572732 prefixEnd_3572732 1223019177132813935546207 := by
  unfold tailWord_3572732
  simp only [CollatzResearch.WordTrace]
  refine ⟨65154120646304806446136225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86872160861739741928181633 65154120646304806446136225)
  ·
    refine ⟨48865590484728604834602169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65154120646304806446136225 48865590484728604834602169)
    ·
      refine ⟨36649192863546453625951627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48865590484728604834602169 36649192863546453625951627)
      ·
        refine ⟨54973789295319680438927441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36649192863546453625951627 54973789295319680438927441)
        ·
          refine ⟨41230341971489760329195581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54973789295319680438927441 41230341971489760329195581)
          ·
            refine ⟨15461378239308660123448343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41230341971489760329195581 15461378239308660123448343)
            ·
              refine ⟨23192067358962990185172515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15461378239308660123448343 23192067358962990185172515)
              ·
                refine ⟨34788101038444485277758773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23192067358962990185172515 34788101038444485277758773)
                ·
                  refine ⟨3261384472354170494789885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34788101038444485277758773 3261384472354170494789885)
                  ·
                    refine ⟨1223019177132813935546207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261384472354170494789885 1223019177132813935546207)
                    ·
                      rfl

theorem cell22_3572732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_3572732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572732 prefixEnd_3572732 := by exact prefixLift 3572732
  have htrace : WordTrace (prefixWord ++ tailWord_3572732) baseStart_3572732 baseEnd_3572732 := by
    simpa [prefixWord, tailWord_3572732, baseEnd_3572732] using wordTrace_append hprefix tailTrace_3572732
  have hstable : (prefixWord ++ tailWord_3572732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572732).length < 2 ^ (prefixWord ++ tailWord_3572732).sum := by decide
  have hdescent : baseEnd_3572732 < baseStart_3572732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572830 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3572830 : Nat := 118140960795 + 3572830 * 2 ^ 59
def prefixEnd_3572830 : Nat := 4983230072969 + 3 ^ 40 * 3572830 * 2
def baseEnd_3572830 : Nat := 407684241511858115531969

theorem tailTrace_3572830 : CollatzResearch.WordTrace tailWord_3572830 prefixEnd_3572830 407684241511858115531969 := by
  unfold tailWord_3572830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288976955781821953667493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86874543764169717086226629 16288976955781821953667493)
  ·
    refine ⟨3054183179209091616312655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16288976955781821953667493 3054183179209091616312655)
    ·
      refine ⟨4581274768813637424468983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054183179209091616312655 4581274768813637424468983)
      ·
        refine ⟨6871912153220456136703475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581274768813637424468983 6871912153220456136703475)
        ·
          refine ⟨10307868229830684205055213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871912153220456136703475 10307868229830684205055213)
          ·
            refine ⟨3865450586186506576895705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10307868229830684205055213 3865450586186506576895705)
            ·
              refine ⟨2899087939639879932671779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865450586186506576895705 2899087939639879932671779)
              ·
                refine ⟨4348631909459819899007669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899087939639879932671779 4348631909459819899007669)
                ·
                  refine ⟨407684241511858115531969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4348631909459819899007669 407684241511858115531969)
                  ·
                    rfl

theorem cell22_3572830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3572830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572830 prefixEnd_3572830 := by exact prefixLift 3572830
  have htrace : WordTrace (prefixWord ++ tailWord_3572830) baseStart_3572830 baseEnd_3572830 := by
    simpa [prefixWord, tailWord_3572830, baseEnd_3572830] using wordTrace_append hprefix tailTrace_3572830
  have hstable : (prefixWord ++ tailWord_3572830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572830).length < 2 ^ (prefixWord ++ tailWord_3572830).sum := by decide
  have hdescent : baseEnd_3572830 < baseStart_3572830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572837 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3572837 : Nat := 118140960795 + 3572837 * 2 ^ 59
def prefixEnd_3572837 : Nat := 4983230072969 + 3 ^ 40 * 3572837 * 2
def baseEnd_3572837 : Nat := 1223055120778628661670885

theorem tailTrace_3572837 : CollatzResearch.WordTrace tailWord_3572837 prefixEnd_3572837 1223055120778628661670885 := by
  unfold tailWord_3572837
  simp only [CollatzResearch.WordTrace]
  refine ⟨130312070957229215824844765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86874713971486143883229843 130312070957229215824844765)
  ·
    refine ⟨48867026608960955934316787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130312070957229215824844765 48867026608960955934316787)
    ·
      refine ⟨73300539913441433901475181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48867026608960955934316787 73300539913441433901475181)
      ·
        refine ⟨27487702467540537713053193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73300539913441433901475181 27487702467540537713053193)
        ·
          refine ⟨20615776850655403284789895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27487702467540537713053193 20615776850655403284789895)
          ·
            refine ⟨30923665275983104927184843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20615776850655403284789895 30923665275983104927184843)
            ·
              refine ⟨46385497913974657390777265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30923665275983104927184843 46385497913974657390777265)
              ·
                refine ⟨34789123435480993043082949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46385497913974657390777265 34789123435480993043082949)
                ·
                  refine ⟨6522960644152686195578053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34789123435480993043082949 6522960644152686195578053)
                  ·
                    refine ⟨1223055120778628661670885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6522960644152686195578053 1223055120778628661670885)
                    ·
                      rfl

theorem cell22_3572837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3572837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572837 prefixEnd_3572837 := by exact prefixLift 3572837
  have htrace : WordTrace (prefixWord ++ tailWord_3572837) baseStart_3572837 baseEnd_3572837 := by
    simpa [prefixWord, tailWord_3572837, baseEnd_3572837] using wordTrace_append hprefix tailTrace_3572837
  have hstable : (prefixWord ++ tailWord_3572837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572837).length < 2 ^ (prefixWord ++ tailWord_3572837).sum := by decide
  have hdescent : baseEnd_3572837 < baseStart_3572837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572961 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3572961 : Nat := 118140960795 + 3572961 * 2 ^ 59
def prefixEnd_3572961 : Nat := 4983230072969 + 3 ^ 40 * 3572961 * 2
def baseEnd_3572961 : Nat := 1223097568512733671570505

theorem tailTrace_3572961 : CollatzResearch.WordTrace tailWord_3572961 prefixEnd_3572961 1223097568512733671570505 := by
  unfold tailWord_3572961
  simp only [CollatzResearch.WordTrace]
  refine ⟨130316593608779985002358737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86877729072519990001572491 130316593608779985002358737)
  ·
    refine ⟨97737445206584988751769053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130316593608779985002358737 97737445206584988751769053)
    ·
      refine ⟨36651541952469370781913395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97737445206584988751769053 36651541952469370781913395)
      ·
        refine ⟨54977312928704056172870093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36651541952469370781913395 54977312928704056172870093)
        ·
          refine ⟨20616492348264021064826285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54977312928704056172870093 20616492348264021064826285)
          ·
            refine ⟨7731184630599007899309857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20616492348264021064826285 7731184630599007899309857)
            ·
              refine ⟨5798388472949255924482393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731184630599007899309857 5798388472949255924482393)
              ·
                refine ⟨4348791354711941943361795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5798388472949255924482393 4348791354711941943361795)
                ·
                  refine ⟨6523187032067912915042693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348791354711941943361795 6523187032067912915042693)
                  ·
                    refine ⟨1223097568512733671570505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523187032067912915042693 1223097568512733671570505)
                    ·
                      rfl

theorem cell22_3572961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3572961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572961 prefixEnd_3572961 := by exact prefixLift 3572961
  have htrace : WordTrace (prefixWord ++ tailWord_3572961) baseStart_3572961 baseEnd_3572961 := by
    simpa [prefixWord, tailWord_3572961, baseEnd_3572961] using wordTrace_append hprefix tailTrace_3572961
  have hstable : (prefixWord ++ tailWord_3572961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572961).length < 2 ^ (prefixWord ++ tailWord_3572961).sum := by decide
  have hdescent : baseEnd_3572961 < baseStart_3572961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572974 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3572974 : Nat := 118140960795 + 3572974 * 2 ^ 59
def prefixEnd_3572974 : Nat := 4983230072969 + 3 ^ 40 * 3572974 * 2
def baseEnd_3572974 : Nat := 1223102018678405970995465

theorem tailTrace_3572974 : CollatzResearch.WordTrace tailWord_3572974 prefixEnd_3572974 1223102018678405970995465 := by
  unfold tailWord_3572974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289633469716611027822747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86878045171821925481721317 16289633469716611027822747)
  ·
    refine ⟨24434450204574916541734121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16289633469716611027822747 24434450204574916541734121)
    ·
      refine ⟨18325837653431187406300591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24434450204574916541734121 18325837653431187406300591)
      ·
        refine ⟨27488756480146781109450887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325837653431187406300591 27488756480146781109450887)
        ·
          refine ⟨41233134720220171664176331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488756480146781109450887 41233134720220171664176331)
          ·
            refine ⟨61849702080330257496264497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41233134720220171664176331 61849702080330257496264497)
            ·
              refine ⟨46387276560247693122198373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61849702080330257496264497 46387276560247693122198373)
              ·
                refine ⟨8697614355046442460412195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46387276560247693122198373 8697614355046442460412195)
                ·
                  refine ⟨13046421532569663690618293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697614355046442460412195 13046421532569663690618293)
                  ·
                    refine ⟨1223102018678405970995465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13046421532569663690618293 1223102018678405970995465)
                    ·
                      rfl

theorem cell22_3572974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3572974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572974 prefixEnd_3572974 := by exact prefixLift 3572974
  have htrace : WordTrace (prefixWord ++ tailWord_3572974) baseStart_3572974 baseEnd_3572974 := by
    simpa [prefixWord, tailWord_3572974, baseEnd_3572974] using wordTrace_append hprefix tailTrace_3572974
  have hstable : (prefixWord ++ tailWord_3572974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572974).length < 2 ^ (prefixWord ++ tailWord_3572974).sum := by decide
  have hdescent : baseEnd_3572974 < baseStart_3572974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3572993 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 4]
def baseStart_3572993 : Nat := 118140960795 + 3572993 * 2 ^ 59
def prefixEnd_3572993 : Nat := 4983230072969 + 3 ^ 40 * 3572993 * 2
def baseEnd_3572993 : Nat := 407702840922232084923469

theorem tailTrace_3572993 : CollatzResearch.WordTrace tailWord_3572993 prefixEnd_3572993 407702840922232084923469 := by
  unfold tailWord_3572993
  simp only [CollatzResearch.WordTrace]
  refine ⟨130317760744664054467523633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86878507163109369645015755 130317760744664054467523633)
  ·
    refine ⟨97738320558498040850642725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130317760744664054467523633 97738320558498040850642725)
    ·
      refine ⟨18325935104718382659495511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97738320558498040850642725 18325935104718382659495511)
      ·
        refine ⟨27488902657077573989243267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325935104718382659495511 27488902657077573989243267)
        ·
          refine ⟨41233353985616360983864901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488902657077573989243267 41233353985616360983864901)
          ·
            refine ⟨7731253872303067684474669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41233353985616360983864901 7731253872303067684474669)
            ·
              refine ⟨2899220202113650381678001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7731253872303067684474669 2899220202113650381678001)
              ·
                refine ⟨2174415151585237786258501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899220202113650381678001 2174415151585237786258501)
                ·
                  refine ⟨407702840922232084923469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174415151585237786258501 407702840922232084923469)
                  ·
                    rfl

theorem cell22_3572993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_3572993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3572993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3572993 prefixEnd_3572993 := by exact prefixLift 3572993
  have htrace : WordTrace (prefixWord ++ tailWord_3572993) baseStart_3572993 baseEnd_3572993 := by
    simpa [prefixWord, tailWord_3572993, baseEnd_3572993] using wordTrace_append hprefix tailTrace_3572993
  have hstable : (prefixWord ++ tailWord_3572993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3572993).length < 2 ^ (prefixWord ++ tailWord_3572993).sum := by decide
  have hdescent : baseEnd_3572993 < baseStart_3572993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3572993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573004 : List Nat := [2, 2, 1, 2, 2, 4, 2, 7]
def baseStart_3573004 : Nat := 118140960795 + 3573004 * 2 ^ 59
def prefixEnd_3573004 : Nat := 4983230072969 + 3 ^ 40 * 3573004 * 2
def baseEnd_3573004 : Nat := 135901365365721765860597

theorem tailTrace_3573004 : CollatzResearch.WordTrace tailWord_3573004 prefixEnd_3573004 135901365365721765860597 := by
  unfold tailWord_3573004
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159080973812101673087033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86878774631749468897449377 65159080973812101673087033)
  ·
    refine ⟨48869310730359076254815275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65159080973812101673087033 48869310730359076254815275)
    ·
      refine ⟨73303966095538614382222913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48869310730359076254815275 73303966095538614382222913)
      ·
        refine ⟨54977974571653960786667185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73303966095538614382222913 54977974571653960786667185)
        ·
          refine ⟨41233480928740470590000389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54977974571653960786667185 41233480928740470590000389)
          ·
            refine ⟨7731277674138838235625073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41233480928740470590000389 7731277674138838235625073)
            ·
              refine ⟨5798458255604128676718805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7731277674138838235625073 5798458255604128676718805)
              ·
                refine ⟨135901365365721765860597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5798458255604128676718805 135901365365721765860597)
                ·
                  rfl

theorem cell22_3573004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_3573004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573004 prefixEnd_3573004 := by exact prefixLift 3573004
  have htrace : WordTrace (prefixWord ++ tailWord_3573004) baseStart_3573004 baseEnd_3573004 := by
    simpa [prefixWord, tailWord_3573004, baseEnd_3573004] using wordTrace_append hprefix tailTrace_3573004
  have hstable : (prefixWord ++ tailWord_3573004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573004).length < 2 ^ (prefixWord ++ tailWord_3573004).sum := by decide
  have hdescent : baseEnd_3573004 < baseStart_3573004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573019 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 5, 3]
def baseStart_3573019 : Nat := 118140960795 + 3573019 * 2 ^ 59
def prefixEnd_3573019 : Nat := 4983230072969 + 3 ^ 40 * 3573019 * 2
def baseEnd_3573019 : Nat := 1223117423098040853620327

theorem tailTrace_3573019 : CollatzResearch.WordTrace tailWord_3573019 prefixEnd_3573019 1223117423098040853620327 := by
  unfold tailWord_3573019
  simp only [CollatzResearch.WordTrace]
  refine ⟨130318709042569860907970111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86879139361713240605313407 130318709042569860907970111)
  ·
    refine ⟨195478063563854791361955167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130318709042569860907970111 195478063563854791361955167)
    ·
      refine ⟨293217095345782187042932751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195478063563854791361955167 293217095345782187042932751)
      ·
        refine ⟨439825643018673280564399127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293217095345782187042932751 439825643018673280564399127)
        ·
          refine ⟨659738464528009920846598691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439825643018673280564399127 659738464528009920846598691)
          ·
            refine ⟨989607696792014881269898037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659738464528009920846598691 989607696792014881269898037)
            ·
              refine ⟨92775721574251395119052941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 989607696792014881269898037 92775721574251395119052941)
              ·
                refine ⟨34790895590344273169644853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92775721574251395119052941 34790895590344273169644853)
                ·
                  refine ⟨3261646461594775609654205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34790895590344273169644853 3261646461594775609654205)
                  ·
                    refine ⟨1223117423098040853620327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261646461594775609654205 1223117423098040853620327)
                    ·
                      rfl

theorem cell22_3573019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 3].length) (baseStart_3573019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573019 prefixEnd_3573019 := by exact prefixLift 3573019
  have htrace : WordTrace (prefixWord ++ tailWord_3573019) baseStart_3573019 baseEnd_3573019 := by
    simpa [prefixWord, tailWord_3573019, baseEnd_3573019] using wordTrace_append hprefix tailTrace_3573019
  have hstable : (prefixWord ++ tailWord_3573019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573019).length < 2 ^ (prefixWord ++ tailWord_3573019).sum := by decide
  have hdescent : baseEnd_3573019 < baseStart_3573019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573111 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 4]
def baseStart_3573111 : Nat := 118140960795 + 3573111 * 2 ^ 59
def prefixEnd_3573111 : Nat := 4983230072969 + 3 ^ 40 * 3573111 * 2
def baseEnd_3573111 : Nat := 407716305526061093440015

theorem tailTrace_3573111 : CollatzResearch.WordTrace tailWord_3573111 prefixEnd_3573111 407716305526061093440015 := by
  unfold tailWord_3573111
  simp only [CollatzResearch.WordTrace]
  refine ⟨130322064558236560620319187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86881376372157707080212791 130322064558236560620319187)
  ·
    refine ⟨195483096837354840930478781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130322064558236560620319187 195483096837354840930478781)
    ·
      refine ⟨73306161314008065348929543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195483096837354840930478781 73306161314008065348929543)
      ·
        refine ⟨109959241971012098023394315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73306161314008065348929543 109959241971012098023394315)
        ·
          refine ⟨164938862956518147035091473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109959241971012098023394315 164938862956518147035091473)
          ·
            refine ⟨123704147217388610276318605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164938862956518147035091473 123704147217388610276318605)
            ·
              refine ⟨46389055206520728853619477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123704147217388610276318605 46389055206520728853619477)
              ·
                refine ⟨2174486962805659165013413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46389055206520728853619477 2174486962805659165013413)
                ·
                  refine ⟨407716305526061093440015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174486962805659165013413 407716305526061093440015)
                  ·
                    rfl

theorem cell22_3573111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 4].length) (baseStart_3573111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573111 prefixEnd_3573111 := by exact prefixLift 3573111
  have htrace : WordTrace (prefixWord ++ tailWord_3573111) baseStart_3573111 baseEnd_3573111 := by
    simpa [prefixWord, tailWord_3573111, baseEnd_3573111] using wordTrace_append hprefix tailTrace_3573111
  have hstable : (prefixWord ++ tailWord_3573111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573111).length < 2 ^ (prefixWord ++ tailWord_3573111).sum := by decide
  have hdescent : baseEnd_3573111 < baseStart_3573111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573177 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_3573177 : Nat := 118140960795 + 3573177 * 2 ^ 59
def prefixEnd_3573177 : Nat := 4983230072969 + 3 ^ 40 * 3573177 * 2
def baseEnd_3573177 : Nat := 1223171509726981108169843

theorem tailTrace_3573177 : CollatzResearch.WordTrace tailWord_3573177 prefixEnd_3573177 1223171509726981108169843 := by
  unfold tailWord_3573177
  simp only [CollatzResearch.WordTrace]
  refine ⟨130324471775997453892221785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86882981183998302594814523 130324471775997453892221785)
  ·
    refine ⟨97743353831998090419166339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130324471775997453892221785 97743353831998090419166339)
    ·
      refine ⟨146615030747997135628749509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97743353831998090419166339 146615030747997135628749509)
      ·
        refine ⟨27490318265249462930390533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146615030747997135628749509 27490318265249462930390533)
        ·
          refine ⟨5154434674734274299448225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27490318265249462930390533 5154434674734274299448225)
          ·
            refine ⟨3865826006050705724586169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154434674734274299448225 3865826006050705724586169)
            ·
              refine ⟨2899369504538029293439627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865826006050705724586169 2899369504538029293439627)
              ·
                refine ⟨4349054256807043940159441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899369504538029293439627 4349054256807043940159441)
                ·
                  refine ⟨3261790692605282955119581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4349054256807043940159441 3261790692605282955119581)
                  ·
                    refine ⟨1223171509726981108169843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261790692605282955119581 1223171509726981108169843)
                    ·
                      rfl

theorem cell22_3573177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_3573177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573177 prefixEnd_3573177 := by exact prefixLift 3573177
  have htrace : WordTrace (prefixWord ++ tailWord_3573177) baseStart_3573177 baseEnd_3573177 := by
    simpa [prefixWord, tailWord_3573177, baseEnd_3573177] using wordTrace_append hprefix tailTrace_3573177
  have hstable : (prefixWord ++ tailWord_3573177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573177).length < 2 ^ (prefixWord ++ tailWord_3573177).sum := by decide
  have hdescent : baseEnd_3573177 < baseStart_3573177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573205 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3573205 : Nat := 118140960795 + 3573205 * 2 ^ 59
def prefixEnd_3573205 : Nat := 4983230072969 + 3 ^ 40 * 3573205 * 2
def baseEnd_3573205 : Nat := 1223181094699198368469757

theorem tailTrace_3573205 : CollatzResearch.WordTrace tailWord_3573205 prefixEnd_3573205 1223181094699198368469757 := by
  unfold tailWord_3573205
  simp only [CollatzResearch.WordTrace]
  refine ⟨130325493019896014674241069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86883662013264009782827379 130325493019896014674241069)
  ·
    refine ⟨48872059882461005502840401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130325493019896014674241069 48872059882461005502840401)
    ·
      refine ⟨36654044911845754127130301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48872059882461005502840401 36654044911845754127130301)
      ·
        refine ⟨13745266841942157797673863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36654044911845754127130301 13745266841942157797673863)
        ·
          refine ⟨20617900262913236696510795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13745266841942157797673863 20617900262913236696510795)
          ·
            refine ⟨30926850394369855044766193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20617900262913236696510795 30926850394369855044766193)
            ·
              refine ⟨23195137795777391283574645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30926850394369855044766193 23195137795777391283574645)
              ·
                refine ⟨2174544168354130432835123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23195137795777391283574645 2174544168354130432835123)
                ·
                  refine ⟨3261816252531195649252685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174544168354130432835123 3261816252531195649252685)
                  ·
                    refine ⟨1223181094699198368469757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261816252531195649252685 1223181094699198368469757)
                    ·
                      rfl

theorem cell22_3573205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3573205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573205 prefixEnd_3573205 := by exact prefixLift 3573205
  have htrace : WordTrace (prefixWord ++ tailWord_3573205) baseStart_3573205 baseEnd_3573205 := by
    simpa [prefixWord, tailWord_3573205, baseEnd_3573205] using wordTrace_append hprefix tailTrace_3573205
  have hstable : (prefixWord ++ tailWord_3573205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573205).length < 2 ^ (prefixWord ++ tailWord_3573205).sum := by decide
  have hdescent : baseEnd_3573205 < baseStart_3573205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573231 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_3573231 : Nat := 118140960795 + 3573231 * 2 ^ 59
def prefixEnd_3573231 : Nat := 4983230072969 + 3 ^ 40 * 3573231 * 2
def baseEnd_3573231 : Nat := 1223189995030542967319677

theorem tailTrace_3573231 : CollatzResearch.WordTrace tailWord_3573231 prefixEnd_3573231 1223189995030542967319677 := by
  unfold tailWord_3573231
  simp only [CollatzResearch.WordTrace]
  refine ⟨130326441317801821114687547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86884294211867880743125031 130326441317801821114687547)
  ·
    refine ⟨195489661976702731672031321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130326441317801821114687547 195489661976702731672031321)
    ·
      refine ⟨146617246482527048754023491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195489661976702731672031321 146617246482527048754023491)
      ·
        refine ⟨219925869723790573131035237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146617246482527048754023491 219925869723790573131035237)
        ·
          refine ⟨41236100573210732462069107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219925869723790573131035237 41236100573210732462069107)
          ·
            refine ⟨61854150859816098693103661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41236100573210732462069107 61854150859816098693103661)
            ·
              refine ⟨23195306572431037009913873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61854150859816098693103661 23195306572431037009913873)
              ·
                refine ⟨17396479929323277757435405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23195306572431037009913873 17396479929323277757435405)
                ·
                  refine ⟨6523679973496229159038277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17396479929323277757435405 6523679973496229159038277)
                  ·
                    refine ⟨1223189995030542967319677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6523679973496229159038277 1223189995030542967319677)
                    ·
                      rfl

theorem cell22_3573231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_3573231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573231 prefixEnd_3573231 := by exact prefixLift 3573231
  have htrace : WordTrace (prefixWord ++ tailWord_3573231) baseStart_3573231 baseEnd_3573231 := by
    simpa [prefixWord, tailWord_3573231, baseEnd_3573231] using wordTrace_append hprefix tailTrace_3573231
  have hstable : (prefixWord ++ tailWord_3573231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573231).length < 2 ^ (prefixWord ++ tailWord_3573231).sum := by decide
  have hdescent : baseEnd_3573231 < baseStart_3573231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573280 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_3573280 : Nat := 118140960795 + 3573280 * 2 ^ 59
def prefixEnd_3573280 : Nat := 4983230072969 + 3 ^ 40 * 3573280 * 2
def baseEnd_3573280 : Nat := 407735589577307724281509

theorem tailTrace_3573280 : CollatzResearch.WordTrace tailWord_3573280 prefixEnd_3573280 407735589577307724281509 := by
  unfold tailWord_3573280
  simp only [CollatzResearch.WordTrace]
  refine ⟨65164114247312151241610647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86885485663082868322147529 65164114247312151241610647)
  ·
    refine ⟨97746171370968226862415971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65164114247312151241610647 97746171370968226862415971)
    ·
      refine ⟨146619257056452340293623957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97746171370968226862415971 146619257056452340293623957)
      ·
        refine ⟨6872777674521203451263623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146619257056452340293623957 6872777674521203451263623)
        ·
          refine ⟨10309166511781805176895435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6872777674521203451263623 10309166511781805176895435)
          ·
            refine ⟨15463749767672707765343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10309166511781805176895435 15463749767672707765343153)
            ·
              refine ⟨11597812325754530824007365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15463749767672707765343153 11597812325754530824007365)
              ·
                refine ⟨2174589811078974529501381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11597812325754530824007365 2174589811078974529501381)
                ·
                  refine ⟨407735589577307724281509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2174589811078974529501381 407735589577307724281509)
                  ·
                    rfl

theorem cell22_3573280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_3573280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573280 prefixEnd_3573280 := by exact prefixLift 3573280
  have htrace : WordTrace (prefixWord ++ tailWord_3573280) baseStart_3573280 baseEnd_3573280 := by
    simpa [prefixWord, tailWord_3573280, baseEnd_3573280] using wordTrace_append hprefix tailTrace_3573280
  have hstable : (prefixWord ++ tailWord_3573280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573280).length < 2 ^ (prefixWord ++ tailWord_3573280).sum := by decide
  have hdescent : baseEnd_3573280 < baseStart_3573280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573306 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3573306 : Nat := 118140960795 + 3573306 * 2 ^ 59
def prefixEnd_3573306 : Nat := 4983230072969 + 3 ^ 40 * 3573306 * 2
def baseEnd_3573306 : Nat := 1223215669063267771694447

theorem tailTrace_3573306 : CollatzResearch.WordTrace tailWord_3573306 prefixEnd_3573306 1223215669063267771694447 := by
  unfold tailWord_3573306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32582294198132527230916943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86886117861686739282445181 32582294198132527230916943)
  ·
    refine ⟨48873441297198790846375415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32582294198132527230916943 48873441297198790846375415)
    ·
      refine ⟨73310161945798186269563123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48873441297198790846375415 73310161945798186269563123)
      ·
        refine ⟨109965242918697279404344685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73310161945798186269563123 109965242918697279404344685)
        ·
          refine ⟨41236966094511479776629257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109965242918697279404344685 41236966094511479776629257)
          ·
            refine ⟨30927724570883609832471943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41236966094511479776629257 30927724570883609832471943)
            ·
              refine ⟨46391586856325414748707915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30927724570883609832471943 46391586856325414748707915)
              ·
                refine ⟨69587380284488122123061873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46391586856325414748707915 69587380284488122123061873)
                ·
                  refine ⟨52190535213366091592296405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69587380284488122123061873 52190535213366091592296405)
                  ·
                    refine ⟨1223215669063267771694447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52190535213366091592296405 1223215669063267771694447)
                    ·
                      rfl

theorem cell22_3573306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3573306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573306 prefixEnd_3573306 := by exact prefixLift 3573306
  have htrace : WordTrace (prefixWord ++ tailWord_3573306) baseStart_3573306 baseEnd_3573306 := by
    simpa [prefixWord, tailWord_3573306, baseEnd_3573306] using wordTrace_append hprefix tailTrace_3573306
  have hstable : (prefixWord ++ tailWord_3573306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573306).length < 2 ^ (prefixWord ++ tailWord_3573306).sum := by decide
  have hdescent : baseEnd_3573306 < baseStart_3573306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573308 : List Nat := [2, 2, 2, 2, 4, 1, 1, 8]
def baseStart_3573308 : Nat := 118140960795 + 3573308 * 2 ^ 59
def prefixEnd_3573308 : Nat := 4983230072969 + 3 ^ 40 * 3573308 * 2
def baseEnd_3573308 : Nat := 135912928189348937016049

theorem tailTrace_3573308 : CollatzResearch.WordTrace tailWord_3573308 prefixEnd_3573308 135912928189348937016049 := by
  unfold tailWord_3573308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65164624869261431632620289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86886166492348575510160385 65164624869261431632620289)
  ·
    refine ⟨48873468651946073724465217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65164624869261431632620289 48873468651946073724465217)
    ·
      refine ⟨36655101488959555293348913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48873468651946073724465217 36655101488959555293348913)
      ·
        refine ⟨27491326116719666470011685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36655101488959555293348913 27491326116719666470011685)
        ·
          refine ⟨5154623646884937463127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27491326116719666470011685 5154623646884937463127191)
          ·
            refine ⟨7731935470327406194690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154623646884937463127191 7731935470327406194690787)
            ·
              refine ⟨11597903205491109292036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731935470327406194690787 11597903205491109292036181)
              ·
                refine ⟨135912928189348937016049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11597903205491109292036181 135912928189348937016049)
                ·
                  rfl

theorem cell22_3573308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_3573308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573308 prefixEnd_3573308 := by exact prefixLift 3573308
  have htrace : WordTrace (prefixWord ++ tailWord_3573308) baseStart_3573308 baseEnd_3573308 := by
    simpa [prefixWord, tailWord_3573308, baseEnd_3573308] using wordTrace_append hprefix tailTrace_3573308
  have hstable : (prefixWord ++ tailWord_3573308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573308).length < 2 ^ (prefixWord ++ tailWord_3573308).sum := by decide
  have hdescent : baseEnd_3573308 < baseStart_3573308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573325 : List Nat := [1, 6, 1, 1, 3, 2, 8]
def baseStart_3573325 : Nat := 118140960795 + 3573325 * 2 ^ 59
def prefixEnd_3573325 : Nat := 4983230072969 + 3 ^ 40 * 3573325 * 2
def baseEnd_3573325 : Nat := 45304524931539187239607

theorem tailTrace_3573325 : CollatzResearch.WordTrace tailWord_3573325 prefixEnd_3573325 45304524931539187239607 := by
  unfold tailWord_3573325
  simp only [CollatzResearch.WordTrace]
  refine ⟨130329869779461275168609429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86886579852974183445739619 130329869779461275168609429)
  ·
    refine ⟨6109212645912247273528567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130329869779461275168609429 6109212645912247273528567)
    ·
      refine ⟨9163818968868370910292851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109212645912247273528567 9163818968868370910292851)
      ·
        refine ⟨13745728453302556365439277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9163818968868370910292851 13745728453302556365439277)
        ·
          refine ⟨5154648169988458637039729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13745728453302556365439277 5154648169988458637039729)
          ·
            refine ⟨3865986127491343977779797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5154648169988458637039729 3865986127491343977779797)
            ·
              refine ⟨45304524931539187239607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3865986127491343977779797 45304524931539187239607)
              ·
                rfl

theorem cell22_3573325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 8].length) (baseStart_3573325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573325 prefixEnd_3573325 := by exact prefixLift 3573325
  have htrace : WordTrace (prefixWord ++ tailWord_3573325) baseStart_3573325 baseEnd_3573325 := by
    simpa [prefixWord, tailWord_3573325, baseEnd_3573325] using wordTrace_append hprefix tailTrace_3573325
  have hstable : (prefixWord ++ tailWord_3573325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573325).length < 2 ^ (prefixWord ++ tailWord_3573325).sum := by decide
  have hdescent : baseEnd_3573325 < baseStart_3573325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573413 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3573413 : Nat := 118140960795 + 3573413 * 2 ^ 59
def prefixEnd_3573413 : Nat := 4983230072969 + 3 ^ 40 * 3573413 * 2
def baseEnd_3573413 : Nat := 1223252297349955159269119

theorem tailTrace_3573413 : CollatzResearch.WordTrace tailWord_3573413 prefixEnd_3573413 1223252297349955159269119 := by
  unfold tailWord_3573413
  simp only [CollatzResearch.WordTrace]
  refine ⟨130333079403142466197812893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86888719602094977465208595 130333079403142466197812893)
  ·
    refine ⟨48874904776178424824179835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130333079403142466197812893 48874904776178424824179835)
    ·
      refine ⟨73312357164267637236269753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48874904776178424824179835 73312357164267637236269753)
      ·
        refine ⟨54984267873200727927202315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73312357164267637236269753 54984267873200727927202315)
        ·
          refine ⟨82476401809801091890803473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54984267873200727927202315 82476401809801091890803473)
          ·
            refine ⟨61857301357350818918102605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82476401809801091890803473 61857301357350818918102605)
            ·
              refine ⟨23196488009006557094288477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61857301357350818918102605 23196488009006557094288477)
              ·
                refine ⟨8698683003377458910358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23196488009006557094288477 8698683003377458910358179)
                ·
                  refine ⟨13048024505066188365537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698683003377458910358179 13048024505066188365537269)
                  ·
                    refine ⟨1223252297349955159269119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13048024505066188365537269 1223252297349955159269119)
                    ·
                      rfl

theorem cell22_3573413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3573413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573413 prefixEnd_3573413 := by exact prefixLift 3573413
  have htrace : WordTrace (prefixWord ++ tailWord_3573413) baseStart_3573413 baseEnd_3573413 := by
    simpa [prefixWord, tailWord_3573413, baseEnd_3573413] using wordTrace_append hprefix tailTrace_3573413
  have hstable : (prefixWord ++ tailWord_3573413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573413).length < 2 ^ (prefixWord ++ tailWord_3573413).sum := by decide
  have hdescent : baseEnd_3573413 < baseStart_3573413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573503 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3573503 : Nat := 118140960795 + 3573503 * 2 ^ 59
def prefixEnd_3573503 : Nat := 4983230072969 + 3 ^ 40 * 3573503 * 2
def baseEnd_3573503 : Nat := 1223283106189224924518843

theorem tailTrace_3573503 : CollatzResearch.WordTrace tailWord_3573503 prefixEnd_3573503 1223283106189224924518843 := by
  unfold tailWord_3573503
  simp only [CollatzResearch.WordTrace]
  refine ⟨130336361972816411568589163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86890907981877607712392775 130336361972816411568589163)
  ·
    refine ⟨195504542959224617352883745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130336361972816411568589163 195504542959224617352883745)
    ·
      refine ⟨146628407219418463014662809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195504542959224617352883745 146628407219418463014662809)
      ·
        refine ⟨109971305414563847260997107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146628407219418463014662809 109971305414563847260997107)
        ·
          refine ⟨164956958121845770891495661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109971305414563847260997107 164956958121845770891495661)
          ·
            refine ⟨61858859295692164084310873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164956958121845770891495661 61858859295692164084310873)
            ·
              refine ⟨46394144471769123063233155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61858859295692164084310873 46394144471769123063233155)
              ·
                refine ⟨69591216707653684594849733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46394144471769123063233155 69591216707653684594849733)
                ·
                  refine ⟨13048353132685065861534325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69591216707653684594849733 13048353132685065861534325)
                  ·
                    refine ⟨1223283106189224924518843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13048353132685065861534325 1223283106189224924518843)
                    ·
                      rfl

theorem cell22_3573503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3573503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573503 prefixEnd_3573503 := by exact prefixLift 3573503
  have htrace : WordTrace (prefixWord ++ tailWord_3573503) baseStart_3573503 baseEnd_3573503 := by
    simpa [prefixWord, tailWord_3573503, baseEnd_3573503] using wordTrace_append hprefix tailTrace_3573503
  have hstable : (prefixWord ++ tailWord_3573503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573503).length < 2 ^ (prefixWord ++ tailWord_3573503).sum := by decide
  have hdescent : baseEnd_3573503 < baseStart_3573503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573535 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3573535 : Nat := 118140960795 + 3573535 * 2 ^ 59
def prefixEnd_3573535 : Nat := 4983230072969 + 3 ^ 40 * 3573535 * 2
def baseEnd_3573535 : Nat := 1223294060443187507718745

theorem tailTrace_3573535 : CollatzResearch.WordTrace tailWord_3573535 prefixEnd_3573535 1223294060443187507718745 := by
  unfold tailWord_3573535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130337529108700481033754059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86891686072466987355836039 130337529108700481033754059)
  ·
    refine ⟨195506293663050721550631089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130337529108700481033754059 195506293663050721550631089)
    ·
      refine ⟨146629720247288041162973317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195506293663050721550631089 146629720247288041162973317)
      ·
        refine ⟨27493072546366507718057497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146629720247288041162973317 27493072546366507718057497)
        ·
          refine ⟨20619804409774880788543123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27493072546366507718057497 20619804409774880788543123)
          ·
            refine ⟨30929706614662321182814685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20619804409774880788543123 30929706614662321182814685)
            ·
              refine ⟨11598639980498370443555507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30929706614662321182814685 11598639980498370443555507)
              ·
                refine ⟨17397959970747555665333261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11598639980498370443555507 17397959970747555665333261)
                ·
                  refine ⟨6524234989030333374499973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17397959970747555665333261 6524234989030333374499973)
                  ·
                    refine ⟨1223294060443187507718745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524234989030333374499973 1223294060443187507718745)
                    ·
                      rfl

theorem cell22_3573535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3573535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573535 prefixEnd_3573535 := by exact prefixLift 3573535
  have htrace : WordTrace (prefixWord ++ tailWord_3573535) baseStart_3573535 baseEnd_3573535 := by
    simpa [prefixWord, tailWord_3573535, baseEnd_3573535] using wordTrace_append hprefix tailTrace_3573535
  have hstable : (prefixWord ++ tailWord_3573535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573535).length < 2 ^ (prefixWord ++ tailWord_3573535).sum := by decide
  have hdescent : baseEnd_3573535 < baseStart_3573535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573633 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3573633 : Nat := 118140960795 + 3573633 * 2 ^ 59
def prefixEnd_3573633 : Nat := 4983230072969 + 3 ^ 40 * 3573633 * 2
def baseEnd_3573633 : Nat := 1223327607845947918768445

theorem tailTrace_3573633 : CollatzResearch.WordTrace tailWord_3573633 prefixEnd_3573633 1223327607845947918768445 := by
  unfold tailWord_3573633
  simp only [CollatzResearch.WordTrace]
  refine ⟨130341103462345443770821553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86894068974896962513881035 130341103462345443770821553)
  ·
    refine ⟨97755827596759082828116165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130341103462345443770821553 97755827596759082828116165)
    ·
      refine ⟨18329217674392328030271781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97755827596759082828116165 18329217674392328030271781)
      ·
        refine ⟨3436728313948561505675959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18329217674392328030271781 3436728313948561505675959)
        ·
          refine ⟨5155092470922842258513939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436728313948561505675959 5155092470922842258513939)
          ·
            refine ⟨7732638706384263387770909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155092470922842258513939 7732638706384263387770909)
            ·
              refine ⟨2899739514894098770414091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732638706384263387770909 2899739514894098770414091)
              ·
                refine ⟨4349609272341148155621137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899739514894098770414091 4349609272341148155621137)
                ·
                  refine ⟨3262206954255861116715853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4349609272341148155621137 3262206954255861116715853)
                  ·
                    refine ⟨1223327607845947918768445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262206954255861116715853 1223327607845947918768445)
                    ·
                      rfl

theorem cell22_3573633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3573633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573633 prefixEnd_3573633 := by exact prefixLift 3573633
  have htrace : WordTrace (prefixWord ++ tailWord_3573633) baseStart_3573633 baseEnd_3573633 := by
    simpa [prefixWord, tailWord_3573633, baseEnd_3573633] using wordTrace_append hprefix tailTrace_3573633
  have hstable : (prefixWord ++ tailWord_3573633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573633).length < 2 ^ (prefixWord ++ tailWord_3573633).sum := by decide
  have hdescent : baseEnd_3573633 < baseStart_3573633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573646 : List Nat := [4, 1, 1, 5, 1, 2, 2, 6]
def baseStart_3573646 : Nat := 118140960795 + 3573646 * 2 ^ 59
def prefixEnd_3573646 : Nat := 4983230072969 + 3 ^ 40 * 3573646 * 2
def baseEnd_3573646 : Nat := 135925784223513357577045

theorem tailTrace_3573646 : CollatzResearch.WordTrace tailWord_3573646 prefixEnd_3573646 135925784223513357577045 := by
  unfold tailWord_3573646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292697201412293373880599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86894385074198897994029861 16292697201412293373880599)
  ·
    refine ⟨24439045802118440060820899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16292697201412293373880599 24439045802118440060820899)
    ·
      refine ⟨36658568703177660091231349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24439045802118440060820899 36658568703177660091231349)
      ·
        refine ⟨3436740815922905633552939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36658568703177660091231349 3436740815922905633552939)
        ·
          refine ⟨5155111223884358450329409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436740815922905633552939 5155111223884358450329409)
          ·
            refine ⟨3866333417913268837747057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155111223884358450329409 3866333417913268837747057)
            ·
              refine ⟨2899750063434951628310293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866333417913268837747057 2899750063434951628310293)
              ·
                refine ⟨135925784223513357577045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2899750063434951628310293 135925784223513357577045)
                ·
                  rfl

theorem cell22_3573646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_3573646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573646 prefixEnd_3573646 := by exact prefixLift 3573646
  have htrace : WordTrace (prefixWord ++ tailWord_3573646) baseStart_3573646 baseEnd_3573646 := by
    simpa [prefixWord, tailWord_3573646, baseEnd_3573646] using wordTrace_append hprefix tailTrace_3573646
  have hstable : (prefixWord ++ tailWord_3573646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573646).length < 2 ^ (prefixWord ++ tailWord_3573646).sum := by decide
  have hdescent : baseEnd_3573646 < baseStart_3573646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573661 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_3573661 : Nat := 118140960795 + 3573661 * 2 ^ 59
def prefixEnd_3573661 : Nat := 4983230072969 + 3 ^ 40 * 3573661 * 2
def baseEnd_3573661 : Nat := 1223337192818165179068359

theorem tailTrace_3573661 : CollatzResearch.WordTrace tailWord_3573661 prefixEnd_3573661 1223337192818165179068359 := by
  unfold tailWord_3573661
  simp only [CollatzResearch.WordTrace]
  refine ⟨130342124706244004552840837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86894749804162669701893891 130342124706244004552840837)
  ·
    refine ⟨24439148382420750853657657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130342124706244004552840837 24439148382420750853657657)
    ·
      refine ⟨18329361286815563140243243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24439148382420750853657657 18329361286815563140243243)
      ·
        refine ⟨27494041930223344710364865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329361286815563140243243 27494041930223344710364865)
        ·
          refine ⟨20620531447667508532773649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27494041930223344710364865 20620531447667508532773649)
          ·
            refine ⟨15465398585750631399580237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20620531447667508532773649 15465398585750631399580237)
            ·
              refine ⟨5799524469656486774842589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15465398585750631399580237 5799524469656486774842589)
              ·
                refine ⟨2174821676121182540565971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5799524469656486774842589 2174821676121182540565971)
                ·
                  refine ⟨3262232514181773810848957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174821676121182540565971 3262232514181773810848957)
                  ·
                    refine ⟨1223337192818165179068359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262232514181773810848957 1223337192818165179068359)
                    ·
                      rfl

theorem cell22_3573661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_3573661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573661 prefixEnd_3573661 := by exact prefixLift 3573661
  have htrace : WordTrace (prefixWord ++ tailWord_3573661) baseStart_3573661 baseEnd_3573661 := by
    simpa [prefixWord, tailWord_3573661, baseEnd_3573661] using wordTrace_append hprefix tailTrace_3573661
  have hstable : (prefixWord ++ tailWord_3573661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573661).length < 2 ^ (prefixWord ++ tailWord_3573661).sum := by decide
  have hdescent : baseEnd_3573661 < baseStart_3573661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573704 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3573704 : Nat := 118140960795 + 3573704 * 2 ^ 59
def prefixEnd_3573704 : Nat := 4983230072969 + 3 ^ 40 * 3573704 * 2
def baseEnd_3573704 : Nat := 1223351912596927400243227

theorem tailTrace_3573704 : CollatzResearch.WordTrace tailWord_3573704 prefixEnd_3573704 1223351912596927400243227 := by
  unfold tailWord_3573704
  simp only [CollatzResearch.WordTrace]
  refine ⟨65171846522544111448328083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86895795363392148597770777 65171846522544111448328083)
  ·
    refine ⟨97757769783816167172492125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65171846522544111448328083 97757769783816167172492125)
    ·
      refine ⟨36659163668931062689684547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97757769783816167172492125 36659163668931062689684547)
      ·
        refine ⟨54988745503396594034526821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36659163668931062689684547 54988745503396594034526821)
        ·
          refine ⟨10310389781886861381473779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54988745503396594034526821 10310389781886861381473779)
          ·
            refine ⟨15465584672830292072210669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310389781886861381473779 15465584672830292072210669)
            ·
              refine ⟨5799594252311359527079001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15465584672830292072210669 5799594252311359527079001)
              ·
                refine ⟨4349695689233519645309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5799594252311359527079001 4349695689233519645309251)
                ·
                  refine ⟨6524543533850279467963877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349695689233519645309251 6524543533850279467963877)
                  ·
                    refine ⟨1223351912596927400243227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524543533850279467963877 1223351912596927400243227)
                    ·
                      rfl

theorem cell22_3573704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3573704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573704 prefixEnd_3573704 := by exact prefixLift 3573704
  have htrace : WordTrace (prefixWord ++ tailWord_3573704) baseStart_3573704 baseEnd_3573704 := by
    simpa [prefixWord, tailWord_3573704, baseEnd_3573704] using wordTrace_append hprefix tailTrace_3573704
  have hstable : (prefixWord ++ tailWord_3573704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573704).length < 2 ^ (prefixWord ++ tailWord_3573704).sum := by decide
  have hdescent : baseEnd_3573704 < baseStart_3573704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573717 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3573717 : Nat := 118140960795 + 3573717 * 2 ^ 59
def prefixEnd_3573717 : Nat := 4983230072969 + 3 ^ 40 * 3573717 * 2
def baseEnd_3573717 : Nat := 1223356362762599699668187

theorem tailTrace_3573717 : CollatzResearch.WordTrace tailWord_3573717 prefixEnd_3573717 1223356362762599699668187 := by
  unfold tailWord_3573717
  simp only [CollatzResearch.WordTrace]
  refine ⟨130344167194041126116879405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86896111462694084077919603 130344167194041126116879405)
  ·
    refine ⟨48879062697765422293829777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130344167194041126116879405 48879062697765422293829777)
    ·
      refine ⟨36659297023324066720372333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48879062697765422293829777 36659297023324066720372333)
      ·
        refine ⟨13747236383746525020139625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36659297023324066720372333 13747236383746525020139625)
        ·
          refine ⟨10310427287809893765104719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13747236383746525020139625 10310427287809893765104719)
          ·
            refine ⟨15465640931714840647657079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310427287809893765104719 15465640931714840647657079)
            ·
              refine ⟨23198461397572260971485619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15465640931714840647657079 23198461397572260971485619)
              ·
                refine ⟨34797692096358391457228429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23198461397572260971485619 34797692096358391457228429)
                ·
                  refine ⟨13049134536134396796460661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34797692096358391457228429 13049134536134396796460661)
                  ·
                    refine ⟨1223356362762599699668187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13049134536134396796460661 1223356362762599699668187)
                    ·
                      rfl

theorem cell22_3573717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3573717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573717 prefixEnd_3573717 := by exact prefixLift 3573717
  have htrace : WordTrace (prefixWord ++ tailWord_3573717) baseStart_3573717 baseEnd_3573717 := by
    simpa [prefixWord, tailWord_3573717, baseEnd_3573717] using wordTrace_append hprefix tailTrace_3573717
  have hstable : (prefixWord ++ tailWord_3573717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573717).length < 2 ^ (prefixWord ++ tailWord_3573717).sum := by decide
  have hdescent : baseEnd_3573717 < baseStart_3573717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573721 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_3573721 : Nat := 118140960795 + 3573721 * 2 ^ 59
def prefixEnd_3573721 : Nat := 4983230072969 + 3 ^ 40 * 3573721 * 2
def baseEnd_3573721 : Nat := 1223357732044345022568175

theorem tailTrace_3573721 : CollatzResearch.WordTrace tailWord_3573721 prefixEnd_3573721 1223357732044345022568175 := by
  unfold tailWord_3573721
  simp only [CollatzResearch.WordTrace]
  refine ⟨130344313086026634800025017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86896208724017756533350011 130344313086026634800025017)
  ·
    refine ⟨97758234814519976100018763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130344313086026634800025017 97758234814519976100018763)
    ·
      refine ⟨146637352221779964150028145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97758234814519976100018763 146637352221779964150028145)
      ·
        refine ⟨109978014166334973112521109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146637352221779964150028145 109978014166334973112521109)
        ·
          refine ⟨5155219414046951864649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109978014166334973112521109 5155219414046951864649427)
          ·
            refine ⟨7732829121070427796974141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155219414046951864649427 7732829121070427796974141)
            ·
              refine ⟨2899810920401410423865303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732829121070427796974141 2899810920401410423865303)
              ·
                refine ⟨4349716380602115635797955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899810920401410423865303 4349716380602115635797955)
                ·
                  refine ⟨6524574570903173453696933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349716380602115635797955 6524574570903173453696933)
                  ·
                    refine ⟨1223357732044345022568175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524574570903173453696933 1223357732044345022568175)
                    ·
                      rfl

theorem cell22_3573721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_3573721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573721 prefixEnd_3573721 := by exact prefixLift 3573721
  have htrace : WordTrace (prefixWord ++ tailWord_3573721) baseStart_3573721 baseEnd_3573721 := by
    simpa [prefixWord, tailWord_3573721, baseEnd_3573721] using wordTrace_append hprefix tailTrace_3573721
  have hstable : (prefixWord ++ tailWord_3573721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573721).length < 2 ^ (prefixWord ++ tailWord_3573721).sum := by decide
  have hdescent : baseEnd_3573721 < baseStart_3573721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573732 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_3573732 : Nat := 118140960795 + 3573732 * 2 ^ 59
def prefixEnd_3573732 : Nat := 4983230072969 + 3 ^ 40 * 3573732 * 2
def baseEnd_3573732 : Nat := 1223361497569144660543141

theorem tailTrace_3573732 : CollatzResearch.WordTrace tailWord_3573732 prefixEnd_3573732 1223361497569144660543141 := by
  unfold tailWord_3573732
  simp only [CollatzResearch.WordTrace]
  refine ⟨65172357144493391839337725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86896476192657855785783633 65172357144493391839337725)
  ·
    refine ⟨24439633929185021939751647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65172357144493391839337725 24439633929185021939751647)
    ·
      refine ⟨36659450893777532909627471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24439633929185021939751647 36659450893777532909627471)
      ·
        refine ⟨54989176340666299364441207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36659450893777532909627471 54989176340666299364441207)
        ·
          refine ⟨82483764510999449046661811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54989176340666299364441207 82483764510999449046661811)
          ·
            refine ⟨123725646766499173569992717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82483764510999449046661811 123725646766499173569992717)
            ·
              refine ⟨46397117537437190088747269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123725646766499173569992717 46397117537437190088747269)
              ·
                refine ⟨8699459538269473141640113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46397117537437190088747269 8699459538269473141640113)
                ·
                  refine ⟨6524594653702104856230085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8699459538269473141640113 6524594653702104856230085)
                  ·
                    refine ⟨1223361497569144660543141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524594653702104856230085 1223361497569144660543141)
                    ·
                      rfl

theorem cell22_3573732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_3573732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573732 prefixEnd_3573732 := by exact prefixLift 3573732
  have htrace : WordTrace (prefixWord ++ tailWord_3573732) baseStart_3573732 baseEnd_3573732 := by
    simpa [prefixWord, tailWord_3573732, baseEnd_3573732] using wordTrace_append hprefix tailTrace_3573732
  have hstable : (prefixWord ++ tailWord_3573732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573732).length < 2 ^ (prefixWord ++ tailWord_3573732).sum := by decide
  have hdescent : baseEnd_3573732 < baseStart_3573732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573869 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3573869 : Nat := 118140960795 + 3573869 * 2 ^ 59
def prefixEnd_3573869 : Nat := 4983230072969 + 3 ^ 40 * 3573869 * 2
def baseEnd_3573869 : Nat := 1223408395468921969867721

theorem tailTrace_3573869 : CollatzResearch.WordTrace tailWord_3573869 prefixEnd_3573869 1223408395468921969867721 := by
  unfold tailWord_3573869
  simp only [CollatzResearch.WordTrace]
  refine ⟨130349711089490456076412661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86899807392993637384275107 130349711089490456076412661)
  ·
    refine ⟨12220285414639730257163687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130349711089490456076412661 12220285414639730257163687)
    ·
      refine ⟨18330428121959595385745531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12220285414639730257163687 18330428121959595385745531)
      ·
        refine ⟨27495642182939393078618297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18330428121959595385745531 27495642182939393078618297)
        ·
          refine ⟨20621731637204544808963723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27495642182939393078618297 20621731637204544808963723)
          ·
            refine ⟨30932597455806817213445585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20621731637204544808963723 30932597455806817213445585)
            ·
              refine ⟨23199448091855112910084189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30932597455806817213445585 23199448091855112910084189)
              ·
                refine ⟨8699793034445667341281571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23199448091855112910084189 8699793034445667341281571)
                ·
                  refine ⟨13049689551668501011922357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8699793034445667341281571 13049689551668501011922357)
                  ·
                    refine ⟨1223408395468921969867721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13049689551668501011922357 1223408395468921969867721)
                    ·
                      rfl

theorem cell22_3573869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3573869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573869 prefixEnd_3573869 := by exact prefixLift 3573869
  have htrace : WordTrace (prefixWord ++ tailWord_3573869) baseStart_3573869 baseEnd_3573869 := by
    simpa [prefixWord, tailWord_3573869, baseEnd_3573869] using wordTrace_append hprefix tailTrace_3573869
  have hstable : (prefixWord ++ tailWord_3573869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573869).length < 2 ^ (prefixWord ++ tailWord_3573869).sum := by decide
  have hdescent : baseEnd_3573869 < baseStart_3573869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3573884 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3573884 : Nat := 118140960795 + 3573884 * 2 ^ 59
def prefixEnd_3573884 : Nat := 4983230072969 + 3 ^ 40 * 3573884 * 2
def baseEnd_3573884 : Nat := 1223413530275466930742675

theorem tailTrace_3573884 : CollatzResearch.WordTrace tailWord_3573884 prefixEnd_3573884 1223413530275466930742675 := by
  unfold tailWord_3573884
  simp only [CollatzResearch.WordTrace]
  refine ⟨65175129092218056819104353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86900172122957409092139137 65175129092218056819104353)
  ·
    refine ⟨48881346819163542614328265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65175129092218056819104353 48881346819163542614328265)
    ·
      refine ⟨36661010114372656960746199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48881346819163542614328265 36661010114372656960746199)
      ·
        refine ⟨54991515171558985441119299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36661010114372656960746199 54991515171558985441119299)
        ·
          refine ⟨82487272757338478161678949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54991515171558985441119299 82487272757338478161678949)
          ·
            refine ⟨15466363642000964655314803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82487272757338478161678949 15466363642000964655314803)
            ·
              refine ⟨23199545463001446982972205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15466363642000964655314803 23199545463001446982972205)
              ·
                refine ⟨8699829548625542618614577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23199545463001446982972205 8699829548625542618614577)
                ·
                  refine ⟨6524872161469156963960933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8699829548625542618614577 6524872161469156963960933)
                  ·
                    refine ⟨1223413530275466930742675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6524872161469156963960933 1223413530275466930742675)
                    ·
                      rfl

theorem cell22_3573884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3573884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3573884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3573884 prefixEnd_3573884 := by exact prefixLift 3573884
  have htrace : WordTrace (prefixWord ++ tailWord_3573884) baseStart_3573884 baseEnd_3573884 := by
    simpa [prefixWord, tailWord_3573884, baseEnd_3573884] using wordTrace_append hprefix tailTrace_3573884
  have hstable : (prefixWord ++ tailWord_3573884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3573884).length < 2 ^ (prefixWord ++ tailWord_3573884).sum := by decide
  have hdescent : baseEnd_3573884 < baseStart_3573884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3573884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574049 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3574049 : Nat := 118140960795 + 3574049 * 2 ^ 59
def prefixEnd_3574049 : Nat := 4983230072969 + 3 ^ 40 * 3574049 * 2
def baseEnd_3574049 : Nat := 1223470013147461500367169

theorem tailTrace_3574049 : CollatzResearch.WordTrace tailWord_3574049 prefixEnd_3574049 1223470013147461500367169 := by
  unfold tailWord_3574049
  simp only [CollatzResearch.WordTrace]
  refine ⟨130356276228838346817965201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86904184152558897878643467 130356276228838346817965201)
  ·
    refine ⟨97767207171628760113473901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130356276228838346817965201 97767207171628760113473901)
    ·
      refine ⟨36662702689360785042552713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97767207171628760113473901 36662702689360785042552713)
      ·
        refine ⟨27497027017020588781914535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36662702689360785042552713 27497027017020588781914535)
        ·
          refine ⟨41245540525530883172871803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27497027017020588781914535 41245540525530883172871803)
          ·
            refine ⟨61868310788296324759307705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41245540525530883172871803 61868310788296324759307705)
            ·
              refine ⟨46401233091222243569480779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61868310788296324759307705 46401233091222243569480779)
              ·
                refine ⟨69601849636833365354221169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46401233091222243569480779 69601849636833365354221169)
                ·
                  refine ⟨52201387227625024015665877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69601849636833365354221169 52201387227625024015665877)
                  ·
                    refine ⟨1223470013147461500367169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52201387227625024015665877 1223470013147461500367169)
                    ·
                      rfl

theorem cell22_3574049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3574049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574049 prefixEnd_3574049 := by exact prefixLift 3574049
  have htrace : WordTrace (prefixWord ++ tailWord_3574049) baseStart_3574049 baseEnd_3574049 := by
    simpa [prefixWord, tailWord_3574049, baseEnd_3574049] using wordTrace_append hprefix tailTrace_3574049
  have hstable : (prefixWord ++ tailWord_3574049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574049).length < 2 ^ (prefixWord ++ tailWord_3574049).sum := by decide
  have hdescent : baseEnd_3574049 < baseStart_3574049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574053 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3574053 : Nat := 118140960795 + 3574053 * 2 ^ 59
def prefixEnd_3574053 : Nat := 4983230072969 + 3 ^ 40 * 3574053 * 2
def baseEnd_3574053 : Nat := 1223471382429206823267157

theorem tailTrace_3574053 : CollatzResearch.WordTrace tailWord_3574053 prefixEnd_3574053 1223471382429206823267157 := by
  unfold tailWord_3574053
  simp only [CollatzResearch.WordTrace]
  refine ⟨130356422120823855501110813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86904281413882570334073875 130356422120823855501110813)
  ·
    refine ⟨48883658295308945812916555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130356422120823855501110813 48883658295308945812916555)
    ·
      refine ⟨73325487442963418719374833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48883658295308945812916555 73325487442963418719374833)
      ·
        refine ⟨54994115582222564039531125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73325487442963418719374833 54994115582222564039531125)
        ·
          refine ⟨5155698335833365378706043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54994115582222564039531125 5155698335833365378706043)
          ·
            refine ⟨7733547503750048068059065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155698335833365378706043 7733547503750048068059065)
            ·
              refine ⟨5800160627812536051044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7733547503750048068059065 5800160627812536051044299)
              ·
                refine ⟨8700240941718804076566449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5800160627812536051044299 8700240941718804076566449)
                ·
                  refine ⟨6525180706289103057424837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8700240941718804076566449 6525180706289103057424837)
                  ·
                    refine ⟨1223471382429206823267157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525180706289103057424837 1223471382429206823267157)
                    ·
                      rfl

theorem cell22_3574053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3574053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574053 prefixEnd_3574053 := by exact prefixLift 3574053
  have htrace : WordTrace (prefixWord ++ tailWord_3574053) baseStart_3574053 baseEnd_3574053 := by
    simpa [prefixWord, tailWord_3574053, baseEnd_3574053] using wordTrace_append hprefix tailTrace_3574053
  have hstable : (prefixWord ++ tailWord_3574053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574053).length < 2 ^ (prefixWord ++ tailWord_3574053).sum := by decide
  have hdescent : baseEnd_3574053 < baseStart_3574053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574096 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_3574096 : Nat := 118140960795 + 3574096 * 2 ^ 59
def prefixEnd_3574096 : Nat := 4983230072969 + 3 ^ 40 * 3574096 * 2
def baseEnd_3574096 : Nat := 407828700735989681480675

theorem tailTrace_3574096 : CollatzResearch.WordTrace tailWord_3574096 prefixEnd_3574096 407828700735989681480675 := by
  unfold tailWord_3574096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65178995229834036922463071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86905326973112049229950761 65178995229834036922463071)
  ·
    refine ⟨97768492844751055383694607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65178995229834036922463071 97768492844751055383694607)
    ·
      refine ⟨146652739267126583075541911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97768492844751055383694607 146652739267126583075541911)
      ·
        refine ⟨219979108900689874613312867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146652739267126583075541911 219979108900689874613312867)
        ·
          refine ⟨329968663351034811919969301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219979108900689874613312867 329968663351034811919969301)
          ·
            refine ⟨15467281094579756808748561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 329968663351034811919969301 15467281094579756808748561)
            ·
              refine ⟨11600460820934817606561421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467281094579756808748561 11600460820934817606561421)
              ·
                refine ⟨4350172807850556602460533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11600460820934817606561421 4350172807850556602460533)
                ·
                  refine ⟨407828700735989681480675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4350172807850556602460533 407828700735989681480675)
                  ·
                    rfl

theorem cell22_3574096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_3574096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574096 prefixEnd_3574096 := by exact prefixLift 3574096
  have htrace : WordTrace (prefixWord ++ tailWord_3574096) baseStart_3574096 baseEnd_3574096 := by
    simpa [prefixWord, tailWord_3574096, baseEnd_3574096] using wordTrace_append hprefix tailTrace_3574096
  have hstable : (prefixWord ++ tailWord_3574096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574096).length < 2 ^ (prefixWord ++ tailWord_3574096).sum := by decide
  have hdescent : baseEnd_3574096 < baseStart_3574096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574141 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3574141 : Nat := 118140960795 + 3574141 * 2 ^ 59
def prefixEnd_3574141 : Nat := 4983230072969 + 3 ^ 40 * 3574141 * 2
def baseEnd_3574141 : Nat := 407833835542534642355629

theorem tailTrace_3574141 : CollatzResearch.WordTrace tailWord_3574141 prefixEnd_3574141 407833835542534642355629 := by
  unfold tailWord_3574141
  simp only [CollatzResearch.WordTrace]
  refine ⟨130359631744505046530314277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86906421163003364353542851 130359631744505046530314277)
  ·
    refine ⟨24442430952094696224433927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130359631744505046530314277 24442430952094696224433927)
    ·
      refine ⟨36663646428142044336650891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24442430952094696224433927 36663646428142044336650891)
      ·
        refine ⟨54995469642213066504976337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36663646428142044336650891 54995469642213066504976337)
        ·
          refine ⟨41246602231659799878732253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54995469642213066504976337 41246602231659799878732253)
          ·
            refine ⟨15467475836872424954524595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41246602231659799878732253 15467475836872424954524595)
            ·
              refine ⟨23201213755308637431786893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15467475836872424954524595 23201213755308637431786893)
              ·
                refine ⟨8700455158240739036920085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23201213755308637431786893 8700455158240739036920085)
                ·
                  refine ⟨407833835542534642355629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700455158240739036920085 407833835542534642355629)
                  ·
                    rfl

theorem cell22_3574141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3574141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574141 prefixEnd_3574141 := by exact prefixLift 3574141
  have htrace : WordTrace (prefixWord ++ tailWord_3574141) baseStart_3574141 baseEnd_3574141 := by
    simpa [prefixWord, tailWord_3574141, baseEnd_3574141] using wordTrace_append hprefix tailTrace_3574141
  have hstable : (prefixWord ++ tailWord_3574141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574141).length < 2 ^ (prefixWord ++ tailWord_3574141).sum := by decide
  have hdescent : baseEnd_3574141 < baseStart_3574141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574158 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_3574158 : Nat := 118140960795 + 3574158 * 2 ^ 59
def prefixEnd_3574158 : Nat := 4983230072969 + 3 ^ 40 * 3574158 * 2
def baseEnd_3574158 : Nat := 407835775358340516463945

theorem tailTrace_3574158 : CollatzResearch.WordTrace tailWord_3574158 prefixEnd_3574158 407835775358340516463945 := by
  unfold tailWord_3574158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295031473180432304210391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86906834523628972289122085 16295031473180432304210391)
  ·
    refine ⟨24442547209770648456315587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16295031473180432304210391 24442547209770648456315587)
    ·
      refine ⟨36663820814655972684473381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24442547209770648456315587 36663820814655972684473381)
      ·
        refine ⟨6874466402747994878338759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36663820814655972684473381 6874466402747994878338759)
        ·
          refine ⟨10311699604121992317508139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874466402747994878338759 10311699604121992317508139)
          ·
            refine ⟨15467549406182988476262209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10311699604121992317508139 15467549406182988476262209)
            ·
              refine ⟨11600662054637241357196657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467549406182988476262209 11600662054637241357196657)
              ·
                refine ⟨8700496540977931017897493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11600662054637241357196657 8700496540977931017897493)
                ·
                  refine ⟨407835775358340516463945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8700496540977931017897493 407835775358340516463945)
                  ·
                    rfl

theorem cell22_3574158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_3574158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574158 prefixEnd_3574158 := by exact prefixLift 3574158
  have htrace : WordTrace (prefixWord ++ tailWord_3574158) baseStart_3574158 baseEnd_3574158 := by
    simpa [prefixWord, tailWord_3574158, baseEnd_3574158] using wordTrace_append hprefix tailTrace_3574158
  have hstable : (prefixWord ++ tailWord_3574158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574158).length < 2 ^ (prefixWord ++ tailWord_3574158).sum := by decide
  have hdescent : baseEnd_3574158 < baseStart_3574158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574218 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3574218 : Nat := 118140960795 + 3574218 * 2 ^ 59
def prefixEnd_3574218 : Nat := 4983230072969 + 3 ^ 40 * 3574218 * 2
def baseEnd_3574218 : Nat := 1223527865301201392891651

theorem tailTrace_3574218 : CollatzResearch.WordTrace tailWord_3574218 prefixEnd_3574218 1223527865301201392891651 := by
  unfold tailWord_3574218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32590610041306522170216827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86908293443484059120578205 32590610041306522170216827)
  ·
    refine ⟨48885915061959783255325241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32590610041306522170216827 48885915061959783255325241)
    ·
      refine ⟨36664436296469837441493931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48885915061959783255325241 36664436296469837441493931)
      ·
        refine ⟨54996654444704756162240897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36664436296469837441493931 54996654444704756162240897)
        ·
          refine ⟨41247490833528567121680673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54996654444704756162240897 41247490833528567121680673)
          ·
            refine ⟨30935618125146425341260505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41247490833528567121680673 30935618125146425341260505)
            ·
              refine ⟨23201713593859819005945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30935618125146425341260505 23201713593859819005945379)
              ·
                refine ⟨34802570390789728508918069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23201713593859819005945379 34802570390789728508918069)
                ·
                  refine ⟨3262740974136537047711069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34802570390789728508918069 3262740974136537047711069)
                  ·
                    refine ⟨1223527865301201392891651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262740974136537047711069 1223527865301201392891651)
                    ·
                      rfl

theorem cell22_3574218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3574218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574218 prefixEnd_3574218 := by exact prefixLift 3574218
  have htrace : WordTrace (prefixWord ++ tailWord_3574218) baseStart_3574218 baseEnd_3574218 := by
    simpa [prefixWord, tailWord_3574218, baseEnd_3574218] using wordTrace_append hprefix tailTrace_3574218
  have hstable : (prefixWord ++ tailWord_3574218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574218).length < 2 ^ (prefixWord ++ tailWord_3574218).sum := by decide
  have hdescent : baseEnd_3574218 < baseStart_3574218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574248 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_3574248 : Nat := 118140960795 + 3574248 * 2 ^ 59
def prefixEnd_3574248 : Nat := 4983230072969 + 3 ^ 40 * 3574248 * 2
def baseEnd_3574248 : Nat := 407846044971430438213853

theorem tailTrace_3574248 : CollatzResearch.WordTrace tailWord_3574248 prefixEnd_3574248 407846044971430438213853 := by
  unfold tailWord_3574248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65181767177558701902229699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86909022903411602536306265 65181767177558701902229699)
  ·
    refine ⟨97772650766338052853344549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65181767177558701902229699 97772650766338052853344549)
    ·
      refine ⟨18332372018688384910002103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97772650766338052853344549 18332372018688384910002103)
      ·
        refine ⟨27498558028032577365003155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18332372018688384910002103 27498558028032577365003155)
        ·
          refine ⟨41247837042048866047504733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27498558028032577365003155 41247837042048866047504733)
          ·
            refine ⟨15467938890768324767814275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41247837042048866047504733 15467938890768324767814275)
            ·
              refine ⟨23201908336152487151721413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15467938890768324767814275 23201908336152487151721413)
              ·
                refine ⟨4350357813028591340947765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23201908336152487151721413 4350357813028591340947765)
                ·
                  refine ⟨407846044971430438213853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4350357813028591340947765 407846044971430438213853)
                  ·
                    rfl

theorem cell22_3574248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_3574248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574248 prefixEnd_3574248 := by exact prefixLift 3574248
  have htrace : WordTrace (prefixWord ++ tailWord_3574248) baseStart_3574248 baseEnd_3574248 := by
    simpa [prefixWord, tailWord_3574248, baseEnd_3574248] using wordTrace_append hprefix tailTrace_3574248
  have hstable : (prefixWord ++ tailWord_3574248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574248).length < 2 ^ (prefixWord ++ tailWord_3574248).sum := by decide
  have hdescent : baseEnd_3574248 < baseStart_3574248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574376 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3574376 : Nat := 118140960795 + 3574376 * 2 ^ 59
def prefixEnd_3574376 : Nat := 4983230072969 + 3 ^ 40 * 3574376 * 2
def baseEnd_3574376 : Nat := 1223581951930141647441167

theorem tailTrace_3574376 : CollatzResearch.WordTrace tailWord_3574376 prefixEnd_3574376 1223581951930141647441167 := by
  unfold tailWord_3574376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65184101449326840832559491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86912135265769121110079321 65184101449326840832559491)
  ·
    refine ⟨97776152173990261248839237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65184101449326840832559491 97776152173990261248839237)
    ·
      refine ⟨18333028532623173984157357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97776152173990261248839237 18333028532623173984157357)
      ·
        refine ⟨6874885699733690244059009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18333028532623173984157357 6874885699733690244059009)
        ·
          refine ⟨5156164274800267683044257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6874885699733690244059009 5156164274800267683044257)
          ·
            refine ⟨3867123206100200762283193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156164274800267683044257 3867123206100200762283193)
            ·
              refine ⟨2900342404575150571712395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867123206100200762283193 2900342404575150571712395)
              ·
                refine ⟨4350513606862725857568593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900342404575150571712395 4350513606862725857568593)
                ·
                  refine ⟨3262885205147044393176445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4350513606862725857568593 3262885205147044393176445)
                  ·
                    refine ⟨1223581951930141647441167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262885205147044393176445 1223581951930141647441167)
                    ·
                      rfl

theorem cell22_3574376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3574376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574376 prefixEnd_3574376 := by exact prefixLift 3574376
  have htrace : WordTrace (prefixWord ++ tailWord_3574376) baseStart_3574376 baseEnd_3574376 := by
    simpa [prefixWord, tailWord_3574376, baseEnd_3574376] using wordTrace_append hprefix tailTrace_3574376
  have hstable : (prefixWord ++ tailWord_3574376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574376).length < 2 ^ (prefixWord ++ tailWord_3574376).sum := by decide
  have hdescent : baseEnd_3574376 < baseStart_3574376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574445 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3574445 : Nat := 118140960795 + 3574445 * 2 ^ 59
def prefixEnd_3574445 : Nat := 4983230072969 + 3 ^ 40 * 3574445 * 2
def baseEnd_3574445 : Nat := 407868524013416155821985

theorem tailTrace_3574445 : CollatzResearch.WordTrace tailWord_3574445 prefixEnd_3574445 407868524013416155821985 := by
  unfold tailWord_3574445
  simp only [CollatzResearch.WordTrace]
  refine ⟨130370719535403706449380789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86913813023602470966253859 130370719535403706449380789)
  ·
    refine ⟨12222254956444097479629449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130370719535403706449380789 12222254956444097479629449)
    ·
      refine ⟨9166691217333073109722087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12222254956444097479629449 9166691217333073109722087)
      ·
        refine ⟨13750036825999609664583131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9166691217333073109722087 13750036825999609664583131)
        ·
          refine ⟨20625055238999414496874697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750036825999609664583131 20625055238999414496874697)
          ·
            refine ⟨15468791429249560872656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20625055238999414496874697 15468791429249560872656023)
            ·
              refine ⟨23203187143874341308984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468791429249560872656023 23203187143874341308984035)
              ·
                refine ⟨34804780715811511963476053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23203187143874341308984035 34804780715811511963476053)
                ·
                  refine ⟨407868524013416155821985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34804780715811511963476053 407868524013416155821985)
                  ·
                    rfl

theorem cell22_3574445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3574445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574445 prefixEnd_3574445 := by exact prefixLift 3574445
  have htrace : WordTrace (prefixWord ++ tailWord_3574445) baseStart_3574445 baseEnd_3574445 := by
    simpa [prefixWord, tailWord_3574445, baseEnd_3574445] using wordTrace_append hprefix tailTrace_3574445
  have hstable : (prefixWord ++ tailWord_3574445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574445).length < 2 ^ (prefixWord ++ tailWord_3574445).sum := by decide
  have hdescent : baseEnd_3574445 < baseStart_3574445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574460 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3574460 : Nat := 118140960795 + 3574460 * 2 ^ 59
def prefixEnd_3574460 : Nat := 4983230072969 + 3 ^ 40 * 3574460 * 2
def baseEnd_3574460 : Nat := 1223610706846793428340909

theorem tailTrace_3574460 : CollatzResearch.WordTrace tailWord_3574460 prefixEnd_3574460 1223610706846793428340909 := by
  unfold tailWord_3574460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65185633315174682005588417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86914177753566242674117889 65185633315174682005588417)
  ·
    refine ⟨48889224986381011504191313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65185633315174682005588417 48889224986381011504191313)
    ·
      refine ⟨36666918739785758628143485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48889224986381011504191313 36666918739785758628143485)
      ·
        refine ⟨13750094527419659485553807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36666918739785758628143485 13750094527419659485553807)
        ·
          refine ⟨20625141791129489228330711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13750094527419659485553807 20625141791129489228330711)
          ·
            refine ⟨30937712686694233842496067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20625141791129489228330711 30937712686694233842496067)
            ·
              refine ⟨46406569030041350763744101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30937712686694233842496067 46406569030041350763744101)
              ·
                refine ⟨8701231693132753268202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46406569030041350763744101 8701231693132753268202019)
                ·
                  refine ⟨13051847539699129902303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8701231693132753268202019 13051847539699129902303029)
                  ·
                    refine ⟨1223610706846793428340909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13051847539699129902303029 1223610706846793428340909)
                    ·
                      rfl

theorem cell22_3574460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3574460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574460 prefixEnd_3574460 := by exact prefixLift 3574460
  have htrace : WordTrace (prefixWord ++ tailWord_3574460) baseStart_3574460 baseEnd_3574460 := by
    simpa [prefixWord, tailWord_3574460, baseEnd_3574460] using wordTrace_append hprefix tailTrace_3574460
  have hstable : (prefixWord ++ tailWord_3574460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574460).length < 2 ^ (prefixWord ++ tailWord_3574460).sum := by decide
  have hdescent : baseEnd_3574460 < baseStart_3574460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574464 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_3574464 : Nat := 118140960795 + 3574464 * 2 ^ 59
def prefixEnd_3574464 : Nat := 4983230072969 + 3 ^ 40 * 3574464 * 2
def baseEnd_3574464 : Nat := 1223612076128538751240897

theorem tailTrace_3574464 : CollatzResearch.WordTrace tailWord_3574464 prefixEnd_3574464 1223612076128538751240897 := by
  unfold tailWord_3574464
  simp only [CollatzResearch.WordTrace]
  refine ⟨65185706261167436347161223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86914275014889915129548297 65185706261167436347161223)
  ·
    refine ⟨97778559391751154520741835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65185706261167436347161223 97778559391751154520741835)
    ·
      refine ⟨146667839087626731781112753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97778559391751154520741835 146667839087626731781112753)
      ·
        refine ⟨110000879315720048835834565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146667839087626731781112753 110000879315720048835834565)
        ·
          refine ⟨20625164871697509156718981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110000879315720048835834565 20625164871697509156718981)
          ·
            refine ⟨3867218413443282966884809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20625164871697509156718981 3867218413443282966884809)
            ·
              refine ⟨2900413810082462225163607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867218413443282966884809 2900413810082462225163607)
              ·
                refine ⟨4350620715123693337745411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900413810082462225163607 4350620715123693337745411)
                ·
                  refine ⟨6525931072685540006618117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350620715123693337745411 6525931072685540006618117)
                  ·
                    refine ⟨1223612076128538751240897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6525931072685540006618117 1223612076128538751240897)
                    ·
                      rfl

theorem cell22_3574464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_3574464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574464 prefixEnd_3574464 := by exact prefixLift 3574464
  have htrace : WordTrace (prefixWord ++ tailWord_3574464) baseStart_3574464 baseEnd_3574464 := by
    simpa [prefixWord, tailWord_3574464, baseEnd_3574464] using wordTrace_append hprefix tailTrace_3574464
  have hstable : (prefixWord ++ tailWord_3574464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574464).length < 2 ^ (prefixWord ++ tailWord_3574464).sum := by decide
  have hdescent : baseEnd_3574464 < baseStart_3574464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574492 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3574492 : Nat := 118140960795 + 3574492 * 2 ^ 59
def prefixEnd_3574492 : Nat := 4983230072969 + 3 ^ 40 * 3574492 * 2
def baseEnd_3574492 : Nat := 1223621661100756011540811

theorem tailTrace_3574492 : CollatzResearch.WordTrace tailWord_3574492 prefixEnd_3574492 1223621661100756011540811 := by
  unfold tailWord_3574492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65186216883116716738170865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86914955844155622317561153 65186216883116716738170865)
  ·
    refine ⟨48889662662337537553628149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65186216883116716738170865 48889662662337537553628149)
    ·
      refine ⟨4583405874594144145652639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48889662662337537553628149 4583405874594144145652639)
      ·
        refine ⟨6875108811891216218478959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583405874594144145652639 6875108811891216218478959)
        ·
          refine ⟨10312663217836824327718439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875108811891216218478959 10312663217836824327718439)
          ·
            refine ⟨15468994826755236491577659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10312663217836824327718439 15468994826755236491577659)
            ·
              refine ⟨23203492240132854737366489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15468994826755236491577659 23203492240132854737366489)
              ·
                refine ⟨17402619180099641053024867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23203492240132854737366489 17402619180099641053024867)
                ·
                  refine ⟨26103928770149461579537301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17402619180099641053024867 26103928770149461579537301)
                  ·
                    refine ⟨1223621661100756011540811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26103928770149461579537301 1223621661100756011540811)
                    ·
                      rfl

theorem cell22_3574492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3574492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574492 prefixEnd_3574492 := by exact prefixLift 3574492
  have htrace : WordTrace (prefixWord ++ tailWord_3574492) baseStart_3574492 baseEnd_3574492 := by
    simpa [prefixWord, tailWord_3574492, baseEnd_3574492] using wordTrace_append hprefix tailTrace_3574492
  have hstable : (prefixWord ++ tailWord_3574492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574492).length < 2 ^ (prefixWord ++ tailWord_3574492).sum := by decide
  have hdescent : baseEnd_3574492 < baseStart_3574492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574590 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3574590 : Nat := 118140960795 + 3574590 * 2 ^ 59
def prefixEnd_3574590 : Nat := 4983230072969 + 3 ^ 40 * 3574590 * 2
def baseEnd_3574590 : Nat := 1223655208503516422590511

theorem tailTrace_3574590 : CollatzResearch.WordTrace tailWord_3574590 prefixEnd_3574590 1223655208503516422590511 := by
  unfold tailWord_3574590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297001014984799526676153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86917338746585597475606149 16297001014984799526676153)
  ·
    refine ⟨12222750761238599645007115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16297001014984799526676153 12222750761238599645007115)
    ·
      refine ⟨18334126141857899467510673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12222750761238599645007115 18334126141857899467510673)
      ·
        refine ⟨13750594606393424600633005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18334126141857899467510673 13750594606393424600633005)
        ·
          refine ⟨5156472977397534225237377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13750594606393424600633005 5156472977397534225237377)
          ·
            refine ⟨3867354733048150668928033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156472977397534225237377 3867354733048150668928033)
            ·
              refine ⟨2900516049786113001696025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867354733048150668928033 2900516049786113001696025)
              ·
                refine ⟨2175387037339584751272019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900516049786113001696025 2175387037339584751272019)
                ·
                  refine ⟨3263080556009377126908029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175387037339584751272019 3263080556009377126908029)
                  ·
                    refine ⟨1223655208503516422590511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263080556009377126908029 1223655208503516422590511)
                    ·
                      rfl

theorem cell22_3574590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3574590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574590 prefixEnd_3574590 := by exact prefixLift 3574590
  have htrace : WordTrace (prefixWord ++ tailWord_3574590) baseStart_3574590 baseEnd_3574590 := by
    simpa [prefixWord, tailWord_3574590, baseEnd_3574590] using wordTrace_append hprefix tailTrace_3574590
  have hstable : (prefixWord ++ tailWord_3574590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574590).length < 2 ^ (prefixWord ++ tailWord_3574590).sum := by decide
  have hdescent : baseEnd_3574590 < baseStart_3574590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574595 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_3574595 : Nat := 118140960795 + 3574595 * 2 ^ 59
def prefixEnd_3574595 : Nat := 4983230072969 + 3 ^ 40 * 3574595 * 2
def baseEnd_3574595 : Nat := 1223656920105698076215495

theorem tailTrace_3574595 : CollatzResearch.WordTrace tailWord_3574595 prefixEnd_3574595 1223656920105698076215495 := by
  unfold tailWord_3574595
  simp only [CollatzResearch.WordTrace]
  refine ⟨130376190484860282067341239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86917460323240188044894159 130376190484860282067341239)
  ·
    refine ⟨195564285727290423101011859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130376190484860282067341239 195564285727290423101011859)
    ·
      refine ⟨293346428590935634651517789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195564285727290423101011859 293346428590935634651517789)
      ·
        refine ⟨110004910721600862994319171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293346428590935634651517789 110004910721600862994319171)
        ·
          refine ⟨165007366082401294491478757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110004910721600862994319171 165007366082401294491478757)
          ·
            refine ⟨30938881140450242717152267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165007366082401294491478757 30938881140450242717152267)
            ·
              refine ⟨46408321710675364075728401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30938881140450242717152267 46408321710675364075728401)
              ·
                refine ⟨34806241283006523056796301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46408321710675364075728401 34806241283006523056796301)
                ·
                  refine ⟨13052340481127446146298613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34806241283006523056796301 13052340481127446146298613)
                  ·
                    refine ⟨1223656920105698076215495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13052340481127446146298613 1223656920105698076215495)
                    ·
                      rfl

theorem cell22_3574595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_3574595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574595 prefixEnd_3574595 := by exact prefixLift 3574595
  have htrace : WordTrace (prefixWord ++ tailWord_3574595) baseStart_3574595 baseEnd_3574595 := by
    simpa [prefixWord, tailWord_3574595, baseEnd_3574595] using wordTrace_append hprefix tailTrace_3574595
  have hstable : (prefixWord ++ tailWord_3574595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574595).length < 2 ^ (prefixWord ++ tailWord_3574595).sum := by decide
  have hdescent : baseEnd_3574595 < baseStart_3574595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574627 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_3574627 : Nat := 118140960795 + 3574627 * 2 ^ 59
def prefixEnd_3574627 : Nat := 4983230072969 + 3 ^ 40 * 3574627 * 2
def baseEnd_3574627 : Nat := 1223667874359660659415397

theorem tailTrace_3574627 : CollatzResearch.WordTrace tailWord_3574627 prefixEnd_3574627 1223667874359660659415397 := by
  unfold tailWord_3574627
  simp only [CollatzResearch.WordTrace]
  refine ⟨130377357620744351532506135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86918238413829567688337423 130377357620744351532506135)
  ·
    refine ⟨195566036431116527298759203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130377357620744351532506135 195566036431116527298759203)
    ·
      refine ⟨293349054646674790948138805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195566036431116527298759203 293349054646674790948138805)
      ·
        refine ⟨27501473873125761651388013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 293349054646674790948138805 27501473873125761651388013)
        ·
          refine ⟨10313052702422160619270505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27501473873125761651388013 10313052702422160619270505)
          ·
            refine ⟨7734789526816620464452879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313052702422160619270505 7734789526816620464452879)
            ·
              refine ⟨11602184290224930696679319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734789526816620464452879 11602184290224930696679319)
              ·
                refine ⟨17403276435337396045018979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602184290224930696679319 17403276435337396045018979)
                ·
                  refine ⟨26104914653006094067528469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17403276435337396045018979 26104914653006094067528469)
                  ·
                    refine ⟨1223667874359660659415397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26104914653006094067528469 1223667874359660659415397)
                    ·
                      rfl

theorem cell22_3574627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_3574627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574627 prefixEnd_3574627 := by exact prefixLift 3574627
  have htrace : WordTrace (prefixWord ++ tailWord_3574627) baseStart_3574627 baseEnd_3574627 := by
    simpa [prefixWord, tailWord_3574627, baseEnd_3574627] using wordTrace_append hprefix tailTrace_3574627
  have hstable : (prefixWord ++ tailWord_3574627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574627).length < 2 ^ (prefixWord ++ tailWord_3574627).sum := by decide
  have hdescent : baseEnd_3574627 < baseStart_3574627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574646 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3574646 : Nat := 118140960795 + 3574646 * 2 ^ 59
def prefixEnd_3574646 : Nat := 4983230072969 + 3 ^ 40 * 3574646 * 2
def baseEnd_3574646 : Nat := 1223674378447950943190339

theorem tailTrace_3574646 : CollatzResearch.WordTrace tailWord_3574646 prefixEnd_3574646 1223674378447950943190339 := by
  unfold tailWord_3574646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148628162979719861090487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86918700405117011851631861 8148628162979719861090487)
  ·
    refine ⟨12222942244469579791635731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8148628162979719861090487 12222942244469579791635731)
    ·
      refine ⟨18334413366704369687453597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12222942244469579791635731 18334413366704369687453597)
      ·
        refine ⟨6875405012514138632795099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18334413366704369687453597 6875405012514138632795099)
        ·
          refine ⟨10313107518771207949192649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875405012514138632795099 10313107518771207949192649)
          ·
            refine ⟨7734830639078405961894487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10313107518771207949192649 7734830639078405961894487)
            ·
              refine ⟨11602245958617608942841731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734830639078405961894487 11602245958617608942841731)
              ·
                refine ⟨17403368937926413414262597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602245958617608942841731 17403368937926413414262597)
                ·
                  refine ⟨3263131675861202515174237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17403368937926413414262597 3263131675861202515174237)
                  ·
                    refine ⟨1223674378447950943190339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263131675861202515174237 1223674378447950943190339)
                    ·
                      rfl

theorem cell22_3574646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3574646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574646 prefixEnd_3574646 := by exact prefixLift 3574646
  have htrace : WordTrace (prefixWord ++ tailWord_3574646) baseStart_3574646 baseEnd_3574646 := by
    simpa [prefixWord, tailWord_3574646, baseEnd_3574646] using wordTrace_append hprefix tailTrace_3574646
  have hstable : (prefixWord ++ tailWord_3574646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574646).length < 2 ^ (prefixWord ++ tailWord_3574646).sum := by decide
  have hdescent : baseEnd_3574646 < baseStart_3574646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574655 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3574655 : Nat := 118140960795 + 3574655 * 2 ^ 59
def prefixEnd_3574655 : Nat := 4983230072969 + 3 ^ 40 * 3574655 * 2
def baseEnd_3574655 : Nat := 1223677459331877919715311

theorem tailTrace_3574655 : CollatzResearch.WordTrace tailWord_3574655 prefixEnd_3574655 1223677459331877919715311 := by
  unfold tailWord_3574655
  simp only [CollatzResearch.WordTrace]
  refine ⟨130378378864642912314525419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86918919243095274876350279 130378378864642912314525419)
  ·
    refine ⟨195567568296964368471788129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130378378864642912314525419 195567568296964368471788129)
    ·
      refine ⟨146675676222723276353841097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195567568296964368471788129 146675676222723276353841097)
      ·
        refine ⟨110006757167042457265380823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146675676222723276353841097 110006757167042457265380823)
        ·
          refine ⟨165010135750563685898071235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110006757167042457265380823 165010135750563685898071235)
          ·
            refine ⟨247515203625845528847106853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165010135750563685898071235 247515203625845528847106853)
            ·
              refine ⟨46409100679846036658832535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247515203625845528847106853 46409100679846036658832535)
              ·
                refine ⟨69613651019769054988248803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46409100679846036658832535 69613651019769054988248803)
                ·
                  refine ⟨104420476529653582482373205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69613651019769054988248803 104420476529653582482373205)
                  ·
                    refine ⟨1223677459331877919715311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104420476529653582482373205 1223677459331877919715311)
                    ·
                      rfl

theorem cell22_3574655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3574655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574655 prefixEnd_3574655 := by exact prefixLift 3574655
  have htrace : WordTrace (prefixWord ++ tailWord_3574655) baseStart_3574655 baseEnd_3574655 := by
    simpa [prefixWord, tailWord_3574655, baseEnd_3574655] using wordTrace_append hprefix tailTrace_3574655
  have hstable : (prefixWord ++ tailWord_3574655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574655).length < 2 ^ (prefixWord ++ tailWord_3574655).sum := by decide
  have hdescent : baseEnd_3574655 < baseStart_3574655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574687 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 7]
def baseStart_3574687 : Nat := 118140960795 + 3574687 * 2 ^ 59
def prefixEnd_3574687 : Nat := 4983230072969 + 3 ^ 40 * 3574687 * 2
def baseEnd_3574687 : Nat := 407896137861946834305071

theorem tailTrace_3574687 : CollatzResearch.WordTrace tailWord_3574687 prefixEnd_3574687 407896137861946834305071 := by
  unfold tailWord_3574687
  simp only [CollatzResearch.WordTrace]
  refine ⟨130379546000526981779690315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86919697333684654519793543 130379546000526981779690315)
  ·
    refine ⟨195569319000790472669535473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130379546000526981779690315 195569319000790472669535473)
    ·
      refine ⟨146676989250592854502151605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195569319000790472669535473 146676989250592854502151605)
      ·
        refine ⟨13750967742243080109576713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146676989250592854502151605 13750967742243080109576713)
        ·
          refine ⟨10313225806682310082182535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13750967742243080109576713 10313225806682310082182535)
          ·
            refine ⟨15469838710023465123273803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313225806682310082182535 15469838710023465123273803)
            ·
              refine ⟨23204758065035197684910705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15469838710023465123273803 23204758065035197684910705)
              ·
                refine ⟨17403568548776398263683029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23204758065035197684910705 17403568548776398263683029)
                ·
                  refine ⟨407896137861946834305071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17403568548776398263683029 407896137861946834305071)
                  ·
                    rfl

theorem cell22_3574687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 7].length) (baseStart_3574687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574687 prefixEnd_3574687 := by exact prefixLift 3574687
  have htrace : WordTrace (prefixWord ++ tailWord_3574687) baseStart_3574687 baseEnd_3574687 := by
    simpa [prefixWord, tailWord_3574687, baseEnd_3574687] using wordTrace_append hprefix tailTrace_3574687
  have hstable : (prefixWord ++ tailWord_3574687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574687).length < 2 ^ (prefixWord ++ tailWord_3574687).sum := by decide
  have hdescent : baseEnd_3574687 < baseStart_3574687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574691 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 1, 3]
def baseStart_3574691 : Nat := 118140960795 + 3574691 * 2 ^ 59
def prefixEnd_3574691 : Nat := 4983230072969 + 3 ^ 40 * 3574691 * 2
def baseEnd_3574691 : Nat := 1223689782867585825815201

theorem tailTrace_3574691 : CollatzResearch.WordTrace tailWord_3574691 prefixEnd_3574691 1223689782867585825815201 := by
  unfold tailWord_3574691
  simp only [CollatzResearch.WordTrace]
  refine ⟨130379691892512490462835927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86919794595008326975223951 130379691892512490462835927)
  ·
    refine ⟨195569537838768735694253891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130379691892512490462835927 195569537838768735694253891)
    ·
      refine ⟨293354306758153103541380837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195569537838768735694253891 293354306758153103541380837)
      ·
        refine ⟨55003932517153706914008907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293354306758153103541380837 55003932517153706914008907)
        ·
          refine ⟨82505898775730560371013361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55003932517153706914008907 82505898775730560371013361)
          ·
            refine ⟨61879424081797920278260021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82505898775730560371013361 61879424081797920278260021)
            ·
              refine ⟨5801196007668555026086877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61879424081797920278260021 5801196007668555026086877)
              ·
                refine ⟨2175448502875708134782579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5801196007668555026086877 2175448502875708134782579)
                ·
                  refine ⟨3263172754313562202173869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175448502875708134782579 3263172754313562202173869)
                  ·
                    refine ⟨1223689782867585825815201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263172754313562202173869 1223689782867585825815201)
                    ·
                      rfl

theorem cell22_3574691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 3].length) (baseStart_3574691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574691 prefixEnd_3574691 := by exact prefixLift 3574691
  have htrace : WordTrace (prefixWord ++ tailWord_3574691) baseStart_3574691 baseEnd_3574691 := by
    simpa [prefixWord, tailWord_3574691, baseEnd_3574691] using wordTrace_append hprefix tailTrace_3574691
  have hstable : (prefixWord ++ tailWord_3574691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574691).length < 2 ^ (prefixWord ++ tailWord_3574691).sum := by decide
  have hdescent : baseEnd_3574691 < baseStart_3574691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574708 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3574708 : Nat := 118140960795 + 3574708 * 2 ^ 59
def prefixEnd_3574708 : Nat := 4983230072969 + 3 ^ 40 * 3574708 * 2
def baseEnd_3574708 : Nat := 1223695602315003448140149

theorem tailTrace_3574708 : CollatzResearch.WordTrace tailWord_3574708 prefixEnd_3574708 1223695602315003448140149 := by
  unfold tailWord_3574708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190155966725451183102389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86920207955633934910803185 65190155966725451183102389)
  ·
    refine ⟨6111577121880511048415849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65190155966725451183102389 6111577121880511048415849)
    ·
      refine ⟨4583682841410383286311887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111577121880511048415849 4583682841410383286311887)
      ·
        refine ⟨6875524262115574929467831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583682841410383286311887 6875524262115574929467831)
        ·
          refine ⟨10313286393173362394201747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875524262115574929467831 10313286393173362394201747)
          ·
            refine ⟨15469929589760043591302621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313286393173362394201747 15469929589760043591302621)
            ·
              refine ⟨5801223596160016346738483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15469929589760043591302621 5801223596160016346738483)
              ·
                refine ⟨8701835394240024520107725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801223596160016346738483 8701835394240024520107725)
                ·
                  refine ⟨3263188272840009195040397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8701835394240024520107725 3263188272840009195040397)
                  ·
                    refine ⟨1223695602315003448140149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263188272840009195040397 1223695602315003448140149)
                    ·
                      rfl

theorem cell22_3574708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3574708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574708 prefixEnd_3574708 := by exact prefixLift 3574708
  have htrace : WordTrace (prefixWord ++ tailWord_3574708) baseStart_3574708 baseEnd_3574708 := by
    simpa [prefixWord, tailWord_3574708, baseEnd_3574708] using wordTrace_append hprefix tailTrace_3574708
  have hstable : (prefixWord ++ tailWord_3574708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574708).length < 2 ^ (prefixWord ++ tailWord_3574708).sum := by decide
  have hdescent : baseEnd_3574708 < baseStart_3574708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574732 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3574732 : Nat := 118140960795 + 3574732 * 2 ^ 59
def prefixEnd_3574732 : Nat := 4983230072969 + 3 ^ 40 * 3574732 * 2
def baseEnd_3574732 : Nat := 407901272668491795180025

theorem tailTrace_3574732 : CollatzResearch.WordTrace tailWord_3574732 prefixEnd_3574732 407901272668491795180025 := by
  unfold tailWord_3574732
  simp only [CollatzResearch.WordTrace]
  refine ⟨65190593642681977232539225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86920791523575969643385633 65190593642681977232539225)
  ·
    refine ⟨48892945232011482924404419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65190593642681977232539225 48892945232011482924404419)
    ·
      refine ⟨73339417848017224386606629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48892945232011482924404419 73339417848017224386606629)
      ·
        refine ⟨13751140846503229572488743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73339417848017224386606629 13751140846503229572488743)
        ·
          refine ⟨20626711269754844358733115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13751140846503229572488743 20626711269754844358733115)
          ·
            refine ⟨30940066904632266538099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20626711269754844358733115 30940066904632266538099673)
            ·
              refine ⟨23205050178474199903574755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30940066904632266538099673 23205050178474199903574755)
              ·
                refine ⟨34807575267711299855362133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23205050178474199903574755 34807575267711299855362133)
                ·
                  refine ⟨407901272668491795180025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34807575267711299855362133 407901272668491795180025)
                  ·
                    rfl

theorem cell22_3574732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3574732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574732 prefixEnd_3574732 := by exact prefixLift 3574732
  have htrace : WordTrace (prefixWord ++ tailWord_3574732) baseStart_3574732 baseEnd_3574732 := by
    simpa [prefixWord, tailWord_3574732, baseEnd_3574732] using wordTrace_append hprefix tailTrace_3574732
  have hstable : (prefixWord ++ tailWord_3574732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574732).length < 2 ^ (prefixWord ++ tailWord_3574732).sum := by decide
  have hdescent : baseEnd_3574732 < baseStart_3574732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574734 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3574734 : Nat := 118140960795 + 3574734 * 2 ^ 59
def prefixEnd_3574734 : Nat := 4983230072969 + 3 ^ 40 * 3574734 * 2
def baseEnd_3574734 : Nat := 1223704502646348046990069

theorem tailTrace_3574734 : CollatzResearch.WordTrace tailWord_3574734 prefixEnd_3574734 1223704502646348046990069 := by
  unfold tailWord_3574734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297657528919588600831407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86920840154237805871100837 16297657528919588600831407)
  ·
    refine ⟨24446486293379382901247111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16297657528919588600831407 24446486293379382901247111)
    ·
      refine ⟨36669729440069074351870667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24446486293379382901247111 36669729440069074351870667)
      ·
        refine ⟨55004594160103611527806001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36669729440069074351870667 55004594160103611527806001)
        ·
          refine ⟨41253445620077708645854501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55004594160103611527806001 41253445620077708645854501)
          ·
            refine ⟨7735021053764570371097719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41253445620077708645854501 7735021053764570371097719)
            ·
              refine ⟨11602531580646855556646579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735021053764570371097719 11602531580646855556646579)
              ·
                refine ⟨17403797370970283334969869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602531580646855556646579 17403797370970283334969869)
                ·
                  refine ⟨6526424014113856250613701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17403797370970283334969869 6526424014113856250613701)
                  ·
                    refine ⟨1223704502646348046990069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526424014113856250613701 1223704502646348046990069)
                    ·
                      rfl

theorem cell22_3574734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3574734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574734 prefixEnd_3574734 := by exact prefixLift 3574734
  have htrace : WordTrace (prefixWord ++ tailWord_3574734) baseStart_3574734 baseEnd_3574734 := by
    simpa [prefixWord, tailWord_3574734, baseEnd_3574734] using wordTrace_append hprefix tailTrace_3574734
  have hstable : (prefixWord ++ tailWord_3574734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574734).length < 2 ^ (prefixWord ++ tailWord_3574734).sum := by decide
  have hdescent : baseEnd_3574734 < baseStart_3574734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574796 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_3574796 : Nat := 118140960795 + 3574796 * 2 ^ 59
def prefixEnd_3574796 : Nat := 4983230072969 + 3 ^ 40 * 3574796 * 2
def baseEnd_3574796 : Nat := 1223725726513400551939879

theorem tailTrace_3574796 : CollatzResearch.WordTrace tailWord_3574796 prefixEnd_3574796 1223725726513400551939879 := by
  unfold tailWord_3574796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65191760778566046697704121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86922347704754728930272161 65191760778566046697704121)
  ·
    refine ⟨48893820583924535023278091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65191760778566046697704121 48893820583924535023278091)
    ·
      refine ⟨73340730875886802534917137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48893820583924535023278091 73340730875886802534917137)
      ·
        refine ⟨55005548156915101901187853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73340730875886802534917137 55005548156915101901187853)
        ·
          refine ⟨20627080558843163212945445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55005548156915101901187853 20627080558843163212945445)
          ·
            refine ⟨3867577604783093102427271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20627080558843163212945445 3867577604783093102427271)
            ·
              refine ⟨5801366407174639653640907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867577604783093102427271 5801366407174639653640907)
              ·
                refine ⟨8702049610761959480461361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801366407174639653640907 8702049610761959480461361)
                ·
                  refine ⟨6526537208071469610346021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8702049610761959480461361 6526537208071469610346021)
                  ·
                    refine ⟨1223725726513400551939879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526537208071469610346021 1223725726513400551939879)
                    ·
                      rfl

theorem cell22_3574796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_3574796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574796 prefixEnd_3574796 := by exact prefixLift 3574796
  have htrace : WordTrace (prefixWord ++ tailWord_3574796) baseStart_3574796 baseEnd_3574796 := by
    simpa [prefixWord, tailWord_3574796, baseEnd_3574796] using wordTrace_append hprefix tailTrace_3574796
  have hstable : (prefixWord ++ tailWord_3574796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574796).length < 2 ^ (prefixWord ++ tailWord_3574796).sum := by decide
  have hdescent : baseEnd_3574796 < baseStart_3574796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574867 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 10]
def baseStart_3574867 : Nat := 118140960795 + 3574867 * 2 ^ 59
def prefixEnd_3574867 : Nat := 4983230072969 + 3 ^ 40 * 3574867 * 2
def baseEnd_3574867 : Nat := 407916677088126677804887

theorem tailTrace_3574867 : CollatzResearch.WordTrace tailWord_3574867 prefixEnd_3574867 407916677088126677804887 := by
  unfold tailWord_3574867
  simp only [CollatzResearch.WordTrace]
  refine ⟨130386111139874872521242855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86924074093249915014161903 130386111139874872521242855)
  ·
    refine ⟨195579166709812308781864283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130386111139874872521242855 195579166709812308781864283)
    ·
      refine ⟨293368750064718463172796425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195579166709812308781864283 293368750064718463172796425)
      ·
        refine ⟨220026562548538847379597319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293368750064718463172796425 220026562548538847379597319)
        ·
          refine ⟨330039843822808271069395979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220026562548538847379597319 330039843822808271069395979)
          ·
            refine ⟨495059765734212406604093969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330039843822808271069395979 495059765734212406604093969)
            ·
              refine ⟨371294824300659304953070477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495059765734212406604093969 371294824300659304953070477)
              ·
                refine ⟨139235559112747239357401429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371294824300659304953070477 139235559112747239357401429)
                ·
                  refine ⟨407916677088126677804887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139235559112747239357401429 407916677088126677804887)
                  ·
                    rfl

theorem cell22_3574867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 10].length) (baseStart_3574867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574867 prefixEnd_3574867 := by exact prefixLift 3574867
  have htrace : WordTrace (prefixWord ++ tailWord_3574867) baseStart_3574867 baseEnd_3574867 := by
    simpa [prefixWord, tailWord_3574867, baseEnd_3574867] using wordTrace_append hprefix tailTrace_3574867
  have hstable : (prefixWord ++ tailWord_3574867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574867).length < 2 ^ (prefixWord ++ tailWord_3574867).sum := by decide
  have hdescent : baseEnd_3574867 < baseStart_3574867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574877 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3574877 : Nat := 118140960795 + 3574877 * 2 ^ 59
def prefixEnd_3574877 : Nat := 4983230072969 + 3 ^ 40 * 3574877 * 2
def baseEnd_3574877 : Nat := 1223753454468743340664631

theorem tailTrace_3574877 : CollatzResearch.WordTrace tailWord_3574877 prefixEnd_3574877 1223753454468743340664631 := by
  unfold tailWord_3574877
  simp only [CollatzResearch.WordTrace]
  refine ⟨130386475869838644229106885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86924317246559096152737923 130386475869838644229106885)
  ·
    refine ⟨24447464225594745792957541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130386475869838644229106885 24447464225594745792957541)
    ·
      refine ⟨4583899542299014836179539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24447464225594745792957541 4583899542299014836179539)
      ·
        refine ⟨6875849313448522254269309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583899542299014836179539 6875849313448522254269309)
        ·
          refine ⟨2578443492543195845350991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6875849313448522254269309 2578443492543195845350991)
          ·
            refine ⟨3867665238814793768026487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578443492543195845350991 3867665238814793768026487)
            ·
              refine ⟨5801497858222190652039731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867665238814793768026487 5801497858222190652039731)
              ·
                refine ⟨8702246787333285978059597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801497858222190652039731 8702246787333285978059597)
                ·
                  refine ⟨3263342545249982241772349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8702246787333285978059597 3263342545249982241772349)
                  ·
                    refine ⟨1223753454468743340664631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263342545249982241772349 1223753454468743340664631)
                    ·
                      rfl

theorem cell22_3574877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3574877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574877 prefixEnd_3574877 := by exact prefixLift 3574877
  have htrace : WordTrace (prefixWord ++ tailWord_3574877) baseStart_3574877 baseEnd_3574877 := by
    simpa [prefixWord, tailWord_3574877, baseEnd_3574877] using wordTrace_append hprefix tailTrace_3574877
  have hstable : (prefixWord ++ tailWord_3574877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574877).length < 2 ^ (prefixWord ++ tailWord_3574877).sum := by decide
  have hdescent : baseEnd_3574877 < baseStart_3574877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574916 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3574916 : Nat := 118140960795 + 3574916 * 2 ^ 59
def prefixEnd_3574916 : Nat := 4983230072969 + 3 ^ 40 * 3574916 * 2
def baseEnd_3574916 : Nat := 1223766804965760238939511

theorem tailTrace_3574916 : CollatzResearch.WordTrace tailWord_3574916 prefixEnd_3574916 1223766804965760238939511 := by
  unfold tailWord_3574916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65193949158348676944888301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86925265544464902593184401 65193949158348676944888301)
  ·
    refine ⟨24447730934380753854333113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65193949158348676944888301 24447730934380753854333113)
    ·
      refine ⟨18335798200785565390749835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24447730934380753854333113 18335798200785565390749835)
      ·
        refine ⟨27503697301178348086124753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18335798200785565390749835 27503697301178348086124753)
        ·
          refine ⟨20627772975883761064593565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27503697301178348086124753 20627772975883761064593565)
          ·
            refine ⟨7735414865956410399222587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20627772975883761064593565 7735414865956410399222587)
            ·
              refine ⟨11603122298934615598833881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735414865956410399222587 11603122298934615598833881)
              ·
                refine ⟨8702341724200961699125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11603122298934615598833881 8702341724200961699125411)
                ·
                  refine ⟨13053512586301442548688117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702341724200961699125411 13053512586301442548688117)
                  ·
                    refine ⟨1223766804965760238939511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13053512586301442548688117 1223766804965760238939511)
                    ·
                      rfl

theorem cell22_3574916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3574916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574916 prefixEnd_3574916 := by exact prefixLift 3574916
  have htrace : WordTrace (prefixWord ++ tailWord_3574916) baseStart_3574916 baseEnd_3574916 := by
    simpa [prefixWord, tailWord_3574916, baseEnd_3574916] using wordTrace_append hprefix tailTrace_3574916
  have hstable : (prefixWord ++ tailWord_3574916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574916).length < 2 ^ (prefixWord ++ tailWord_3574916).sum := by decide
  have hdescent : baseEnd_3574916 < baseStart_3574916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574920 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_3574920 : Nat := 118140960795 + 3574920 * 2 ^ 59
def prefixEnd_3574920 : Nat := 4983230072969 + 3 ^ 40 * 3574920 * 2
def baseEnd_3574920 : Nat := 1223768174247505561839499

theorem tailTrace_3574920 : CollatzResearch.WordTrace tailWord_3574920 prefixEnd_3574920 1223768174247505561839499 := by
  unfold tailWord_3574920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65194022104341431286461107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86925362805788575048614809 65194022104341431286461107)
  ·
    refine ⟨97791033156512146929691661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65194022104341431286461107 97791033156512146929691661)
    ·
      refine ⟨36671637433692055098634373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97791033156512146929691661 36671637433692055098634373)
      ·
        refine ⟨6875932018817260330993945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36671637433692055098634373 6875932018817260330993945)
        ·
          refine ⟨5156949014112945248245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6875932018817260330993945 5156949014112945248245459)
          ·
            refine ⟨7735423521169417872368189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156949014112945248245459 7735423521169417872368189)
            ·
              refine ⟨2900783820438531702138071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735423521169417872368189 2900783820438531702138071)
              ·
                refine ⟨4351175730657797553207107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900783820438531702138071 4351175730657797553207107)
                ·
                  refine ⟨6526763595986696329810661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351175730657797553207107 6526763595986696329810661)
                  ·
                    refine ⟨1223768174247505561839499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6526763595986696329810661 1223768174247505561839499)
                    ·
                      rfl

theorem cell22_3574920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_3574920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574920 prefixEnd_3574920 := by exact prefixLift 3574920
  have htrace : WordTrace (prefixWord ++ tailWord_3574920) baseStart_3574920 baseEnd_3574920 := by
    simpa [prefixWord, tailWord_3574920, baseEnd_3574920] using wordTrace_append hprefix tailTrace_3574920
  have hstable : (prefixWord ++ tailWord_3574920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574920).length < 2 ^ (prefixWord ++ tailWord_3574920).sum := by decide
  have hdescent : baseEnd_3574920 < baseStart_3574920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3574935 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 4]
def baseStart_3574935 : Nat := 118140960795 + 3574935 * 2 ^ 59
def prefixEnd_3574935 : Nat := 4983230072969 + 3 ^ 40 * 3574935 * 2
def baseEnd_3574935 : Nat := 407924436351350174238151

theorem tailTrace_3574935 : CollatzResearch.WordTrace tailWord_3574935 prefixEnd_3574935 407924436351350174238151 := by
  unfold tailWord_3574935
  simp only [CollatzResearch.WordTrace]
  refine ⟨130388591303628520134718259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86925727535752346756478839 130388591303628520134718259)
  ·
    refine ⟨195582886955442780202077389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130388591303628520134718259 195582886955442780202077389)
    ·
      refine ⟨73343582608291042575779021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195582886955442780202077389 73343582608291042575779021)
      ·
        refine ⟨27503843478109140965917133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73343582608291042575779021 27503843478109140965917133)
        ·
          refine ⟨10313941304290927862218925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27503843478109140965917133 10313941304290927862218925)
          ·
            refine ⟨3867727989109097948332097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10313941304290927862218925 3867727989109097948332097)
            ·
              refine ⟨2900795991831823461249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867727989109097948332097 2900795991831823461249073)
              ·
                refine ⟨2175596993873867595936805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900795991831823461249073 2175596993873867595936805)
                ·
                  refine ⟨407924436351350174238151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2175596993873867595936805 407924436351350174238151)
                  ·
                    rfl

theorem cell22_3574935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 4].length) (baseStart_3574935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3574935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3574935 prefixEnd_3574935 := by exact prefixLift 3574935
  have htrace : WordTrace (prefixWord ++ tailWord_3574935) baseStart_3574935 baseEnd_3574935 := by
    simpa [prefixWord, tailWord_3574935, baseEnd_3574935] using wordTrace_append hprefix tailTrace_3574935
  have hstable : (prefixWord ++ tailWord_3574935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3574935).length < 2 ^ (prefixWord ++ tailWord_3574935).sum := by decide
  have hdescent : baseEnd_3574935 < baseStart_3574935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3574935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575008 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_3575008 : Nat := 118140960795 + 3575008 * 2 ^ 59
def prefixEnd_3575008 : Nat := 4983230072969 + 3 ^ 40 * 3575008 * 2
def baseEnd_3575008 : Nat := 407932766148634221879743

theorem tailTrace_3575008 : CollatzResearch.WordTrace tailWord_3575008 prefixEnd_3575008 407932766148634221879743 := by
  unfold tailWord_3575008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65195626916182026801062839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86927502554909369068083785 65195626916182026801062839)
  ·
    refine ⟨97793440374273040201594259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65195626916182026801062839 97793440374273040201594259)
    ·
      refine ⟨146690160561409560302391389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97793440374273040201594259 146690160561409560302391389)
      ·
        refine ⟨55008810210528585113396771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146690160561409560302391389 55008810210528585113396771)
        ·
          refine ⟨82513215315792877670095157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55008810210528585113396771 82513215315792877670095157)
          ·
            refine ⟨7735613935855582281571421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82513215315792877670095157 7735613935855582281571421)
            ·
              refine ⟨2900855225945843355589283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735613935855582281571421 2900855225945843355589283)
              ·
                refine ⟨4351282838918765033383925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900855225945843355589283 4351282838918765033383925)
                ·
                  refine ⟨407932766148634221879743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351282838918765033383925 407932766148634221879743)
                  ·
                    rfl

theorem cell22_3575008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_3575008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575008 prefixEnd_3575008 := by exact prefixLift 3575008
  have htrace : WordTrace (prefixWord ++ tailWord_3575008) baseStart_3575008 baseEnd_3575008 := by
    simpa [prefixWord, tailWord_3575008, baseEnd_3575008] using wordTrace_append hprefix tailTrace_3575008
  have hstable : (prefixWord ++ tailWord_3575008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575008).length < 2 ^ (prefixWord ++ tailWord_3575008).sum := by decide
  have hdescent : baseEnd_3575008 < baseStart_3575008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575072 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_3575072 : Nat := 118140960795 + 3575072 * 2 ^ 59
def prefixEnd_3575072 : Nat := 4983230072969 + 3 ^ 40 * 3575072 * 2
def baseEnd_3575072 : Nat := 1223820206953827832039033

theorem tailTrace_3575072 : CollatzResearch.WordTrace tailWord_3575072 prefixEnd_3575072 1223820206953827832039033 := by
  unfold tailWord_3575072
  simp only [CollatzResearch.WordTrace]
  refine ⟨65196794052066096266227735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86929058736088128354970313 65196794052066096266227735)
  ·
    refine ⟨97795191078099144399341603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65196794052066096266227735 97795191078099144399341603)
    ·
      refine ⟨146692786617148716599012405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97795191078099144399341603 146692786617148716599012405)
      ·
        refine ⟨13752448745357692181157413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146692786617148716599012405 13752448745357692181157413)
        ·
          refine ⟨2578584139754567283967015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13752448745357692181157413 2578584139754567283967015)
          ·
            refine ⟨3867876209631850925950523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578584139754567283967015 3867876209631850925950523)
            ·
              refine ⟨5801814314447776388925785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867876209631850925950523 5801814314447776388925785)
              ·
                refine ⟨4351360735835832291694339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5801814314447776388925785 4351360735835832291694339)
                ·
                  refine ⟨6527041103753748437541509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351360735835832291694339 6527041103753748437541509)
                  ·
                    refine ⟨1223820206953827832039033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527041103753748437541509 1223820206953827832039033)
                    ·
                      rfl

theorem cell22_3575072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_3575072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575072 prefixEnd_3575072 := by exact prefixLift 3575072
  have htrace : WordTrace (prefixWord ++ tailWord_3575072) baseStart_3575072 baseEnd_3575072 := by
    simpa [prefixWord, tailWord_3575072, baseEnd_3575072] using wordTrace_append hprefix tailTrace_3575072
  have hstable : (prefixWord ++ tailWord_3575072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575072).length < 2 ^ (prefixWord ++ tailWord_3575072).sum := by decide
  have hdescent : baseEnd_3575072 < baseStart_3575072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575085 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3575085 : Nat := 118140960795 + 3575085 * 2 ^ 59
def prefixEnd_3575085 : Nat := 4983230072969 + 3 ^ 40 * 3575085 * 2
def baseEnd_3575085 : Nat := 1223824657119500131463993

theorem tailTrace_3575085 : CollatzResearch.WordTrace tailWord_3575085 prefixEnd_3575085 1223824657119500131463993 := by
  unfold tailWord_3575085
  simp only [CollatzResearch.WordTrace]
  refine ⟨130394062253085095752678709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86929374835390063835119139 130394062253085095752678709)
  ·
    refine ⟨12224443336226727726813629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130394062253085095752678709 12224443336226727726813629)
    ·
      refine ⟨4584166251085022897555111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12224443336226727726813629 4584166251085022897555111)
      ·
        refine ⟨6876249376627534346332667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584166251085022897555111 6876249376627534346332667)
        ·
          refine ⟨10314374064941301519499001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876249376627534346332667 10314374064941301519499001)
          ·
            refine ⟨7735780548705976139624251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10314374064941301519499001 7735780548705976139624251)
            ·
              refine ⟨11603670823058964209436377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7735780548705976139624251 11603670823058964209436377)
              ·
                refine ⟨8702753117294223157077283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11603670823058964209436377 8702753117294223157077283)
                ·
                  refine ⟨13054129675941334735615925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8702753117294223157077283 13054129675941334735615925)
                  ·
                    refine ⟨1223824657119500131463993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13054129675941334735615925 1223824657119500131463993)
                    ·
                      rfl

theorem cell22_3575085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3575085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575085 prefixEnd_3575085 := by exact prefixLift 3575085
  have htrace : WordTrace (prefixWord ++ tailWord_3575085) baseStart_3575085 baseEnd_3575085 := by
    simpa [prefixWord, tailWord_3575085, baseEnd_3575085] using wordTrace_append hprefix tailTrace_3575085
  have hstable : (prefixWord ++ tailWord_3575085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575085).length < 2 ^ (prefixWord ++ tailWord_3575085).sum := by decide
  have hdescent : baseEnd_3575085 < baseStart_3575085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575111 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3575111 : Nat := 118140960795 + 3575111 * 2 ^ 59
def prefixEnd_3575111 : Nat := 4983230072969 + 3 ^ 40 * 3575111 * 2
def baseEnd_3575111 : Nat := 1223833557450844730313913

theorem tailTrace_3575111 : CollatzResearch.WordTrace tailWord_3575111 prefixEnd_3575111 1223833557450844730313913 := by
  unfold tailWord_3575111
  simp only [CollatzResearch.WordTrace]
  refine ⟨130395010550990902193125187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86930007033993934795416791 130395010550990902193125187)
  ·
    refine ⟨195592515826486353289687781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130395010550990902193125187 195592515826486353289687781)
    ·
      refine ⟨36673596717466191241816459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195592515826486353289687781 36673596717466191241816459)
      ·
        refine ⟨55010395076199286862724689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36673596717466191241816459 55010395076199286862724689)
        ·
          refine ⟨41257796307149465147043517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55010395076199286862724689 41257796307149465147043517)
          ·
            refine ⟨15471673615181049430141319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41257796307149465147043517 15471673615181049430141319)
            ·
              refine ⟨23207510422771574145211979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15471673615181049430141319 23207510422771574145211979)
              ·
                refine ⟨34811265634157361217817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23207510422771574145211979 34811265634157361217817969)
                ·
                  refine ⟨26108449225618020913363477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34811265634157361217817969 26108449225618020913363477)
                  ·
                    refine ⟨1223833557450844730313913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26108449225618020913363477 1223833557450844730313913)
                    ·
                      rfl

theorem cell22_3575111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3575111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575111 prefixEnd_3575111 := by exact prefixLift 3575111
  have htrace : WordTrace (prefixWord ++ tailWord_3575111) baseStart_3575111 baseEnd_3575111 := by
    simpa [prefixWord, tailWord_3575111, baseEnd_3575111] using wordTrace_append hprefix tailTrace_3575111
  have hstable : (prefixWord ++ tailWord_3575111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575111).length < 2 ^ (prefixWord ++ tailWord_3575111).sum := by decide
  have hdescent : baseEnd_3575111 < baseStart_3575111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575141 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3575141 : Nat := 118140960795 + 3575141 * 2 ^ 59
def prefixEnd_3575141 : Nat := 4983230072969 + 3 ^ 40 * 3575141 * 2
def baseEnd_3575141 : Nat := 1223843827063934652063821

theorem tailTrace_3575141 : CollatzResearch.WordTrace tailWord_3575141 prefixEnd_3575141 1223843827063934652063821 := by
  unfold tailWord_3575141
  simp only [CollatzResearch.WordTrace]
  refine ⟨130396104740882217316717277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86930736493921478211144851 130396104740882217316717277)
  ·
    refine ⟨48898539277830831493768979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130396104740882217316717277 48898539277830831493768979)
    ·
      refine ⟨73347808916746247240653469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48898539277830831493768979 73347808916746247240653469)
      ·
        refine ⟨27505428343779842715245051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73347808916746247240653469 27505428343779842715245051)
        ·
          refine ⟨41258142515669764072867577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27505428343779842715245051 41258142515669764072867577)
          ·
            refine ⟨30943606886752323054650683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41258142515669764072867577 30943606886752323054650683)
            ·
              refine ⟨46415410330128484581976025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30943606886752323054650683 46415410330128484581976025)
              ·
                refine ⟨34811557747596363436482019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46415410330128484581976025 34811557747596363436482019)
                ·
                  refine ⟨52217336621394545154723029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34811557747596363436482019 52217336621394545154723029)
                  ·
                    refine ⟨1223843827063934652063821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52217336621394545154723029 1223843827063934652063821)
                    ·
                      rfl

theorem cell22_3575141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3575141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575141 prefixEnd_3575141 := by exact prefixLift 3575141
  have htrace : WordTrace (prefixWord ++ tailWord_3575141) baseStart_3575141 baseEnd_3575141 := by
    simpa [prefixWord, tailWord_3575141, baseEnd_3575141] using wordTrace_append hprefix tailTrace_3575141
  have hstable : (prefixWord ++ tailWord_3575141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575141).length < 2 ^ (prefixWord ++ tailWord_3575141).sum := by decide
  have hdescent : baseEnd_3575141 < baseStart_3575141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575198 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3575198 : Nat := 118140960795 + 3575198 * 2 ^ 59
def prefixEnd_3575198 : Nat := 4983230072969 + 3 ^ 40 * 3575198 * 2
def baseEnd_3575198 : Nat := 1223863339328805503388647

theorem tailTrace_3575198 : CollatzResearch.WordTrace tailWord_3575198 prefixEnd_3575198 1223863339328805503388647 := by
  unfold tailWord_3575198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299772962709464506442781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86932122467783810701028165 16299772962709464506442781)
  ·
    refine ⟨6112414861016049189916043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16299772962709464506442781 6112414861016049189916043)
    ·
      refine ⟨9168622291524073784874065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6112414861016049189916043 9168622291524073784874065)
      ·
        refine ⟨6876466718643055338655549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9168622291524073784874065 6876466718643055338655549)
        ·
          refine ⟨2578675019491145751995831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6876466718643055338655549 2578675019491145751995831)
          ·
            refine ⟨3868012529236718627993747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578675019491145751995831 3868012529236718627993747)
            ·
              refine ⟨5802018793855077941990621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868012529236718627993747 5802018793855077941990621)
              ·
                refine ⟨2175757047695654228246483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5802018793855077941990621 2175757047695654228246483)
                ·
                  refine ⟨3263635571543481342369725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175757047695654228246483 3263635571543481342369725)
                  ·
                    refine ⟨1223863339328805503388647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263635571543481342369725 1223863339328805503388647)
                    ·
                      rfl

theorem cell22_3575198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3575198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575198 prefixEnd_3575198 := by exact prefixLift 3575198
  have htrace : WordTrace (prefixWord ++ tailWord_3575198) baseStart_3575198 baseEnd_3575198 := by
    simpa [prefixWord, tailWord_3575198, baseEnd_3575198] using wordTrace_append hprefix tailTrace_3575198
  have hstable : (prefixWord ++ tailWord_3575198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575198).length < 2 ^ (prefixWord ++ tailWord_3575198).sum := by decide
  have hdescent : baseEnd_3575198 < baseStart_3575198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575203 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 6, 3]
def baseStart_3575203 : Nat := 118140960795 + 3575203 * 2 ^ 59
def prefixEnd_3575203 : Nat := 4983230072969 + 3 ^ 40 * 3575203 * 2
def baseEnd_3575203 : Nat := 1223865050930987157013631

theorem tailTrace_3575203 : CollatzResearch.WordTrace tailWord_3575203 prefixEnd_3575203 1223865050930987157013631 := by
  unfold tailWord_3575203
  simp only [CollatzResearch.WordTrace]
  refine ⟨130398366066657601905474263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86932244044438401270316175 130398366066657601905474263)
  ·
    refine ⟨195597549099986402858211395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130398366066657601905474263 195597549099986402858211395)
    ·
      refine ⟨293396323649979604287317093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195597549099986402858211395 293396323649979604287317093)
      ·
        refine ⟨55011810684371175803871955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293396323649979604287317093 55011810684371175803871955)
        ·
          refine ⟨82517716026556763705807933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55011810684371175803871955 82517716026556763705807933)
          ·
            refine ⟨30944143509958786389677975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82517716026556763705807933 30944143509958786389677975)
            ·
              refine ⟨46416215264938179584516963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30944143509958786389677975 46416215264938179584516963)
              ·
                refine ⟨69624322897407269376775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46416215264938179584516963 69624322897407269376775445)
                ·
                  refine ⟨3263640135815965752036349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69624322897407269376775445 3263640135815965752036349)
                  ·
                    refine ⟨1223865050930987157013631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263640135815965752036349 1223865050930987157013631)
                    ·
                      rfl

theorem cell22_3575203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 3].length) (baseStart_3575203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575203 prefixEnd_3575203 := by exact prefixLift 3575203
  have htrace : WordTrace (prefixWord ++ tailWord_3575203) baseStart_3575203 baseEnd_3575203 := by
    simpa [prefixWord, tailWord_3575203, baseEnd_3575203] using wordTrace_append hprefix tailTrace_3575203
  have hstable : (prefixWord ++ tailWord_3575203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575203).length < 2 ^ (prefixWord ++ tailWord_3575203).sum := by decide
  have hdescent : baseEnd_3575203 < baseStart_3575203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575252 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3575252 : Nat := 118140960795 + 3575252 * 2 ^ 59
def prefixEnd_3575252 : Nat := 4983230072969 + 3 ^ 40 * 3575252 * 2
def baseEnd_3575252 : Nat := 1223881824632367362538481

theorem tailTrace_3575252 : CollatzResearch.WordTrace tailWord_3575252 prefixEnd_3575252 1223881824632367362538481 := by
  unfold tailWord_3575252
  simp only [CollatzResearch.WordTrace]
  refine ⟨65200076621740041637004005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86933435495653388849338673 65200076621740041637004005)
  ·
    refine ⟨12225014366576257806938251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65200076621740041637004005 12225014366576257806938251)
    ·
      refine ⟨18337521549864386710407377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225014366576257806938251 18337521549864386710407377)
      ·
        refine ⟨13753141162398290032805533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18337521549864386710407377 13753141162398290032805533)
        ·
          refine ⟨5157427935899358762302075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13753141162398290032805533 5157427935899358762302075)
          ·
            refine ⟨7736141903849038143453113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157427935899358762302075 7736141903849038143453113)
            ·
              refine ⟨5802106427886778607589835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7736141903849038143453113 5802106427886778607589835)
              ·
                refine ⟨8703159641830167911384753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802106427886778607589835 8703159641830167911384753)
                ·
                  refine ⟨6527369731372625933538565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703159641830167911384753 6527369731372625933538565)
                  ·
                    refine ⟨1223881824632367362538481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527369731372625933538565 1223881824632367362538481)
                    ·
                      rfl

theorem cell22_3575252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3575252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575252 prefixEnd_3575252 := by exact prefixLift 3575252
  have htrace : WordTrace (prefixWord ++ tailWord_3575252) baseStart_3575252 baseEnd_3575252 := by
    simpa [prefixWord, tailWord_3575252, baseEnd_3575252] using wordTrace_append hprefix tailTrace_3575252
  have hstable : (prefixWord ++ tailWord_3575252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575252).length < 2 ^ (prefixWord ++ tailWord_3575252).sum := by decide
  have hdescent : baseEnd_3575252 < baseStart_3575252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575293 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3575293 : Nat := 118140960795 + 3575293 * 2 ^ 59
def prefixEnd_3575293 : Nat := 4983230072969 + 3 ^ 40 * 3575293 * 2
def baseEnd_3575293 : Nat := 1223895859770256922263355

theorem tailTrace_3575293 : CollatzResearch.WordTrace tailWord_3575293 prefixEnd_3575293 1223895859770256922263355 := by
  unfold tailWord_3575293
  simp only [CollatzResearch.WordTrace]
  refine ⟨130401648636331547276250533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86934432424221031517500355 130401648636331547276250533)
  ·
    refine ⟨24450309119312165114296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130401648636331547276250533 24450309119312165114296975)
    ·
      refine ⟨36675463678968247671445463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24450309119312165114296975 36675463678968247671445463)
      ·
        refine ⟨55013195518452371507168195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36675463678968247671445463 55013195518452371507168195)
        ·
          refine ⟨82519793277678557260752293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55013195518452371507168195 82519793277678557260752293)
          ·
            refine ⟨15472461239564729486391055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82519793277678557260752293 15472461239564729486391055)
            ·
              refine ⟨23208691859347094229586583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15472461239564729486391055 23208691859347094229586583)
              ·
                refine ⟨34813037789020641344379875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23208691859347094229586583 34813037789020641344379875)
                ·
                  refine ⟨52219556683530962016569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34813037789020641344379875 52219556683530962016569813)
                  ·
                    refine ⟨1223895859770256922263355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52219556683530962016569813 1223895859770256922263355)
                    ·
                      rfl

theorem cell22_3575293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3575293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575293 prefixEnd_3575293 := by exact prefixLift 3575293
  have htrace : WordTrace (prefixWord ++ tailWord_3575293) baseStart_3575293 baseEnd_3575293 := by
    simpa [prefixWord, tailWord_3575293, baseEnd_3575293] using wordTrace_append hprefix tailTrace_3575293
  have hstable : (prefixWord ++ tailWord_3575293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575293).length < 2 ^ (prefixWord ++ tailWord_3575293).sum := by decide
  have hdescent : baseEnd_3575293 < baseStart_3575293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575370 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3575370 : Nat := 118140960795 + 3575370 * 2 ^ 59
def prefixEnd_3575370 : Nat := 4983230072969 + 3 ^ 40 * 3575370 * 2
def baseEnd_3575370 : Nat := 1223922218443854388088119

theorem tailTrace_3575370 : CollatzResearch.WordTrace tailWord_3575370 prefixEnd_3575370 1223922218443854388088119 := by
  unfold tailWord_3575370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601114264263147356700891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86936304704701726284535709 32601114264263147356700891)
  ·
    refine ⟨48901671396394721035051337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32601114264263147356700891 48901671396394721035051337)
    ·
      refine ⟨36676253547296040776288503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48901671396394721035051337 36676253547296040776288503)
      ·
        refine ⟨55014380320944061164432755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36676253547296040776288503 55014380320944061164432755)
        ·
          refine ⟨82521570481416091746649133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55014380320944061164432755 82521570481416091746649133)
          ·
            refine ⟨30945588930531034404993425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82521570481416091746649133 30945588930531034404993425)
            ·
              refine ⟨23209191697898275803745069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30945588930531034404993425 23209191697898275803745069)
              ·
                refine ⟨8703446886711853426404401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23209191697898275803745069 8703446886711853426404401)
                ·
                  refine ⟨6527585165033890069803301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8703446886711853426404401 6527585165033890069803301)
                  ·
                    refine ⟨1223922218443854388088119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6527585165033890069803301 1223922218443854388088119)
                    ·
                      rfl

theorem cell22_3575370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3575370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575370 prefixEnd_3575370 := by exact prefixLift 3575370
  have htrace : WordTrace (prefixWord ++ tailWord_3575370) baseStart_3575370 baseEnd_3575370 := by
    simpa [prefixWord, tailWord_3575370, baseEnd_3575370] using wordTrace_append hprefix tailTrace_3575370
  have hstable : (prefixWord ++ tailWord_3575370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575370).length < 2 ^ (prefixWord ++ tailWord_3575370).sum := by decide
  have hdescent : baseEnd_3575370 < baseStart_3575370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575447 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 5]
def baseStart_3575447 : Nat := 118140960795 + 3575447 * 2 ^ 59
def prefixEnd_3575447 : Nat := 4983230072969 + 3 ^ 40 * 3575447 * 2
def baseEnd_3575447 : Nat := 407982859039150617970961

theorem tailTrace_3575447 : CollatzResearch.WordTrace tailWord_3575447 prefixEnd_3575447 407982859039150617970961 := by
  unfold tailWord_3575447
  simp only [CollatzResearch.WordTrace]
  refine ⟨130407265477773631577356595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86938176985182421051571063 130407265477773631577356595)
  ·
    refine ⟨195610898216660447366034893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130407265477773631577356595 195610898216660447366034893)
    ·
      refine ⟨73354086831247667762263085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195610898216660447366034893 73354086831247667762263085)
      ·
        refine ⟨27507782561717875410848657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73354086831247667762263085 27507782561717875410848657)
        ·
          refine ⟨20630836921288406558136493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27507782561717875410848657 20630836921288406558136493)
          ·
            refine ⟨7736563845483152459301185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20630836921288406558136493 7736563845483152459301185)
            ·
              refine ⟨5802422884112364344475889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7736563845483152459301185 5802422884112364344475889)
              ·
                refine ⟨4351817163084273258356917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5802422884112364344475889 4351817163084273258356917)
                ·
                  refine ⟨407982859039150617970961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4351817163084273258356917 407982859039150617970961)
                  ·
                    rfl

theorem cell22_3575447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 5].length) (baseStart_3575447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575447 prefixEnd_3575447 := by exact prefixLift 3575447
  have htrace : WordTrace (prefixWord ++ tailWord_3575447) baseStart_3575447 baseEnd_3575447 := by
    simpa [prefixWord, tailWord_3575447, baseEnd_3575447] using wordTrace_append hprefix tailTrace_3575447
  have hstable : (prefixWord ++ tailWord_3575447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575447).length < 2 ^ (prefixWord ++ tailWord_3575447).sum := by decide
  have hdescent : baseEnd_3575447 < baseStart_3575447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575475 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 6]
def baseStart_3575475 : Nat := 118140960795 + 3575475 * 2 ^ 59
def prefixEnd_3575475 : Nat := 4983230072969 + 3 ^ 40 * 3575475 * 2
def baseEnd_3575475 : Nat := 407986054029889704737599

theorem tailTrace_3575475 : CollatzResearch.WordTrace tailWord_3575475 prefixEnd_3575475 407986054029889704737599 := by
  unfold tailWord_3575475
  simp only [CollatzResearch.WordTrace]
  refine ⟨130408286721672192359375879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86938857814448128239583919 130408286721672192359375879)
  ·
    refine ⟨195612430082508288539063819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130408286721672192359375879 195612430082508288539063819)
    ·
      refine ⟨293418645123762432808595729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195612430082508288539063819 293418645123762432808595729)
      ·
        refine ⟨220063983842821824606446797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293418645123762432808595729 220063983842821824606446797)
        ·
          refine ⟨82523993941058184227417549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220063983842821824606446797 82523993941058184227417549)
          ·
            refine ⟨30946497727896819085281581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82523993941058184227417549 30946497727896819085281581)
            ·
              refine ⟨11604936647961307156980593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30946497727896819085281581 11604936647961307156980593)
              ·
                refine ⟨8703702485970980367735445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11604936647961307156980593 8703702485970980367735445)
                ·
                  refine ⟨407986054029889704737599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8703702485970980367735445 407986054029889704737599)
                  ·
                    rfl

theorem cell22_3575475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 6].length) (baseStart_3575475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575475 prefixEnd_3575475 := by exact prefixLift 3575475
  have htrace : WordTrace (prefixWord ++ tailWord_3575475) baseStart_3575475 baseEnd_3575475 := by
    simpa [prefixWord, tailWord_3575475, baseEnd_3575475] using wordTrace_append hprefix tailTrace_3575475
  have hstable : (prefixWord ++ tailWord_3575475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575475).length < 2 ^ (prefixWord ++ tailWord_3575475).sum := by decide
  have hdescent : baseEnd_3575475 < baseStart_3575475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575535 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3575535 : Nat := 118140960795 + 3575535 * 2 ^ 59
def prefixEnd_3575535 : Nat := 4983230072969 + 3 ^ 40 * 3575535 * 2
def baseEnd_3575535 : Nat := 1223978701315848957712613

theorem tailTrace_3575535 : CollatzResearch.WordTrace tailWord_3575535 prefixEnd_3575535 1223978701315848957712613 := by
  unfold tailWord_3575535
  simp only [CollatzResearch.WordTrace]
  refine ⟨130410475101454822606560059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86940316734303215071040039 130410475101454822606560059)
  ·
    refine ⟨195615712652182233909840089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130410475101454822606560059 195615712652182233909840089)
    ·
      refine ⟨146711784489136675432380067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195615712652182233909840089 146711784489136675432380067)
      ·
        refine ⟨220067676733705013148570101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146711784489136675432380067 220067676733705013148570101)
        ·
          refine ⟨20631344693784844982678447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220067676733705013148570101 20631344693784844982678447)
          ·
            refine ⟨30947017040677267474017671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20631344693784844982678447 30947017040677267474017671)
            ·
              refine ⟨46420525561015901211026507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30947017040677267474017671 46420525561015901211026507)
              ·
                refine ⟨69630788341523851816539761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46420525561015901211026507 69630788341523851816539761)
                ·
                  refine ⟨52223091256142888862404821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69630788341523851816539761 52223091256142888862404821)
                  ·
                    refine ⟨1223978701315848957712613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52223091256142888862404821 1223978701315848957712613)
                    ·
                      rfl

theorem cell22_3575535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3575535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575535 prefixEnd_3575535 := by exact prefixLift 3575535
  have htrace : WordTrace (prefixWord ++ tailWord_3575535) baseStart_3575535 baseEnd_3575535 := by
    simpa [prefixWord, tailWord_3575535, baseEnd_3575535] using wordTrace_append hprefix tailTrace_3575535
  have hstable : (prefixWord ++ tailWord_3575535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575535).length < 2 ^ (prefixWord ++ tailWord_3575535).sum := by decide
  have hdescent : baseEnd_3575535 < baseStart_3575535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575537 : List Nat := [1, 2, 2, 2, 2, 3, 4, 6]
def baseStart_3575537 : Nat := 118140960795 + 3575537 * 2 ^ 59
def prefixEnd_3575537 : Nat := 4983230072969 + 3 ^ 40 * 3575537 * 2
def baseEnd_3575537 : Nat := 135997709550746846573623

theorem tailTrace_3575537 : CollatzResearch.WordTrace tailWord_3575537 prefixEnd_3575537 135997709550746846573623 := by
  unfold tailWord_3575537
  simp only [CollatzResearch.WordTrace]
  refine ⟨130410548047447576948132865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86940365364965051298755243 130410548047447576948132865)
  ·
    refine ⟨97807911035585682711099649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130410548047447576948132865 97807911035585682711099649)
    ·
      refine ⟨73355933276689262033324737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97807911035585682711099649 73355933276689262033324737)
      ·
        refine ⟨55016949957516946524993553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73355933276689262033324737 55016949957516946524993553)
        ·
          refine ⟨41262712468137709893745165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55016949957516946524993553 41262712468137709893745165)
          ·
            refine ⟨15473517175551641210154437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41262712468137709893745165 15473517175551641210154437)
            ·
              refine ⟨2901284470415932726903957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15473517175551641210154437 2901284470415932726903957)
              ·
                refine ⟨135997709550746846573623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2901284470415932726903957 135997709550746846573623)
                ·
                  rfl

theorem cell22_3575537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 6].length) (baseStart_3575537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575537 prefixEnd_3575537 := by exact prefixLift 3575537
  have htrace : WordTrace (prefixWord ++ tailWord_3575537) baseStart_3575537 baseEnd_3575537 := by
    simpa [prefixWord, tailWord_3575537, baseEnd_3575537] using wordTrace_append hprefix tailTrace_3575537
  have hstable : (prefixWord ++ tailWord_3575537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575537).length < 2 ^ (prefixWord ++ tailWord_3575537).sum := by decide
  have hdescent : baseEnd_3575537 < baseStart_3575537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575678 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3575678 : Nat := 118140960795 + 3575678 * 2 ^ 59
def prefixEnd_3575678 : Nat := 4983230072969 + 3 ^ 40 * 3575678 * 2
def baseEnd_3575678 : Nat := 408009217712748083795725

theorem tailTrace_3575678 : CollatzResearch.WordTrace tailWord_3575678 prefixEnd_3575678 408009217712748083795725 := by
  unfold tailWord_3575678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301961342492094753626961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86943793826624505352677125 16301961342492094753626961)
  ·
    refine ⟨12226471006869071065220221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16301961342492094753626961 12226471006869071065220221)
    ·
      refine ⟨4584926627575901649457583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12226471006869071065220221 4584926627575901649457583)
      ·
        refine ⟨6877389941363852474186375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4584926627575901649457583 6877389941363852474186375)
        ·
          refine ⟨10316084912045778711279563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6877389941363852474186375 10316084912045778711279563)
          ·
            refine ⟨15474127368068668066919345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316084912045778711279563 15474127368068668066919345)
            ·
              refine ⟨11605595526051501050189509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15474127368068668066919345 11605595526051501050189509)
              ·
                refine ⟨2176049161134656446910533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11605595526051501050189509 2176049161134656446910533)
                ·
                  refine ⟨408009217712748083795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176049161134656446910533 408009217712748083795725)
                  ·
                    rfl

theorem cell22_3575678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3575678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575678 prefixEnd_3575678 := by exact prefixLift 3575678
  have htrace : WordTrace (prefixWord ++ tailWord_3575678) baseStart_3575678 baseEnd_3575678 := by
    simpa [prefixWord, tailWord_3575678, baseEnd_3575678] using wordTrace_append hprefix tailTrace_3575678
  have hstable : (prefixWord ++ tailWord_3575678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575678).length < 2 ^ (prefixWord ++ tailWord_3575678).sum := by decide
  have hdescent : baseEnd_3575678 < baseStart_3575678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575706 : List Nat := [3, 1, 1, 4, 2, 3, 2, 6]
def baseStart_3575706 : Nat := 118140960795 + 3575706 * 2 ^ 59
def prefixEnd_3575706 : Nat := 4983230072969 + 3 ^ 40 * 3575706 * 2
def baseEnd_3575706 : Nat := 136004137567829056854121

theorem tailTrace_3575706 : CollatzResearch.WordTrace tailWord_3575706 prefixEnd_3575706 136004137567829056854121 := by
  unfold tailWord_3575706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32604177995958829702758743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86944474655890212540689981 32604177995958829702758743)
  ·
    refine ⟨48906266993938244554138115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32604177995958829702758743 48906266993938244554138115)
    ·
      refine ⟨73359400490907366831207173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48906266993938244554138115 73359400490907366831207173)
      ·
        refine ⟨13754887592045131280851345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73359400490907366831207173 13754887592045131280851345)
        ·
          refine ⟨10316165694033848460638509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13754887592045131280851345 10316165694033848460638509)
          ·
            refine ⟨3868562135262693172739441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10316165694033848460638509 3868562135262693172739441)
            ·
              refine ⟨2901421601447019879554581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868562135262693172739441 2901421601447019879554581)
              ·
                refine ⟨136004137567829056854121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2901421601447019879554581 136004137567829056854121)
                ·
                  rfl

theorem cell22_3575706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_3575706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575706 prefixEnd_3575706 := by exact prefixLift 3575706
  have htrace : WordTrace (prefixWord ++ tailWord_3575706) baseStart_3575706 baseEnd_3575706 := by
    simpa [prefixWord, tailWord_3575706, baseEnd_3575706] using wordTrace_append hprefix tailTrace_3575706
  have hstable : (prefixWord ++ tailWord_3575706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575706).length < 2 ^ (prefixWord ++ tailWord_3575706).sum := by decide
  have hdescent : baseEnd_3575706 < baseStart_3575706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575721 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_3575721 : Nat := 118140960795 + 3575721 * 2 ^ 59
def prefixEnd_3575721 : Nat := 4983230072969 + 3 ^ 40 * 3575721 * 2
def baseEnd_3575721 : Nat := 1224042372917006472562043

theorem tailTrace_3575721 : CollatzResearch.WordTrace tailWord_3575721 prefixEnd_3575721 1224042372917006472562043 := by
  unfold tailWord_3575721
  simp only [CollatzResearch.WordTrace]
  refine ⟨130417259078780976372831017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86944839385853984248554011 130417259078780976372831017)
  ·
    refine ⟨97812944309085732279623263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130417259078780976372831017 97812944309085732279623263)
    ·
      refine ⟨146719416463628598419434895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97812944309085732279623263 146719416463628598419434895)
      ·
        refine ⟨220079124695442897629152343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146719416463628598419434895 220079124695442897629152343)
        ·
          refine ⟨330118687043164346443728515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220079124695442897629152343 330118687043164346443728515)
          ·
            refine ⟨495178030564746519665592773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330118687043164346443728515 495178030564746519665592773)
            ·
              refine ⟨92845880730889972437298645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495178030564746519665592773 92845880730889972437298645)
              ·
                refine ⟨2176075329630233728999187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92845880730889972437298645 2176075329630233728999187)
                ·
                  refine ⟨3264112994445350593498781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176075329630233728999187 3264112994445350593498781)
                  ·
                    refine ⟨1224042372917006472562043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264112994445350593498781 1224042372917006472562043)
                    ·
                      rfl

theorem cell22_3575721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_3575721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575721 prefixEnd_3575721 := by exact prefixLift 3575721
  have htrace : WordTrace (prefixWord ++ tailWord_3575721) baseStart_3575721 baseEnd_3575721 := by
    simpa [prefixWord, tailWord_3575721, baseEnd_3575721] using wordTrace_append hprefix tailTrace_3575721
  have hstable : (prefixWord ++ tailWord_3575721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575721).length < 2 ^ (prefixWord ++ tailWord_3575721).sum := by decide
  have hdescent : baseEnd_3575721 < baseStart_3575721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575789 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_3575789 : Nat := 118140960795 + 3575789 * 2 ^ 59
def prefixEnd_3575789 : Nat := 4983230072969 + 3 ^ 40 * 3575789 * 2
def baseEnd_3575789 : Nat := 1224065650706676961861835

theorem tailTrace_3575789 : CollatzResearch.WordTrace tailWord_3575789 prefixEnd_3575789 1224065650706676961861835 := by
  unfold tailWord_3575789
  simp only [CollatzResearch.WordTrace]
  refine ⟨130419739242534623986306421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86946492828356415990870947 130419739242534623986306421)
  ·
    refine ⟨12226850553987620998716227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130419739242534623986306421 12226850553987620998716227)
    ·
      refine ⟨18340275830981431498074341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12226850553987620998716227 18340275830981431498074341)
      ·
        refine ⟨3438801718309018405888939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18340275830981431498074341 3438801718309018405888939)
        ·
          refine ⟨5158202577463527608833409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438801718309018405888939 5158202577463527608833409)
          ·
            refine ⟨3868651933097645706625057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158202577463527608833409 3868651933097645706625057)
            ·
              refine ⟨2901488949823234279968793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868651933097645706625057 2901488949823234279968793)
              ·
                refine ⟨2176116712367425709976595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901488949823234279968793 2176116712367425709976595)
                ·
                  refine ⟨3264175068551138564964893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176116712367425709976595 3264175068551138564964893)
                  ·
                    refine ⟨1224065650706676961861835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264175068551138564964893 1224065650706676961861835)
                    ·
                      rfl

theorem cell22_3575789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_3575789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575789 prefixEnd_3575789 := by exact prefixLift 3575789
  have htrace : WordTrace (prefixWord ++ tailWord_3575789) baseStart_3575789 baseEnd_3575789 := by
    simpa [prefixWord, tailWord_3575789, baseEnd_3575789] using wordTrace_append hprefix tailTrace_3575789
  have hstable : (prefixWord ++ tailWord_3575789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575789).length < 2 ^ (prefixWord ++ tailWord_3575789).sum := by decide
  have hdescent : baseEnd_3575789 < baseStart_3575789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575809 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3575809 : Nat := 118140960795 + 3575809 * 2 ^ 59
def prefixEnd_3575809 : Nat := 4983230072969 + 3 ^ 40 * 3575809 * 2
def baseEnd_3575809 : Nat := 1224072497115403576361773

theorem tailTrace_3575809 : CollatzResearch.WordTrace tailWord_3575809 prefixEnd_3575809 1224072497115403576361773 := by
  unfold tailWord_3575809
  simp only [CollatzResearch.WordTrace]
  refine ⟨130420468702462167402034481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86946979134974778268022987 130420468702462167402034481)
  ·
    refine ⟨97815351526846625551525861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130420468702462167402034481 97815351526846625551525861)
    ·
      refine ⟨18340378411283742290911099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97815351526846625551525861 18340378411283742290911099)
      ·
        refine ⟨27510567616925613436366649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18340378411283742290911099 27510567616925613436366649)
        ·
          refine ⟨20632925712694210077274987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27510567616925613436366649 20632925712694210077274987)
          ·
            refine ⟨30949388569041315115912481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20632925712694210077274987 30949388569041315115912481)
            ·
              refine ⟨23212041426780986336934361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30949388569041315115912481 23212041426780986336934361)
              ·
                refine ⟨17409031070085739752700771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23212041426780986336934361 17409031070085739752700771)
                ·
                  refine ⟨26113546605128609629051157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17409031070085739752700771 26113546605128609629051157)
                  ·
                    refine ⟨1224072497115403576361773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26113546605128609629051157 1224072497115403576361773)
                    ·
                      rfl

theorem cell22_3575809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3575809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575809 prefixEnd_3575809 := by exact prefixLift 3575809
  have htrace : WordTrace (prefixWord ++ tailWord_3575809) baseStart_3575809 baseEnd_3575809 := by
    simpa [prefixWord, tailWord_3575809, baseEnd_3575809] using wordTrace_append hprefix tailTrace_3575809
  have hstable : (prefixWord ++ tailWord_3575809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575809).length < 2 ^ (prefixWord ++ tailWord_3575809).sum := by decide
  have hdescent : baseEnd_3575809 < baseStart_3575809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575856 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_3575856 : Nat := 118140960795 + 3575856 * 2 ^ 59
def prefixEnd_3575856 : Nat := 4983230072969 + 3 ^ 40 * 3575856 * 2
def baseEnd_3575856 : Nat := 1224088586175911120436629

theorem tailTrace_3575856 : CollatzResearch.WordTrace tailWord_3575856 prefixEnd_3575856 1224088586175911120436629 := by
  unfold tailWord_3575856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65211091466645947214497711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86948121955527929619330281 65211091466645947214497711)
  ·
    refine ⟨97816637199968920821746567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65211091466645947214497711 97816637199968920821746567)
    ·
      refine ⟨146724955799953381232619851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97816637199968920821746567 146724955799953381232619851)
      ·
        refine ⟨220087433699930071848929777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146724955799953381232619851 220087433699930071848929777)
        ·
          refine ⟨165065575274947553886697333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220087433699930071848929777 165065575274947553886697333)
          ·
            refine ⟨15474897682026333176877875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165065575274947553886697333 15474897682026333176877875)
            ·
              refine ⟨23212346523039499765316813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15474897682026333176877875 23212346523039499765316813)
              ·
                refine ⟨8704629946139812411993805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23212346523039499765316813 8704629946139812411993805)
                ·
                  refine ⟨3264236229802429654497677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8704629946139812411993805 3264236229802429654497677)
                  ·
                    refine ⟨1224088586175911120436629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264236229802429654497677 1224088586175911120436629)
                    ·
                      rfl

theorem cell22_3575856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_3575856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575856 prefixEnd_3575856 := by exact prefixLift 3575856
  have htrace : WordTrace (prefixWord ++ tailWord_3575856) baseStart_3575856 baseEnd_3575856 := by
    simpa [prefixWord, tailWord_3575856, baseEnd_3575856] using wordTrace_append hprefix tailTrace_3575856
  have hstable : (prefixWord ++ tailWord_3575856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575856).length < 2 ^ (prefixWord ++ tailWord_3575856).sum := by decide
  have hdescent : baseEnd_3575856 < baseStart_3575856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575873 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3575873 : Nat := 118140960795 + 3575873 * 2 ^ 59
def prefixEnd_3575873 : Nat := 4983230072969 + 3 ^ 40 * 3575873 * 2
def baseEnd_3575873 : Nat := 1224094405623328742761577

theorem tailTrace_3575873 : CollatzResearch.WordTrace tailWord_3575873 prefixEnd_3575873 1224094405623328742761577 := by
  unfold tailWord_3575873
  simp only [CollatzResearch.WordTrace]
  refine ⟨130422802974230306332364273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86948535316153537554909515 130422802974230306332364273)
  ·
    refine ⟨97817102230672729749273205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130422802974230306332364273 97817102230672729749273205)
    ·
      refine ⟨9170353334125568413994363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97817102230672729749273205 9170353334125568413994363)
      ·
        refine ⟨13755530001188352620991545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170353334125568413994363 13755530001188352620991545)
        ·
          refine ⟨10316647500891264465743659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13755530001188352620991545 10316647500891264465743659)
          ·
            refine ⟨15474971251336896698615489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10316647500891264465743659 15474971251336896698615489)
            ·
              refine ⟨11606228438502672523961617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15474971251336896698615489 11606228438502672523961617)
              ·
                refine ⟨8704671328877004392971213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11606228438502672523961617 8704671328877004392971213)
                ·
                  refine ⟨3264251748328876647364205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8704671328877004392971213 3264251748328876647364205)
                  ·
                    refine ⟨1224094405623328742761577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264251748328876647364205 1224094405623328742761577)
                    ·
                      rfl

theorem cell22_3575873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3575873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575873 prefixEnd_3575873 := by exact prefixLift 3575873
  have htrace : WordTrace (prefixWord ++ tailWord_3575873) baseStart_3575873 baseEnd_3575873 := by
    simpa [prefixWord, tailWord_3575873, baseEnd_3575873] using wordTrace_append hprefix tailTrace_3575873
  have hstable : (prefixWord ++ tailWord_3575873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575873).length < 2 ^ (prefixWord ++ tailWord_3575873).sum := by decide
  have hdescent : baseEnd_3575873 < baseStart_3575873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575884 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3575884 : Nat := 118140960795 + 3575884 * 2 ^ 59
def prefixEnd_3575884 : Nat := 4983230072969 + 3 ^ 40 * 3575884 * 2
def baseEnd_3575884 : Nat := 1224098171148128380736543

theorem tailTrace_3575884 : CollatzResearch.WordTrace tailWord_3575884 prefixEnd_3575884 1224098171148128380736543 := by
  unfold tailWord_3575884
  simp only [CollatzResearch.WordTrace]
  refine ⟨65211602088595227605507353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86948802784793636807343137 65211602088595227605507353)
  ·
    refine ⟨48908701566446420704130515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65211602088595227605507353 48908701566446420704130515)
    ·
      refine ⟨73363052349669631056195773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48908701566446420704130515 73363052349669631056195773)
      ·
        refine ⟨27511144631126111646073415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73363052349669631056195773 27511144631126111646073415)
        ·
          refine ⟨41266716946689167469110123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27511144631126111646073415 41266716946689167469110123)
          ·
            refine ⟨61900075420033751203665185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41266716946689167469110123 61900075420033751203665185)
            ·
              refine ⟨46425056565025313402748889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61900075420033751203665185 46425056565025313402748889)
              ·
                refine ⟨34818792423768985052061667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46425056565025313402748889 34818792423768985052061667)
                ·
                  refine ⟨52228188635653477578092501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34818792423768985052061667 52228188635653477578092501)
                  ·
                    refine ⟨1224098171148128380736543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52228188635653477578092501 1224098171148128380736543)
                    ·
                      rfl

theorem cell22_3575884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3575884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575884 prefixEnd_3575884 := by exact prefixLift 3575884
  have htrace : WordTrace (prefixWord ++ tailWord_3575884) baseStart_3575884 baseEnd_3575884 := by
    simpa [prefixWord, tailWord_3575884, baseEnd_3575884] using wordTrace_append hprefix tailTrace_3575884
  have hstable : (prefixWord ++ tailWord_3575884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575884).length < 2 ^ (prefixWord ++ tailWord_3575884).sum := by decide
  have hdescent : baseEnd_3575884 < baseStart_3575884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575933 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3575933 : Nat := 118140960795 + 3575933 * 2 ^ 59
def prefixEnd_3575933 : Nat := 4983230072969 + 3 ^ 40 * 3575933 * 2
def baseEnd_3575933 : Nat := 1224114944849508586261393

theorem tailTrace_3575933 : CollatzResearch.WordTrace tailWord_3575933 prefixEnd_3575933 1224114944849508586261393 := by
  unfold tailWord_3575933
  simp only [CollatzResearch.WordTrace]
  refine ⟨130424991354012936579548453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86949994236008624386365635 130424991354012936579548453)
  ·
    refine ⟨24454685878877425608665335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130424991354012936579548453 24454685878877425608665335)
    ·
      refine ⟨36682028818316138412998003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24454685878877425608665335 36682028818316138412998003)
      ·
        refine ⟨55023043227474207619497005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36682028818316138412998003 55023043227474207619497005)
        ·
          refine ⟨20633641210302827857311377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55023043227474207619497005 20633641210302827857311377)
          ·
            refine ⟨15475230907727120892983533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20633641210302827857311377 15475230907727120892983533)
            ·
              refine ⟨5803211590397670334868825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15475230907727120892983533 5803211590397670334868825)
              ·
                refine ⟨4352408692798252751151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803211590397670334868825 4352408692798252751151619)
                ·
                  refine ⟨6528613039197379126727429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4352408692798252751151619 6528613039197379126727429)
                  ·
                    refine ⟨1224114944849508586261393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6528613039197379126727429 1224114944849508586261393)
                    ·
                      rfl

theorem cell22_3575933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3575933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575933 prefixEnd_3575933 := by exact prefixLift 3575933
  have htrace : WordTrace (prefixWord ++ tailWord_3575933) baseStart_3575933 baseEnd_3575933 := by
    simpa [prefixWord, tailWord_3575933, baseEnd_3575933] using wordTrace_append hprefix tailTrace_3575933
  have hstable : (prefixWord ++ tailWord_3575933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575933).length < 2 ^ (prefixWord ++ tailWord_3575933).sum := by decide
  have hdescent : baseEnd_3575933 < baseStart_3575933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575946 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3575946 : Nat := 118140960795 + 3575946 * 2 ^ 59
def prefixEnd_3575946 : Nat := 4983230072969 + 3 ^ 40 * 3575946 * 2
def baseEnd_3575946 : Nat := 1224119395015180885686353

theorem tailTrace_3575946 : CollatzResearch.WordTrace tailWord_3575946 prefixEnd_3575946 1224119395015180885686353 := by
  unfold tailWord_3575946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32606366375741459949942923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86950310335310559866514461 32606366375741459949942923)
  ·
    refine ⟨48909549563612189924914385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32606366375741459949942923 48909549563612189924914385)
    ·
      refine ⟨36682162172709142443685789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48909549563612189924914385 36682162172709142443685789)
      ·
        refine ⟨13755810814765928416382171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36682162172709142443685789 13755810814765928416382171)
        ·
          refine ⟨20633716222148892624573257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13755810814765928416382171 20633716222148892624573257)
          ·
            refine ⟨15475287166611669468429943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20633716222148892624573257 15475287166611669468429943)
            ·
              refine ⟨23212930749917504202644915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15475287166611669468429943 23212930749917504202644915)
              ·
                refine ⟨34819396124876256303967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23212930749917504202644915 34819396124876256303967373)
                ·
                  refine ⟨13057273546828596113987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34819396124876256303967373 13057273546828596113987765)
                  ·
                    refine ⟨1224119395015180885686353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13057273546828596113987765 1224119395015180885686353)
                    ·
                      rfl

theorem cell22_3575946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3575946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575946 prefixEnd_3575946 := by exact prefixLift 3575946
  have htrace : WordTrace (prefixWord ++ tailWord_3575946) baseStart_3575946 baseEnd_3575946 := by
    simpa [prefixWord, tailWord_3575946, baseEnd_3575946] using wordTrace_append hprefix tailTrace_3575946
  have hstable : (prefixWord ++ tailWord_3575946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575946).length < 2 ^ (prefixWord ++ tailWord_3575946).sum := by decide
  have hdescent : baseEnd_3575946 < baseStart_3575946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575958 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3575958 : Nat := 118140960795 + 3575958 * 2 ^ 59
def prefixEnd_3575958 : Nat := 4983230072969 + 3 ^ 40 * 3575958 * 2
def baseEnd_3575958 : Nat := 1224123502860416854386317

theorem tailTrace_3575958 : CollatzResearch.WordTrace tailWord_3575958 prefixEnd_3575958 1224123502860416854386317 := by
  unfold tailWord_3575958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151618948682647865575533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86950602119281577232805685 8151618948682647865575533)
  ·
    refine ⟨3056857105755992949590825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8151618948682647865575533 3056857105755992949590825)
    ·
      refine ⟨2292642829316994712193119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3056857105755992949590825 2292642829316994712193119)
      ·
        refine ⟨3438964243975492068289679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292642829316994712193119 3438964243975492068289679)
        ·
          refine ⟨5158446365963238102434519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438964243975492068289679 5158446365963238102434519)
          ·
            refine ⟨7737669548944857153651779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158446365963238102434519 7737669548944857153651779)
            ·
              refine ⟨11606504323417285730477669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737669548944857153651779 11606504323417285730477669)
              ·
                refine ⟨2176219560640741074464563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11606504323417285730477669 2176219560640741074464563)
                ·
                  refine ⟨3264329340961111611696845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176219560640741074464563 3264329340961111611696845)
                  ·
                    refine ⟨1224123502860416854386317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264329340961111611696845 1224123502860416854386317)
                    ·
                      rfl

theorem cell22_3575958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3575958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575958 prefixEnd_3575958 := by exact prefixLift 3575958
  have htrace : WordTrace (prefixWord ++ tailWord_3575958) baseStart_3575958 baseEnd_3575958 := by
    simpa [prefixWord, tailWord_3575958, baseEnd_3575958] using wordTrace_append hprefix tailTrace_3575958
  have hstable : (prefixWord ++ tailWord_3575958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575958).length < 2 ^ (prefixWord ++ tailWord_3575958).sum := by decide
  have hdescent : baseEnd_3575958 < baseStart_3575958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575959 : List Nat := [1, 1, 3, 3, 14]
def baseStart_3575959 : Nat := 118140960795 + 3575959 * 2 ^ 59
def prefixEnd_3575959 : Nat := 4983230072969 + 3 ^ 40 * 3575959 * 2
def baseEnd_3575959 : Nat := 5037546687987050144491

theorem tailTrace_3575959 : CollatzResearch.WordTrace tailWord_3575959 prefixEnd_3575959 5037546687987050144491 := by
  unfold tailWord_3575959
  simp only [CollatzResearch.WordTrace]
  refine ⟨130425939651918743019994931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86950626434612495346663287 130425939651918743019994931)
  ·
    refine ⟨195638909477878114529992397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130425939651918743019994931 195638909477878114529992397)
    ·
      refine ⟨73364591054204292948747149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195638909477878114529992397 73364591054204292948747149)
      ·
        refine ⟨27511721645326609855780181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73364591054204292948747149 27511721645326609855780181)
        ·
          refine ⟨5037546687987050144491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 27511721645326609855780181 5037546687987050144491)
          ·
            rfl

theorem cell22_3575959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 14].length) (baseStart_3575959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575959 prefixEnd_3575959 := by exact prefixLift 3575959
  have htrace : WordTrace (prefixWord ++ tailWord_3575959) baseStart_3575959 baseEnd_3575959 := by
    simpa [prefixWord, tailWord_3575959, baseEnd_3575959] using wordTrace_append hprefix tailTrace_3575959
  have hstable : (prefixWord ++ tailWord_3575959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575959).length < 2 ^ (prefixWord ++ tailWord_3575959).sum := by decide
  have hdescent : baseEnd_3575959 < baseStart_3575959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3575965 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 4]
def baseStart_3575965 : Nat := 118140960795 + 3575965 * 2 ^ 59
def prefixEnd_3575965 : Nat := 4983230072969 + 3 ^ 40 * 3575965 * 2
def baseEnd_3575965 : Nat := 408041966367823723153765

theorem tailTrace_3575965 : CollatzResearch.WordTrace tailWord_3575965 prefixEnd_3575965 408041966367823723153765 := by
  unfold tailWord_3575965
  simp only [CollatzResearch.WordTrace]
  refine ⟨130426158489897006044713349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86950772326598004029808899 130426158489897006044713349)
  ·
    refine ⟨24454904716855688633383753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130426158489897006044713349 24454904716855688633383753)
    ·
      refine ⟨18341178537641766475037815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24454904716855688633383753 18341178537641766475037815)
      ·
        refine ⟨27511767806462649712556723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18341178537641766475037815 27511767806462649712556723)
        ·
          refine ⟨41267651709693974568835085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27511767806462649712556723 41267651709693974568835085)
          ·
            refine ⟨15475369391135240463313157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41267651709693974568835085 15475369391135240463313157)
            ·
              refine ⟨2901631760837857586871217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15475369391135240463313157 2901631760837857586871217)
              ·
                refine ⟨2176223820628393190153413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901631760837857586871217 2176223820628393190153413)
                ·
                  refine ⟨408041966367823723153765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176223820628393190153413 408041966367823723153765)
                  ·
                    rfl

theorem cell22_3575965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_3575965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3575965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3575965 prefixEnd_3575965 := by exact prefixLift 3575965
  have htrace : WordTrace (prefixWord ++ tailWord_3575965) baseStart_3575965 baseEnd_3575965 := by
    simpa [prefixWord, tailWord_3575965, baseEnd_3575965] using wordTrace_append hprefix tailTrace_3575965
  have hstable : (prefixWord ++ tailWord_3575965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3575965).length < 2 ^ (prefixWord ++ tailWord_3575965).sum := by decide
  have hdescent : baseEnd_3575965 < baseStart_3575965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3575965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576025 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_3576025 : Nat := 118140960795 + 3576025 * 2 ^ 59
def prefixEnd_3576025 : Nat := 4983230072969 + 3 ^ 40 * 3576025 * 2
def baseEnd_3576025 : Nat := 1224146438329651012961111

theorem tailTrace_3576025 : CollatzResearch.WordTrace tailWord_3576025 prefixEnd_3576025 1224146438329651012961111 := by
  unfold tailWord_3576025
  simp only [CollatzResearch.WordTrace]
  refine ⟨130428346869679636291897529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86952231246453090861265019 130428346869679636291897529)
  ·
    refine ⟨97821260152259727218923147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130428346869679636291897529 97821260152259727218923147)
    ·
      refine ⟨146731890228389590828384721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97821260152259727218923147 146731890228389590828384721)
      ·
        refine ⟨110048917671292193121288541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146731890228389590828384721 110048917671292193121288541)
        ·
          refine ⟨41268344126734572420483203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110048917671292193121288541 41268344126734572420483203)
          ·
            refine ⟨61902516190101858630724805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41268344126734572420483203 61902516190101858630724805)
            ·
              refine ⟨11606721785644098493260901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61902516190101858630724805 11606721785644098493260901)
              ·
                refine ⟨2176260334808268467486419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11606721785644098493260901 2176260334808268467486419)
                ·
                  refine ⟨3264390502212402701229629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176260334808268467486419 3264390502212402701229629)
                  ·
                    refine ⟨1224146438329651012961111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264390502212402701229629 1224146438329651012961111)
                    ·
                      rfl

theorem cell22_3576025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_3576025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576025 prefixEnd_3576025 := by exact prefixLift 3576025
  have htrace : WordTrace (prefixWord ++ tailWord_3576025) baseStart_3576025 baseEnd_3576025 := by
    simpa [prefixWord, tailWord_3576025, baseEnd_3576025] using wordTrace_append hprefix tailTrace_3576025
  have hstable : (prefixWord ++ tailWord_3576025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576025).length < 2 ^ (prefixWord ++ tailWord_3576025).sum := by decide
  have hdescent : baseEnd_3576025 < baseStart_3576025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576083 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 4]
def baseStart_3576083 : Nat := 118140960795 + 3576083 * 2 ^ 59
def prefixEnd_3576083 : Nat := 4983230072969 + 3 ^ 40 * 3576083 * 2
def baseEnd_3576083 : Nat := 408055430971652731670311

theorem tailTrace_3576083 : CollatzResearch.WordTrace tailWord_3576083 prefixEnd_3576083 408055430971652731670311 := by
  unfold tailWord_3576083
  simp only [CollatzResearch.WordTrace]
  refine ⟨130430462303469512197508903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86953641535646341465005935 130430462303469512197508903)
  ·
    refine ⟨195645693455204268296263355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130430462303469512197508903 195645693455204268296263355)
    ·
      refine ⟨293468540182806402444395033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195645693455204268296263355 293468540182806402444395033)
      ·
        refine ⟨220101405137104801833296275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293468540182806402444395033 220101405137104801833296275)
        ·
          refine ⟨330152107705657202749944413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220101405137104801833296275 330152107705657202749944413)
          ·
            refine ⟨123807040389621451031229155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330152107705657202749944413 123807040389621451031229155)
            ·
              refine ⟨185710560584432176546843733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123807040389621451031229155 185710560584432176546843733)
              ·
                refine ⟨2176295631848814568908325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 185710560584432176546843733 2176295631848814568908325)
                ·
                  refine ⟨408055430971652731670311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176295631848814568908325 408055430971652731670311)
                  ·
                    rfl

theorem cell22_3576083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 4].length) (baseStart_3576083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576083 prefixEnd_3576083 := by exact prefixLift 3576083
  have htrace : WordTrace (prefixWord ++ tailWord_3576083) baseStart_3576083 baseEnd_3576083 := by
    simpa [prefixWord, tailWord_3576083, baseEnd_3576083] using wordTrace_append hprefix tailTrace_3576083
  have hstable : (prefixWord ++ tailWord_3576083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576083).length < 2 ^ (prefixWord ++ tailWord_3576083).sum := by decide
  have hdescent : baseEnd_3576083 < baseStart_3576083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576111 : List Nat := [1, 1, 2, 1, 2, 1, 6, 8]
def baseStart_3576111 : Nat := 118140960795 + 3576111 * 2 ^ 59
def prefixEnd_3576111 : Nat := 4983230072969 + 3 ^ 40 * 3576111 * 2
def baseEnd_3576111 : Nat := 136019541987463939478983

theorem tailTrace_3576111 : CollatzResearch.WordTrace tailWord_3576111 prefixEnd_3576111 136019541987463939478983 := by
  unfold tailWord_3576111
  simp only [CollatzResearch.WordTrace]
  refine ⟨130431483547368072979528187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86954322364912048653018791 130431483547368072979528187)
  ·
    refine ⟨195647225321052109469292281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130431483547368072979528187 195647225321052109469292281)
    ·
      refine ⟨146735418990789082101969211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195647225321052109469292281 146735418990789082101969211)
      ·
        refine ⟨220103128486183623152953817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146735418990789082101969211 220103128486183623152953817)
        ·
          refine ⟨165077346364637717364715363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220103128486183623152953817 165077346364637717364715363)
          ·
            refine ⟨247616019546956576047073045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165077346364637717364715363 247616019546956576047073045)
            ·
              refine ⟨11607000916263589502206549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247616019546956576047073045 11607000916263589502206549)
              ·
                refine ⟨136019541987463939478983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11607000916263589502206549 136019541987463939478983)
                ·
                  rfl

theorem cell22_3576111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 8].length) (baseStart_3576111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576111 prefixEnd_3576111 := by exact prefixLift 3576111
  have htrace : WordTrace (prefixWord ++ tailWord_3576111) baseStart_3576111 baseEnd_3576111 := by
    simpa [prefixWord, tailWord_3576111, baseEnd_3576111] using wordTrace_append hprefix tailTrace_3576111
  have hstable : (prefixWord ++ tailWord_3576111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576111).length < 2 ^ (prefixWord ++ tailWord_3576111).sum := by decide
  have hdescent : baseEnd_3576111 < baseStart_3576111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576173 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3576173 : Nat := 118140960795 + 3576173 * 2 ^ 59
def prefixEnd_3576173 : Nat := 4983230072969 + 3 ^ 40 * 3576173 * 2
def baseEnd_3576173 : Nat := 408065700584742653420219

theorem tailTrace_3576173 : CollatzResearch.WordTrace tailWord_3576173 prefixEnd_3576173 408065700584742653420219 := by
  unfold tailWord_3576173
  simp only [CollatzResearch.WordTrace]
  refine ⟨130433744873143457568285173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86955829915428971712190115 130433744873143457568285173)
  ·
    refine ⟨12228163581857199147026735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130433744873143457568285173 12228163581857199147026735)
    ·
      refine ⟨18342245372785798720540103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228163581857199147026735 18342245372785798720540103)
      ·
        refine ⟨27513368059178698080810155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18342245372785798720540103 27513368059178698080810155)
        ·
          refine ⟨41270052088768047121215233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27513368059178698080810155 41270052088768047121215233)
          ·
            refine ⟨30952539066576035340911425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41270052088768047121215233 30952539066576035340911425)
            ·
              refine ⟨23214404299932026505683569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30952539066576035340911425 23214404299932026505683569)
              ·
                refine ⟨17410803224949019879262677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23214404299932026505683569 17410803224949019879262677)
                ·
                  refine ⟨408065700584742653420219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17410803224949019879262677 408065700584742653420219)
                  ·
                    rfl

theorem cell22_3576173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3576173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576173 prefixEnd_3576173 := by exact prefixLift 3576173
  have htrace : WordTrace (prefixWord ++ tailWord_3576173) baseStart_3576173 baseEnd_3576173 := by
    simpa [prefixWord, tailWord_3576173, baseEnd_3576173] using wordTrace_append hprefix tailTrace_3576173
  have hstable : (prefixWord ++ tailWord_3576173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576173).length < 2 ^ (prefixWord ++ tailWord_3576173).sum := by decide
  have hdescent : baseEnd_3576173 < baseStart_3576173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576233 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_3576233 : Nat := 118140960795 + 3576233 * 2 ^ 59
def prefixEnd_3576233 : Nat := 4983230072969 + 3 ^ 40 * 3576233 * 2
def baseEnd_3576233 : Nat := 1224217640980407803760473

theorem tailTrace_3576233 : CollatzResearch.WordTrace tailWord_3576233 prefixEnd_3576233 1224217640980407803760473 := by
  unfold tailWord_3576233
  simp only [CollatzResearch.WordTrace]
  refine ⟨130435933252926087815469353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86957288835284058543646235 130435933252926087815469353)
  ·
    refine ⟨97826949939694565861602015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130435933252926087815469353 97826949939694565861602015)
    ·
      refine ⟨146740424909541848792403023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97826949939694565861602015 146740424909541848792403023)
      ·
        refine ⟨220110637364312773188604535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146740424909541848792403023 220110637364312773188604535)
        ·
          refine ⟨330165956046469159782906803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220110637364312773188604535 330165956046469159782906803)
          ·
            refine ⟨495248934069703739674360205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330165956046469159782906803 495248934069703739674360205)
            ·
              refine ⟨185718350276138902377885077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 495248934069703739674360205 185718350276138902377885077)
              ·
                refine ⟨8705547669194011048963363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 185718350276138902377885077 8705547669194011048963363)
                ·
                  refine ⟨13058321503791016573445045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8705547669194011048963363 13058321503791016573445045)
                  ·
                    refine ⟨1224217640980407803760473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13058321503791016573445045 1224217640980407803760473)
                    ·
                      rfl

theorem cell22_3576233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_3576233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576233 prefixEnd_3576233 := by exact prefixLift 3576233
  have htrace : WordTrace (prefixWord ++ tailWord_3576233) baseStart_3576233 baseEnd_3576233 := by
    simpa [prefixWord, tailWord_3576233, baseEnd_3576233] using wordTrace_append hprefix tailTrace_3576233
  have hstable : (prefixWord ++ tailWord_3576233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576233).length < 2 ^ (prefixWord ++ tailWord_3576233).sum := by decide
  have hdescent : baseEnd_3576233 < baseStart_3576233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576252 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_3576252 : Nat := 118140960795 + 3576252 * 2 ^ 59
def prefixEnd_3576252 : Nat := 4983230072969 + 3 ^ 40 * 3576252 * 2
def baseEnd_3576252 : Nat := 408074715022899362511805

theorem tailTrace_3576252 : CollatzResearch.WordTrace tailWord_3576252 prefixEnd_3576252 408074715022899362511805 := by
  unfold tailWord_3576252
  simp only [CollatzResearch.WordTrace]
  refine ⟨65218313119928627030205505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86957750826571502706940673 65218313119928627030205505)
  ·
    refine ⟨48913734839946470272654129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65218313119928627030205505 48913734839946470272654129)
    ·
      refine ⟨36685301129959852704490597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48913734839946470272654129 36685301129959852704490597)
      ·
        refine ⟨6878493961867472382091987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36685301129959852704490597 6878493961867472382091987)
        ·
          refine ⟨10317740942801208573137981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6878493961867472382091987 10317740942801208573137981)
          ·
            refine ⟨3869152853550453214926743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10317740942801208573137981 3869152853550453214926743)
            ·
              refine ⟨5803729280325679822390115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869152853550453214926743 5803729280325679822390115)
              ·
                refine ⟨8705593920488519733585173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5803729280325679822390115 8705593920488519733585173)
                ·
                  refine ⟨408074715022899362511805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8705593920488519733585173 408074715022899362511805)
                  ·
                    rfl

theorem cell22_3576252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_3576252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576252 prefixEnd_3576252 := by exact prefixLift 3576252
  have htrace : WordTrace (prefixWord ++ tailWord_3576252) baseStart_3576252 baseEnd_3576252 := by
    simpa [prefixWord, tailWord_3576252, baseEnd_3576252] using wordTrace_append hprefix tailTrace_3576252
  have hstable : (prefixWord ++ tailWord_3576252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576252).length < 2 ^ (prefixWord ++ tailWord_3576252).sum := by decide
  have hdescent : baseEnd_3576252 < baseStart_3576252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576263 : List Nat := [1, 1, 4, 1, 1, 4, 1, 9]
def baseStart_3576263 : Nat := 118140960795 + 3576263 * 2 ^ 59
def prefixEnd_3576263 : Nat := 4983230072969 + 3 ^ 40 * 3576263 * 2
def baseEnd_3576263 : Nat := 136025323399277525056709

theorem tailTrace_3576263 : CollatzResearch.WordTrace tailWord_3576263 prefixEnd_3576263 136025323399277525056709 := by
  unfold tailWord_3576263
  simp only [CollatzResearch.WordTrace]
  refine ⟨130437027442817402939061443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86958018295211601959374295 130437027442817402939061443)
  ·
    refine ⟨195655541164226104408592165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130437027442817402939061443 195655541164226104408592165)
    ·
      refine ⟨36685413968292394576611031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195655541164226104408592165 36685413968292394576611031)
      ·
        refine ⟨55028120952438591864916547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36685413968292394576611031 55028120952438591864916547)
        ·
          refine ⟨82542181428657887797374821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55028120952438591864916547 82542181428657887797374821)
          ·
            refine ⟨15476659017873353962007779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82542181428657887797374821 15476659017873353962007779)
            ·
              refine ⟨23214988526810030943011669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15476659017873353962007779 23214988526810030943011669)
              ·
                refine ⟨136025323399277525056709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23214988526810030943011669 136025323399277525056709)
                ·
                  rfl

theorem cell22_3576263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 9].length) (baseStart_3576263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576263 prefixEnd_3576263 := by exact prefixLift 3576263
  have htrace : WordTrace (prefixWord ++ tailWord_3576263) baseStart_3576263 baseEnd_3576263 := by
    simpa [prefixWord, tailWord_3576263, baseEnd_3576263] using wordTrace_append hprefix tailTrace_3576263
  have hstable : (prefixWord ++ tailWord_3576263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576263).length < 2 ^ (prefixWord ++ tailWord_3576263).sum := by decide
  have hdescent : baseEnd_3576263 < baseStart_3576263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576310 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3576310 : Nat := 118140960795 + 3576310 * 2 ^ 59
def prefixEnd_3576310 : Nat := 4983230072969 + 3 ^ 40 * 3576310 * 2
def baseEnd_3576310 : Nat := 1224243999654005269585237

theorem tailTrace_3576310 : CollatzResearch.WordTrace tailWord_3576310 prefixEnd_3576310 1224243999654005269585237 := by
  unfold tailWord_3576310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152421354602945622876399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86959161115764753310681589 8152421354602945622876399)
  ·
    refine ⟨12228632031904418434314599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8152421354602945622876399 12228632031904418434314599)
    ·
      refine ⟨18342948047856627651471899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228632031904418434314599 18342948047856627651471899)
      ·
        refine ⟨27514422071784941477207849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18342948047856627651471899 27514422071784941477207849)
        ·
          refine ⟨20635816553838706107905887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27514422071784941477207849 20635816553838706107905887)
          ·
            refine ⟨30953724830758059161858831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20635816553838706107905887 30953724830758059161858831)
            ·
              refine ⟨46430587246137088742788247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30953724830758059161858831 46430587246137088742788247)
              ·
                refine ⟨69645880869205633114182371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46430587246137088742788247 69645880869205633114182371)
                ·
                  refine ⟨104468821303808449671273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69645880869205633114182371 104468821303808449671273557)
                  ·
                    refine ⟨1224243999654005269585237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104468821303808449671273557 1224243999654005269585237)
                    ·
                      rfl

theorem cell22_3576310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3576310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576310 prefixEnd_3576310 := by exact prefixLift 3576310
  have htrace : WordTrace (prefixWord ++ tailWord_3576310) baseStart_3576310 baseEnd_3576310 := by
    simpa [prefixWord, tailWord_3576310, baseEnd_3576310] using wordTrace_append hprefix tailTrace_3576310
  have hstable : (prefixWord ++ tailWord_3576310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576310).length < 2 ^ (prefixWord ++ tailWord_3576310).sum := by decide
  have hdescent : baseEnd_3576310 < baseStart_3576310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576325 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 5]
def baseStart_3576325 : Nat := 118140960795 + 3576325 * 2 ^ 59
def prefixEnd_3576325 : Nat := 4983230072969 + 3 ^ 40 * 3576325 * 2
def baseEnd_3576325 : Nat := 408083044820183410153397

theorem tailTrace_3576325 : CollatzResearch.WordTrace tailWord_3576325 prefixEnd_3576325 408083044820183410153397 := by
  unfold tailWord_3576325
  simp only [CollatzResearch.WordTrace]
  refine ⟨130439288768592787527818429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86959525845728525018545619 130439288768592787527818429)
  ·
    refine ⟨48914733288222295322931911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130439288768592787527818429 48914733288222295322931911)
    ·
      refine ⟨73372099932333442984397867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48914733288222295322931911 73372099932333442984397867)
      ·
        refine ⟨110058149898500164476596801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73372099932333442984397867 110058149898500164476596801)
        ·
          refine ⟨82543612423875123357447601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110058149898500164476596801 82543612423875123357447601)
          ·
            refine ⟨61907709317906342518085701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82543612423875123357447601 61907709317906342518085701)
            ·
              refine ⟨11607695497107439222141069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61907709317906342518085701 11607695497107439222141069)
              ·
                refine ⟨4352885811415289708302901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11607695497107439222141069 4352885811415289708302901)
                ·
                  refine ⟨408083044820183410153397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4352885811415289708302901 408083044820183410153397)
                  ·
                    rfl

theorem cell22_3576325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_3576325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576325 prefixEnd_3576325 := by exact prefixLift 3576325
  have htrace : WordTrace (prefixWord ++ tailWord_3576325) baseStart_3576325 baseEnd_3576325 := by
    simpa [prefixWord, tailWord_3576325, baseEnd_3576325] using wordTrace_append hprefix tailTrace_3576325
  have hstable : (prefixWord ++ tailWord_3576325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576325).length < 2 ^ (prefixWord ++ tailWord_3576325).sum := by decide
  have hdescent : baseEnd_3576325 < baseStart_3576325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576359 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 7]
def baseStart_3576359 : Nat := 118140960795 + 3576359 * 2 ^ 59
def prefixEnd_3576359 : Nat := 4983230072969 + 3 ^ 40 * 3576359 * 2
def baseEnd_3576359 : Nat := 408086924451795158370029

theorem tailTrace_3576359 : CollatzResearch.WordTrace tailWord_3576359 prefixEnd_3576359 408086924451795158370029 := by
  unfold tailWord_3576359
  simp only [CollatzResearch.WordTrace]
  refine ⟨130440528850469611334556131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86960352566979740889704087 130440528850469611334556131)
  ·
    refine ⟨195660793275704417001834197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130440528850469611334556131 195660793275704417001834197)
    ·
      refine ⟨4585799842399322273480489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 195660793275704417001834197 4585799842399322273480489)
      ·
        refine ⟨3439349881799491705110367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585799842399322273480489 3439349881799491705110367)
        ·
          refine ⟨5159024822699237557665551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439349881799491705110367 5159024822699237557665551)
          ·
            refine ⟨7738537234048856336498327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159024822699237557665551 7738537234048856336498327)
            ·
              refine ⟨11607805851073284504747491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738537234048856336498327 11607805851073284504747491)
              ·
                refine ⟨17411708776609926757121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11607805851073284504747491 17411708776609926757121237)
                ·
                  refine ⟨408086924451795158370029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17411708776609926757121237 408086924451795158370029)
                  ·
                    rfl

theorem cell22_3576359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].length) (baseStart_3576359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576359 prefixEnd_3576359 := by exact prefixLift 3576359
  have htrace : WordTrace (prefixWord ++ tailWord_3576359) baseStart_3576359 baseEnd_3576359 := by
    simpa [prefixWord, tailWord_3576359, baseEnd_3576359] using wordTrace_append hprefix tailTrace_3576359
  have hstable : (prefixWord ++ tailWord_3576359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576359).length < 2 ^ (prefixWord ++ tailWord_3576359).sum := by decide
  have hdescent : baseEnd_3576359 < baseStart_3576359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576370 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3576370 : Nat := 118140960795 + 3576370 * 2 ^ 59
def prefixEnd_3576370 : Nat := 4983230072969 + 3 ^ 40 * 3576370 * 2
def baseEnd_3576370 : Nat := 408088179626728371028351

theorem tailTrace_3576370 : CollatzResearch.WordTrace tailWord_3576370 prefixEnd_3576370 408088179626728371028351 := by
  unfold tailWord_3576370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32610232513357440053301641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86960620035619840142137709 32610232513357440053301641)
  ·
    refine ⟨24457674385018080039976231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32610232513357440053301641 24457674385018080039976231)
    ·
      refine ⟨36686511577527120059964347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24457674385018080039976231 36686511577527120059964347)
      ·
        refine ⟨55029767366290680089946521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36686511577527120059964347 55029767366290680089946521)
        ·
          refine ⟨41272325524718010067459891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55029767366290680089946521 41272325524718010067459891)
          ·
            refine ⟨61908488287077015101189837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41272325524718010067459891 61908488287077015101189837)
            ·
              refine ⟨23215683107653880662946189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61908488287077015101189837 23215683107653880662946189)
              ·
                refine ⟨8705881165370205248604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23215683107653880662946189 8705881165370205248604821)
                ·
                  refine ⟨408088179626728371028351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8705881165370205248604821 408088179626728371028351)
                  ·
                    rfl

theorem cell22_3576370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3576370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576370 prefixEnd_3576370 := by exact prefixLift 3576370
  have htrace : WordTrace (prefixWord ++ tailWord_3576370) baseStart_3576370 baseEnd_3576370 := by
    simpa [prefixWord, tailWord_3576370, baseEnd_3576370] using wordTrace_append hprefix tailTrace_3576370
  have hstable : (prefixWord ++ tailWord_3576370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576370).length < 2 ^ (prefixWord ++ tailWord_3576370).sum := by decide
  have hdescent : baseEnd_3576370 < baseStart_3576370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576402 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3576402 : Nat := 118140960795 + 3576402 * 2 ^ 59
def prefixEnd_3576402 : Nat := 4983230072969 + 3 ^ 40 * 3576402 * 2
def baseEnd_3576402 : Nat := 1224275493134147696284955

theorem tailTrace_3576402 : CollatzResearch.WordTrace tailWord_3576402 prefixEnd_3576402 1224275493134147696284955 := by
  unfold tailWord_3576402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32610524297328457419592865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86961398126209219785580973 32610524297328457419592865)
  ·
    refine ⟨24457893222996343064694649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32610524297328457419592865 24457893222996343064694649)
    ·
      refine ⟨18343419917247257298520987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24457893222996343064694649 18343419917247257298520987)
      ·
        refine ⟨27515129875870885947781481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343419917247257298520987 27515129875870885947781481)
        ·
          refine ⟨20636347406903164460836111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27515129875870885947781481 20636347406903164460836111)
          ·
            refine ⟨30954521110354746691254167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20636347406903164460836111 30954521110354746691254167)
            ·
              refine ⟨46431781665532120036881251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30954521110354746691254167 46431781665532120036881251)
              ·
                refine ⟨69647672498298180055321877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46431781665532120036881251 69647672498298180055321877)
                ·
                  refine ⟨3264734648357727190093213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69647672498298180055321877 3264734648357727190093213)
                  ·
                    refine ⟨1224275493134147696284955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3264734648357727190093213 1224275493134147696284955)
                    ·
                      rfl

theorem cell22_3576402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3576402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576402 prefixEnd_3576402 := by exact prefixLift 3576402
  have htrace : WordTrace (prefixWord ++ tailWord_3576402) baseStart_3576402 baseEnd_3576402 := by
    simpa [prefixWord, tailWord_3576402, baseEnd_3576402] using wordTrace_append hprefix tailTrace_3576402
  have hstable : (prefixWord ++ tailWord_3576402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576402).length < 2 ^ (prefixWord ++ tailWord_3576402).sum := by decide
  have hdescent : baseEnd_3576402 < baseStart_3576402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576404 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3576404 : Nat := 118140960795 + 3576404 * 2 ^ 59
def prefixEnd_3576404 : Nat := 4983230072969 + 3 ^ 40 * 3576404 * 2
def baseEnd_3576404 : Nat := 408092059258340119244983

theorem tailTrace_3576404 : CollatzResearch.WordTrace tailWord_3576404 prefixEnd_3576404 408092059258340119244983 := by
  unfold tailWord_3576404
  simp only [CollatzResearch.WordTrace]
  refine ⟨65221085067653292009972133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86961446756871056013296177 65221085067653292009972133)
  ·
    refine ⟨12228953450184992251869775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65221085067653292009972133 12228953450184992251869775)
    ·
      refine ⟨18343430175277488377804663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228953450184992251869775 18343430175277488377804663)
      ·
        refine ⟨27515145262916232566706995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343430175277488377804663 27515145262916232566706995)
        ·
          refine ⟨41272717894374348850060493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515145262916232566706995 41272717894374348850060493)
          ·
            refine ⟨15477269210390380818772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41272717894374348850060493 15477269210390380818772685)
            ·
              refine ⟨5803975953896392807039757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15477269210390380818772685 5803975953896392807039757)
              ·
                refine ⟨2176490982711147302639909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5803975953896392807039757 2176490982711147302639909)
                ·
                  refine ⟨408092059258340119244983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176490982711147302639909 408092059258340119244983)
                  ·
                    rfl

theorem cell22_3576404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3576404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576404 prefixEnd_3576404 := by exact prefixLift 3576404
  have htrace : WordTrace (prefixWord ++ tailWord_3576404) baseStart_3576404 baseEnd_3576404 := by
    simpa [prefixWord, tailWord_3576404, baseEnd_3576404] using wordTrace_append hprefix tailTrace_3576404
  have hstable : (prefixWord ++ tailWord_3576404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576404).length < 2 ^ (prefixWord ++ tailWord_3576404).sum := by decide
  have hdescent : baseEnd_3576404 < baseStart_3576404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576417 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3576417 : Nat := 118140960795 + 3576417 * 2 ^ 59
def prefixEnd_3576417 : Nat := 4983230072969 + 3 ^ 40 * 3576417 * 2
def baseEnd_3576417 : Nat := 1224280627940692657159909

theorem tailTrace_3576417 : CollatzResearch.WordTrace tailWord_3576417 prefixEnd_3576417 1224280627940692657159909 := by
  unfold tailWord_3576417
  simp only [CollatzResearch.WordTrace]
  refine ⟨130442644284259487240167505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86961762856172991493445003 130442644284259487240167505)
  ·
    refine ⟨97831983213194615430125629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130442644284259487240167505 97831983213194615430125629)
    ·
      refine ⟨36686993704947980786297111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97831983213194615430125629 36686993704947980786297111)
      ·
        refine ⟨55030490557421971179445667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36686993704947980786297111 55030490557421971179445667)
        ·
          refine ⟨82545735836132956769168501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55030490557421971179445667 82545735836132956769168501)
          ·
            refine ⟨7738662734637464697109547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82545735836132956769168501 7738662734637464697109547)
            ·
              refine ⟨11607994101956197045664321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738662734637464697109547 11607994101956197045664321)
              ·
                refine ⟨8705995576467147784248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607994101956197045664321 8705995576467147784248241)
                ·
                  refine ⟨6529496682350360838186181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8705995576467147784248241 6529496682350360838186181)
                  ·
                    refine ⟨1224280627940692657159909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6529496682350360838186181 1224280627940692657159909)
                    ·
                      rfl

theorem cell22_3576417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3576417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576417 prefixEnd_3576417 := by exact prefixLift 3576417
  have htrace : WordTrace (prefixWord ++ tailWord_3576417) baseStart_3576417 baseEnd_3576417 := by
    simpa [prefixWord, tailWord_3576417, baseEnd_3576417] using wordTrace_append hprefix tailTrace_3576417
  have hstable : (prefixWord ++ tailWord_3576417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576417).length < 2 ^ (prefixWord ++ tailWord_3576417).sum := by decide
  have hdescent : baseEnd_3576417 < baseStart_3576417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576421 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 4]
def baseStart_3576421 : Nat := 118140960795 + 3576421 * 2 ^ 59
def prefixEnd_3576421 : Nat := 4983230072969 + 3 ^ 40 * 3576421 * 2
def baseEnd_3576421 : Nat := 408093999074145993353299

theorem tailTrace_3576421 : CollatzResearch.WordTrace tailWord_3576421 prefixEnd_3576421 408093999074145993353299 := by
  unfold tailWord_3576421
  simp only [CollatzResearch.WordTrace]
  refine ⟨130442790176244995923313117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86961860117496663948875411 130442790176244995923313117)
  ·
    refine ⟨48916046316091873471242419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130442790176244995923313117 48916046316091873471242419)
    ·
      refine ⟨73374069474137810206863629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48916046316091873471242419 73374069474137810206863629)
      ·
        refine ⟨27515276052801678827573861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73374069474137810206863629 27515276052801678827573861)
        ·
          refine ⟨5159114259900314780170099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27515276052801678827573861 5159114259900314780170099)
          ·
            refine ⟨7738671389850472170255149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159114259900314780170099 7738671389850472170255149)
            ·
              refine ⟨2902001771193927063845681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7738671389850472170255149 2902001771193927063845681)
              ·
                refine ⟨2176501328395445297884261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902001771193927063845681 2176501328395445297884261)
                ·
                  refine ⟨408093999074145993353299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176501328395445297884261 408093999074145993353299)
                  ·
                    rfl

theorem cell22_3576421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_3576421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576421 prefixEnd_3576421 := by exact prefixLift 3576421
  have htrace : WordTrace (prefixWord ++ tailWord_3576421) baseStart_3576421 baseEnd_3576421 := by
    simpa [prefixWord, tailWord_3576421, baseEnd_3576421] using wordTrace_append hprefix tailTrace_3576421
  have hstable : (prefixWord ++ tailWord_3576421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576421).length < 2 ^ (prefixWord ++ tailWord_3576421).sum := by decide
  have hdescent : baseEnd_3576421 < baseStart_3576421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576432 : List Nat := [2, 1, 1, 1, 7, 1, 2, 7]
def baseStart_3576432 : Nat := 118140960795 + 3576432 * 2 ^ 59
def prefixEnd_3576432 : Nat := 4983230072969 + 3 ^ 40 * 3576432 * 2
def baseEnd_3576432 : Nat := 136031751416359735337207

theorem tailTrace_3576432 : CollatzResearch.WordTrace tailWord_3576432 prefixEnd_3576432 136031751416359735337207 := by
  unfold tailWord_3576432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65221595689602572400981775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86962127586136763201309033 65221595689602572400981775)
  ·
    refine ⟨97832393534403858601472663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65221595689602572400981775 97832393534403858601472663)
    ·
      refine ⟨146748590301605787902208995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97832393534403858601472663 146748590301605787902208995)
      ·
        refine ⟨220122885452408681853313493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146748590301605787902208995 220122885452408681853313493)
        ·
          refine ⟨5159130127790828480937035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 220122885452408681853313493 5159130127790828480937035)
          ·
            refine ⟨7738695191686242721405553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159130127790828480937035 7738695191686242721405553)
            ·
              refine ⟨5804021393764682041054165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7738695191686242721405553 5804021393764682041054165)
              ·
                refine ⟨136031751416359735337207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5804021393764682041054165 136031751416359735337207)
                ·
                  rfl

theorem cell22_3576432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_3576432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576432 prefixEnd_3576432 := by exact prefixLift 3576432
  have htrace : WordTrace (prefixWord ++ tailWord_3576432) baseStart_3576432 baseEnd_3576432 := by
    simpa [prefixWord, tailWord_3576432, baseEnd_3576432] using wordTrace_append hprefix tailTrace_3576432
  have hstable : (prefixWord ++ tailWord_3576432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576432).length < 2 ^ (prefixWord ++ tailWord_3576432).sum := by decide
  have hdescent : baseEnd_3576432 < baseStart_3576432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576460 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3576460 : Nat := 118140960795 + 3576460 * 2 ^ 59
def prefixEnd_3576460 : Nat := 4983230072969 + 3 ^ 40 * 3576460 * 2
def baseEnd_3576460 : Nat := 408098449239818292778259

theorem tailTrace_3576460 : CollatzResearch.WordTrace tailWord_3576460 prefixEnd_3576460 408098449239818292778259 := by
  unfold tailWord_3576460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65222106311551852791991417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86962808415402470389321889 65222106311551852791991417)
  ·
    refine ⟨48916579733663889593993563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65222106311551852791991417 48916579733663889593993563)
    ·
      refine ⟨73374869600495834390990345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48916579733663889593993563 73374869600495834390990345)
      ·
        refine ⟨55031152200371875793242759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73374869600495834390990345 55031152200371875793242759)
        ·
          refine ⟨82546728300557813689864139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55031152200371875793242759 82546728300557813689864139)
          ·
            refine ⟨123820092450836720534796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82546728300557813689864139 123820092450836720534796209)
            ·
              refine ⟨92865069338127540401097157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123820092450836720534796209 92865069338127540401097157)
              ·
                refine ⟨17412200500898913825205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92865069338127540401097157 17412200500898913825205717)
                ·
                  refine ⟨408098449239818292778259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17412200500898913825205717 408098449239818292778259)
                  ·
                    rfl

theorem cell22_3576460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3576460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576460 prefixEnd_3576460 := by exact prefixLift 3576460
  have htrace : WordTrace (prefixWord ++ tailWord_3576460) baseStart_3576460 baseEnd_3576460 := by
    simpa [prefixWord, tailWord_3576460, baseEnd_3576460] using wordTrace_append hprefix tailTrace_3576460
  have hstable : (prefixWord ++ tailWord_3576460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576460).length < 2 ^ (prefixWord ++ tailWord_3576460).sum := by decide
  have hdescent : baseEnd_3576460 < baseStart_3576460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576477 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3576477 : Nat := 118140960795 + 3576477 * 2 ^ 59
def prefixEnd_3576477 : Nat := 4983230072969 + 3 ^ 40 * 3576477 * 2
def baseEnd_3576477 : Nat := 408100389055624166886575

theorem tailTrace_3576477 : CollatzResearch.WordTrace tailWord_3576477 prefixEnd_3576477 408100389055624166886575 := by
  unfold tailWord_3576477
  simp only [CollatzResearch.WordTrace]
  refine ⟨130444832664042117487351685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86963221776028078324901123 130444832664042117487351685)
  ·
    refine ⟨24458406124507897028878441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130444832664042117487351685 24458406124507897028878441)
    ·
      refine ⟨18343804593380922771658831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24458406124507897028878441 18343804593380922771658831)
      ·
        refine ⟨27515706890071384157488247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343804593380922771658831 27515706890071384157488247)
        ·
          refine ⟨41273560335107076236232371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515706890071384157488247 41273560335107076236232371)
          ·
            refine ⟨61910340502660614354348557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41273560335107076236232371 61910340502660614354348557)
            ·
              refine ⟨23216377688497730382880709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61910340502660614354348557 23216377688497730382880709)
              ·
                refine ⟨4353070816593324446790133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23216377688497730382880709 4353070816593324446790133)
                ·
                  refine ⟨408100389055624166886575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4353070816593324446790133 408100389055624166886575)
                  ·
                    rfl

theorem cell22_3576477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3576477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576477 prefixEnd_3576477 := by exact prefixLift 3576477
  have htrace : WordTrace (prefixWord ++ tailWord_3576477) baseStart_3576477 baseEnd_3576477 := by
    simpa [prefixWord, tailWord_3576477, baseEnd_3576477] using wordTrace_append hprefix tailTrace_3576477
  have hstable : (prefixWord ++ tailWord_3576477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576477).length < 2 ^ (prefixWord ++ tailWord_3576477).sum := by decide
  have hdescent : baseEnd_3576477 < baseStart_3576477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576597 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3576597 : Nat := 118140960795 + 3576597 * 2 ^ 59
def prefixEnd_3576597 : Nat := 4983230072969 + 3 ^ 40 * 3576597 * 2
def baseEnd_3576597 : Nat := 1224342245619232187659357

theorem tailTrace_3576597 : CollatzResearch.WordTrace tailWord_3576597 prefixEnd_3576597 1224342245619232187659357 := by
  unfold tailWord_3576597
  simp only [CollatzResearch.WordTrace]
  refine ⟨130449209423607377981720045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86966139615738251987813363 130449209423607377981720045)
  ·
    refine ⟨48918453533852766743145017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130449209423607377981720045 48918453533852766743145017)
    ·
      refine ⟨36688840150389575057358763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48918453533852766743145017 36688840150389575057358763)
      ·
        refine ⟨55033260225584362586038145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36688840150389575057358763 55033260225584362586038145)
        ·
          refine ⟨41274945169188271939528609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55033260225584362586038145 41274945169188271939528609)
          ·
            refine ⟨30956208876891203954646457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41274945169188271939528609 30956208876891203954646457)
            ·
              refine ⟨23217156657668402965984843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30956208876891203954646457 23217156657668402965984843)
              ·
                refine ⟨34825734986502604448977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23217156657668402965984843 34825734986502604448977265)
                ·
                  refine ⟨26119301239876953336732949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34825734986502604448977265 26119301239876953336732949)
                  ·
                    refine ⟨1224342245619232187659357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26119301239876953336732949 1224342245619232187659357)
                    ·
                      rfl

theorem cell22_3576597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3576597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576597 prefixEnd_3576597 := by exact prefixLift 3576597
  have htrace : WordTrace (prefixWord ++ tailWord_3576597) baseStart_3576597 baseEnd_3576597 := by
    simpa [prefixWord, tailWord_3576597, baseEnd_3576597] using wordTrace_append hprefix tailTrace_3576597
  have hstable : (prefixWord ++ tailWord_3576597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576597).length < 2 ^ (prefixWord ++ tailWord_3576597).sum := by decide
  have hdescent : baseEnd_3576597 < baseStart_3576597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576689 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3576689 : Nat := 118140960795 + 3576689 * 2 ^ 59
def prefixEnd_3576689 : Nat := 4983230072969 + 3 ^ 40 * 3576689 * 2
def baseEnd_3576689 : Nat := 1224373739099374614359075

theorem tailTrace_3576689 : CollatzResearch.WordTrace tailWord_3576689 prefixEnd_3576689 1224373739099374614359075 := by
  unfold tailWord_3576689
  simp only [CollatzResearch.WordTrace]
  refine ⟨130452564939274077694069121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86968376626182718462712747 130452564939274077694069121)
  ·
    refine ⟨97839423704455558270551841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130452564939274077694069121 97839423704455558270551841)
    ·
      refine ⟨73379567778341668702913881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97839423704455558270551841 73379567778341668702913881)
      ·
        refine ⟨55034675833756251527185411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73379567778341668702913881 55034675833756251527185411)
        ·
          refine ⟨82552013750634377290778117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55034675833756251527185411 82552013750634377290778117)
          ·
            refine ⟨15478502578243945742020897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82552013750634377290778117 15478502578243945742020897)
            ·
              refine ⟨11608876933682959306515673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15478502578243945742020897 11608876933682959306515673)
              ·
                refine ⟨8706657700262219479886755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11608876933682959306515673 8706657700262219479886755)
                ·
                  refine ⟨13059986550393329219830133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8706657700262219479886755 13059986550393329219830133)
                  ·
                    refine ⟨1224373739099374614359075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13059986550393329219830133 1224373739099374614359075)
                    ·
                      rfl

theorem cell22_3576689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3576689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576689 prefixEnd_3576689 := by exact prefixLift 3576689
  have htrace : WordTrace (prefixWord ++ tailWord_3576689) baseStart_3576689 baseEnd_3576689 := by
    simpa [prefixWord, tailWord_3576689, baseEnd_3576689] using wordTrace_append hprefix tailTrace_3576689
  have hstable : (prefixWord ++ tailWord_3576689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576689).length < 2 ^ (prefixWord ++ tailWord_3576689).sum := by decide
  have hdescent : baseEnd_3576689 < baseStart_3576689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576693 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3576693 : Nat := 118140960795 + 3576693 * 2 ^ 59
def prefixEnd_3576693 : Nat := 4983230072969 + 3 ^ 40 * 3576693 * 2
def baseEnd_3576693 : Nat := 1224375108381119937259063

theorem tailTrace_3576693 : CollatzResearch.WordTrace tailWord_3576693 prefixEnd_3576693 1224375108381119937259063 := by
  unfold tailWord_3576693
  simp only [CollatzResearch.WordTrace]
  refine ⟨130452710831259586377214733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86968473887506390918143155 130452710831259586377214733)
  ·
    refine ⟨48919766561722344891455525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130452710831259586377214733 48919766561722344891455525)
    ·
      refine ⟨9172456230322939667147911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48919766561722344891455525 9172456230322939667147911)
      ·
        refine ⟨13758684345484409500721867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172456230322939667147911 13758684345484409500721867)
        ·
          refine ⟨20638026518226614251082801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13758684345484409500721867 20638026518226614251082801)
          ·
            refine ⟨15478519888669960688312101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20638026518226614251082801 15478519888669960688312101)
            ·
              refine ⟨2902222479125617629058519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15478519888669960688312101 2902222479125617629058519)
              ·
                refine ⟨4353333718688426443587779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902222479125617629058519 4353333718688426443587779)
                ·
                  refine ⟨6530000578032639665381669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353333718688426443587779 6530000578032639665381669)
                  ·
                    refine ⟨1224375108381119937259063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530000578032639665381669 1224375108381119937259063)
                    ·
                      rfl

theorem cell22_3576693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3576693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576693 prefixEnd_3576693 := by exact prefixLift 3576693
  have htrace : WordTrace (prefixWord ++ tailWord_3576693) baseStart_3576693 baseEnd_3576693 := by
    simpa [prefixWord, tailWord_3576693, baseEnd_3576693] using wordTrace_append hprefix tailTrace_3576693
  have hstable : (prefixWord ++ tailWord_3576693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576693).length < 2 ^ (prefixWord ++ tailWord_3576693).sum := by decide
  have hdescent : baseEnd_3576693 < baseStart_3576693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576768 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_3576768 : Nat := 118140960795 + 3576768 * 2 ^ 59
def prefixEnd_3576768 : Nat := 4983230072969 + 3 ^ 40 * 3576768 * 2
def baseEnd_3576768 : Nat := 1224400782413844741633833

theorem tailTrace_3576768 : CollatzResearch.WordTrace tailWord_3576768 prefixEnd_3576768 1224400782413844741633833 := by
  unfold tailWord_3576768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65227723152993937093097479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86970297537325249457463305 65227723152993937093097479)
  ·
    refine ⟨97841584729490905639646219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65227723152993937093097479 97841584729490905639646219)
    ·
      refine ⟨146762377094236358459469329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97841584729490905639646219 146762377094236358459469329)
      ·
        refine ⟨110071782820677268844601997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146762377094236358459469329 110071782820677268844601997)
        ·
          refine ⟨41276918557753975816725749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110071782820677268844601997 41276918557753975816725749)
          ·
            refine ⟨3869711114789435232818039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41276918557753975816725749 3869711114789435232818039)
            ·
              refine ⟨5804566672184152849227059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3869711114789435232818039 5804566672184152849227059)
              ·
                refine ⟨8706850008276229273840589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5804566672184152849227059 8706850008276229273840589)
                ·
                  refine ⟨3265068753103585977690221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8706850008276229273840589 3265068753103585977690221)
                  ·
                    refine ⟨1224400782413844741633833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265068753103585977690221 1224400782413844741633833)
                    ·
                      rfl

theorem cell22_3576768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_3576768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576768 prefixEnd_3576768 := by exact prefixLift 3576768
  have htrace : WordTrace (prefixWord ++ tailWord_3576768) baseStart_3576768 baseEnd_3576768 := by
    simpa [prefixWord, tailWord_3576768, baseEnd_3576768] using wordTrace_append hprefix tailTrace_3576768
  have hstable : (prefixWord ++ tailWord_3576768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576768).length < 2 ^ (prefixWord ++ tailWord_3576768).sum := by decide
  have hdescent : baseEnd_3576768 < baseStart_3576768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576824 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_3576824 : Nat := 118140960795 + 3576824 * 2 ^ 59
def prefixEnd_3576824 : Nat := 4983230072969 + 3 ^ 40 * 3576824 * 2
def baseEnd_3576824 : Nat := 1224419952358279262233661

theorem tailTrace_3576824 : CollatzResearch.WordTrace tailWord_3576824 prefixEnd_3576824 1224419952358279262233661 := by
  unfold tailWord_3576824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65228744396892497875116763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86971659195856663833489017 65228744396892497875116763)
  ·
    refine ⟨97843116595338746812675145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65228744396892497875116763 97843116595338746812675145)
    ·
      refine ⟨73382337446504060109506359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97843116595338746812675145 73382337446504060109506359)
      ·
        refine ⟨110073506169756090164259539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73382337446504060109506359 110073506169756090164259539)
        ·
          refine ⟨165110259254634135246389309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110073506169756090164259539 165110259254634135246389309)
          ·
            refine ⟨61916347220487800717395991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165110259254634135246389309 61916347220487800717395991)
            ·
              refine ⟨92874520830731701076093987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61916347220487800717395991 92874520830731701076093987)
              ·
                refine ⟨139311781246097551614140981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92874520830731701076093987 139311781246097551614140981)
                ·
                  refine ⟨13060479491821645463825717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139311781246097551614140981 13060479491821645463825717)
                  ·
                    refine ⟨1224419952358279262233661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13060479491821645463825717 1224419952358279262233661)
                    ·
                      rfl

theorem cell22_3576824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_3576824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576824 prefixEnd_3576824 := by exact prefixLift 3576824
  have htrace : WordTrace (prefixWord ++ tailWord_3576824) baseStart_3576824 baseEnd_3576824 := by
    simpa [prefixWord, tailWord_3576824, baseEnd_3576824] using wordTrace_append hprefix tailTrace_3576824
  have hstable : (prefixWord ++ tailWord_3576824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576824).length < 2 ^ (prefixWord ++ tailWord_3576824).sum := by decide
  have hdescent : baseEnd_3576824 < baseStart_3576824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576856 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_3576856 : Nat := 118140960795 + 3576856 * 2 ^ 59
def prefixEnd_3576856 : Nat := 4983230072969 + 3 ^ 40 * 3576856 * 2
def baseEnd_3576856 : Nat := 1224430906612241845433563

theorem tailTrace_3576856 : CollatzResearch.WordTrace tailWord_3576856 prefixEnd_3576856 1224430906612241845433563 := by
  unfold tailWord_3576856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65229327964834532607699211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86972437286446043476932281 65229327964834532607699211)
  ·
    refine ⟨97843991947251798911548817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65229327964834532607699211 97843991947251798911548817)
    ·
      refine ⟨73382993960438849183661613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97843991947251798911548817 73382993960438849183661613)
      ·
        refine ⟨27518622735164568443873105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73382993960438849183661613 27518622735164568443873105)
        ·
          refine ⟨20638967051373426332904829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27518622735164568443873105 20638967051373426332904829)
          ·
            refine ⟨7739612644265034874839311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20638967051373426332904829 7739612644265034874839311)
            ·
              refine ⟨11609418966397552312258967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739612644265034874839311 11609418966397552312258967)
              ·
                refine ⟨17414128449596328468388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609418966397552312258967 17414128449596328468388451)
                ·
                  refine ⟨26121192674394492702582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17414128449596328468388451 26121192674394492702582677)
                  ·
                    refine ⟨1224430906612241845433563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26121192674394492702582677 1224430906612241845433563)
                    ·
                      rfl

theorem cell22_3576856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_3576856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576856 prefixEnd_3576856 := by exact prefixLift 3576856
  have htrace : WordTrace (prefixWord ++ tailWord_3576856) baseStart_3576856 baseEnd_3576856 := by
    simpa [prefixWord, tailWord_3576856, baseEnd_3576856] using wordTrace_append hprefix tailTrace_3576856
  have hstable : (prefixWord ++ tailWord_3576856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576856).length < 2 ^ (prefixWord ++ tailWord_3576856).sum := by decide
  have hdescent : baseEnd_3576856 < baseStart_3576856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576860 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_3576860 : Nat := 118140960795 + 3576860 * 2 ^ 59
def prefixEnd_3576860 : Nat := 4983230072969 + 3 ^ 40 * 3576860 * 2
def baseEnd_3576860 : Nat := 408144091964662389444517

theorem tailTrace_3576860 : CollatzResearch.WordTrace tailWord_3576860 prefixEnd_3576860 408144091964662389444517 := by
  unfold tailWord_3576860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65229400910827286949272017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86972534547769715932362689 65229400910827286949272017)
  ·
    refine ⟨48922050683120465211954013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65229400910827286949272017 48922050683120465211954013)
    ·
      refine ⟨18345769006170174454482755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48922050683120465211954013 18345769006170174454482755)
      ·
        refine ⟨27518653509255261681724133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18345769006170174454482755 27518653509255261681724133)
        ·
          refine ⟨5159747532985361565323275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27518653509255261681724133 5159747532985361565323275)
          ·
            refine ⟨7739621299478042347984913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159747532985361565323275 7739621299478042347984913)
            ·
              refine ⟨5804715974608531760988685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7739621299478042347984913 5804715974608531760988685)
              ·
                refine ⟨2176768490478199410370757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5804715974608531760988685 2176768490478199410370757)
                ·
                  refine ⟨408144091964662389444517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176768490478199410370757 408144091964662389444517)
                  ·
                    rfl

theorem cell22_3576860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_3576860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576860 prefixEnd_3576860 := by exact prefixLift 3576860
  have htrace : WordTrace (prefixWord ++ tailWord_3576860) baseStart_3576860 baseEnd_3576860 := by
    simpa [prefixWord, tailWord_3576860, baseEnd_3576860] using wordTrace_append hprefix tailTrace_3576860
  have hstable : (prefixWord ++ tailWord_3576860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576860).length < 2 ^ (prefixWord ++ tailWord_3576860).sum := by decide
  have hdescent : baseEnd_3576860 < baseStart_3576860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576903 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3576903 : Nat := 118140960795 + 3576903 * 2 ^ 59
def prefixEnd_3576903 : Nat := 4983230072969 + 3 ^ 40 * 3576903 * 2
def baseEnd_3576903 : Nat := 1224446995672749389508419

theorem tailTrace_3576903 : CollatzResearch.WordTrace tailWord_3576903 prefixEnd_3576903 1224446995672749389508419 := by
  unfold tailWord_3576903
  simp only [CollatzResearch.WordTrace]
  refine ⟨130460370160498792242359363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86973580106999194828239575 130460370160498792242359363)
  ·
    refine ⟨195690555240748188363539045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130460370160498792242359363 195690555240748188363539045)
    ·
      refine ⟨36691979107640285318163571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195690555240748188363539045 36691979107640285318163571)
      ·
        refine ⟨55037968661460427977245357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36691979107640285318163571 55037968661460427977245357)
        ·
          refine ⟨20639238248047660491467009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55037968661460427977245357 20639238248047660491467009)
          ·
            refine ⟨15479428686035745368600257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20639238248047660491467009 15479428686035745368600257)
            ·
              refine ⟨11609571514526809026450193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479428686035745368600257 11609571514526809026450193)
              ·
                refine ⟨8707178635895106769837645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11609571514526809026450193 8707178635895106769837645)
                ·
                  refine ⟨3265191988460665038689117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8707178635895106769837645 3265191988460665038689117)
                  ·
                    refine ⟨1224446995672749389508419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265191988460665038689117 1224446995672749389508419)
                    ·
                      rfl

theorem cell22_3576903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3576903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576903 prefixEnd_3576903 := by exact prefixLift 3576903
  have htrace : WordTrace (prefixWord ++ tailWord_3576903) baseStart_3576903 baseEnd_3576903 := by
    simpa [prefixWord, tailWord_3576903, baseEnd_3576903] using wordTrace_append hprefix tailTrace_3576903
  have hstable : (prefixWord ++ tailWord_3576903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576903).length < 2 ^ (prefixWord ++ tailWord_3576903).sum := by decide
  have hdescent : baseEnd_3576903 < baseStart_3576903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576916 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3576916 : Nat := 118140960795 + 3576916 * 2 ^ 59
def prefixEnd_3576916 : Nat := 4983230072969 + 3 ^ 40 * 3576916 * 2
def baseEnd_3576916 : Nat := 408150481946140562977793

theorem tailTrace_3576916 : CollatzResearch.WordTrace tailWord_3576916 prefixEnd_3576916 408150481946140562977793 := by
  unfold tailWord_3576916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65230422154725847731291301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86973896206301130308388401 65230422154725847731291301)
  ·
    refine ⟨12230704154011096449617119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65230422154725847731291301 12230704154011096449617119)
    ·
      refine ⟨18346056231016644674425679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12230704154011096449617119 18346056231016644674425679)
      ·
        refine ⟨27519084346524967011638519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18346056231016644674425679 27519084346524967011638519)
        ·
          refine ⟨41278626519787450517457779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27519084346524967011638519 41278626519787450517457779)
          ·
            refine ⟨61917939779681175776186669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41278626519787450517457779 61917939779681175776186669)
            ·
              refine ⟨23219227417380440916070001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61917939779681175776186669 23219227417380440916070001)
              ·
                refine ⟨17414420563035330687052501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23219227417380440916070001 17414420563035330687052501)
                ·
                  refine ⟨408150481946140562977793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17414420563035330687052501 408150481946140562977793)
                  ·
                    rfl

theorem cell22_3576916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3576916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576916 prefixEnd_3576916 := by exact prefixLift 3576916
  have htrace : WordTrace (prefixWord ++ tailWord_3576916) baseStart_3576916 baseEnd_3576916 := by
    simpa [prefixWord, tailWord_3576916, baseEnd_3576916] using wordTrace_append hprefix tailTrace_3576916
  have hstable : (prefixWord ++ tailWord_3576916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576916).length < 2 ^ (prefixWord ++ tailWord_3576916).sum := by decide
  have hdescent : baseEnd_3576916 < baseStart_3576916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3576937 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_3576937 : Nat := 118140960795 + 3576937 * 2 ^ 59
def prefixEnd_3576937 : Nat := 4983230072969 + 3 ^ 40 * 3576937 * 2
def baseEnd_3576937 : Nat := 1224458634567584634158315

theorem tailTrace_3576937 : CollatzResearch.WordTrace tailWord_3576937 prefixEnd_3576937 1224458634567584634158315 := by
  unfold tailWord_3576937
  simp only [CollatzResearch.WordTrace]
  refine ⟨130461610242375616049097065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86974406828250410699398043 130461610242375616049097065)
  ·
    refine ⟨97846207681781712036822799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130461610242375616049097065 97846207681781712036822799)
    ·
      refine ⟨146769311522672568055234199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97846207681781712036822799 146769311522672568055234199)
      ·
        refine ⟨220153967284008852082851299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146769311522672568055234199 220153967284008852082851299)
        ·
          refine ⟨330230950926013278124276949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220153967284008852082851299 330230950926013278124276949)
          ·
            refine ⟨7739787912328436206037741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 330230950926013278124276949 7739787912328436206037741)
            ·
              refine ⟨2902420467123163577264153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7739787912328436206037741 2902420467123163577264153)
              ·
                refine ⟨2176815350342372682948115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902420467123163577264153 2176815350342372682948115)
                ·
                  refine ⟨3265223025513559024422173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176815350342372682948115 3265223025513559024422173)
                  ·
                    refine ⟨1224458634567584634158315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265223025513559024422173 1224458634567584634158315)
                    ·
                      rfl

theorem cell22_3576937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_3576937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3576937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3576937 prefixEnd_3576937 := by exact prefixLift 3576937
  have htrace : WordTrace (prefixWord ++ tailWord_3576937) baseStart_3576937 baseEnd_3576937 := by
    simpa [prefixWord, tailWord_3576937, baseEnd_3576937] using wordTrace_append hprefix tailTrace_3576937
  have hstable : (prefixWord ++ tailWord_3576937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3576937).length < 2 ^ (prefixWord ++ tailWord_3576937).sum := by decide
  have hdescent : baseEnd_3576937 < baseStart_3576937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3576937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577010 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_3577010 : Nat := 118140960795 + 3577010 * 2 ^ 59
def prefixEnd_3577010 : Nat := 4983230072969 + 3 ^ 40 * 3577010 * 2
def baseEnd_3577010 : Nat := 1224483623959436777083091

theorem tailTrace_3577010 : CollatzResearch.WordTrace tailWord_3577010 prefixEnd_3577010 1224483623959436777083091 := by
  unfold tailWord_3577010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616068192777787379126121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86976181847407433011002989 32616068192777787379126121)
  ·
    refine ⟨24462051144583340534344591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32616068192777787379126121 24462051144583340534344591)
    ·
      refine ⟨36693076716875010801516887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24462051144583340534344591 36693076716875010801516887)
      ·
        refine ⟨55039615075312516202275331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36693076716875010801516887 55039615075312516202275331)
        ·
          refine ⟨82559422612968774303412997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55039615075312516202275331 82559422612968774303412997)
          ·
            refine ⟨15479891739931645181889937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82559422612968774303412997 15479891739931645181889937)
            ·
              refine ⟨11609918804948733886417453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15479891739931645181889937 11609918804948733886417453)
              ·
                refine ⟨4353719551855775207406545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11609918804948733886417453 4353719551855775207406545)
                ·
                  refine ⟨3265289663891831405554909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4353719551855775207406545 3265289663891831405554909)
                  ·
                    refine ⟨1224483623959436777083091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265289663891831405554909 1224483623959436777083091)
                    ·
                      rfl

theorem cell22_3577010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_3577010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577010 prefixEnd_3577010 := by exact prefixLift 3577010
  have htrace : WordTrace (prefixWord ++ tailWord_3577010) baseStart_3577010 baseEnd_3577010 := by
    simpa [prefixWord, tailWord_3577010, baseEnd_3577010] using wordTrace_append hprefix tailTrace_3577010
  have hstable : (prefixWord ++ tailWord_3577010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577010).length < 2 ^ (prefixWord ++ tailWord_3577010).sum := by decide
  have hdescent : baseEnd_3577010 < baseStart_3577010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577025 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3577025 : Nat := 118140960795 + 3577025 * 2 ^ 59
def prefixEnd_3577025 : Nat := 4983230072969 + 3 ^ 40 * 3577025 * 2
def baseEnd_3577025 : Nat := 1224488758765981737958045

theorem tailTrace_3577025 : CollatzResearch.WordTrace tailWord_3577025 prefixEnd_3577025 1224488758765981737958045 := by
  unfold tailWord_3577025
  simp only [CollatzResearch.WordTrace]
  refine ⟨130464819866056807078300529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86976546577371204718867019 130464819866056807078300529)
  ·
    refine ⟨97848614899542605308725397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130464819866056807078300529 97848614899542605308725397)
    ·
      refine ⟨4586653823416059623846503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97848614899542605308725397 4586653823416059623846503)
      ·
        refine ⟨6879980735124089435769755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586653823416059623846503 6879980735124089435769755)
        ·
          refine ⟨10319971102686134153654633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879980735124089435769755 10319971102686134153654633)
          ·
            refine ⟨7739978327014600615240975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10319971102686134153654633 7739978327014600615240975)
            ·
              refine ⟨11609967490521900922861463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7739978327014600615240975 11609967490521900922861463)
              ·
                refine ⟨17414951235782851384292195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11609967490521900922861463 17414951235782851384292195)
                ·
                  refine ⟨26122426853674277076438293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17414951235782851384292195 26122426853674277076438293)
                  ·
                    refine ⟨1224488758765981737958045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26122426853674277076438293 1224488758765981737958045)
                    ·
                      rfl

theorem cell22_3577025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3577025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577025 prefixEnd_3577025 := by exact prefixLift 3577025
  have htrace : WordTrace (prefixWord ++ tailWord_3577025) baseStart_3577025 baseEnd_3577025 := by
    simpa [prefixWord, tailWord_3577025, baseEnd_3577025] using wordTrace_append hprefix tailTrace_3577025
  have hstable : (prefixWord ++ tailWord_3577025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577025).length < 2 ^ (prefixWord ++ tailWord_3577025).sum := by decide
  have hdescent : baseEnd_3577025 < baseStart_3577025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577089 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3577089 : Nat := 118140960795 + 3577089 * 2 ^ 59
def prefixEnd_3577089 : Nat := 4983230072969 + 3 ^ 40 * 3577089 * 2
def baseEnd_3577089 : Nat := 1224510667273906904357849

theorem tailTrace_3577089 : CollatzResearch.WordTrace tailWord_3577089 prefixEnd_3577089 1224510667273906904357849 := by
  unfold tailWord_3577089
  simp only [CollatzResearch.WordTrace]
  refine ⟨130467154137824946008630321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86978102758549964005753547 130467154137824946008630321)
  ·
    refine ⟨97850365603368709506472741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130467154137824946008630321 97850365603368709506472741)
    ·
      refine ⟨18346943550631633032463639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97850365603368709506472741 18346943550631633032463639)
      ·
        refine ⟨27520415325947449548695459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18346943550631633032463639 27520415325947449548695459)
        ·
          refine ⟨41280622988921174323043189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27520415325947449548695459 41280622988921174323043189)
          ·
            refine ⟨3870058405211360092785299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41280622988921174323043189 3870058405211360092785299)
            ·
              refine ⟨5805087607817040139177949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870058405211360092785299 5805087607817040139177949)
              ·
                refine ⟨2176907852931390052191731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5805087607817040139177949 2176907852931390052191731)
                ·
                  refine ⟨3265361779397085078287597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176907852931390052191731 3265361779397085078287597)
                  ·
                    refine ⟨1224510667273906904357849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265361779397085078287597 1224510667273906904357849)
                    ·
                      rfl

theorem cell22_3577089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3577089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577089 prefixEnd_3577089 := by exact prefixLift 3577089
  have htrace : WordTrace (prefixWord ++ tailWord_3577089) baseStart_3577089 baseEnd_3577089 := by
    simpa [prefixWord, tailWord_3577089, baseEnd_3577089] using wordTrace_append hprefix tailTrace_3577089
  have hstable : (prefixWord ++ tailWord_3577089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577089).length < 2 ^ (prefixWord ++ tailWord_3577089).sum := by decide
  have hdescent : baseEnd_3577089 < baseStart_3577089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577098 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3577098 : Nat := 118140960795 + 3577098 * 2 ^ 59
def prefixEnd_3577098 : Nat := 4983230072969 + 3 ^ 40 * 3577098 * 2
def baseEnd_3577098 : Nat := 1224513748157833880882821

theorem tailTrace_3577098 : CollatzResearch.WordTrace tailWord_3577098 prefixEnd_3577098 1224513748157833880882821 := by
  unfold tailWord_3577098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616870598698085136426987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86978321596528227030471965 32616870598698085136426987)
  ·
    refine ⟨48925305898047127704640481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32616870598698085136426987 48925305898047127704640481)
    ·
      refine ⟨36693979423535345778480361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48925305898047127704640481 36693979423535345778480361)
      ·
        refine ⟨27520484567651509333860271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36693979423535345778480361 27520484567651509333860271)
        ·
          refine ⟨41280726851477264000790407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27520484567651509333860271 41280726851477264000790407)
          ·
            refine ⟨61921090277215896001185611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41280726851477264000790407 61921090277215896001185611)
            ·
              refine ⟨92881635415823844001778417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61921090277215896001185611 92881635415823844001778417)
              ·
                refine ⟨69661226561867883001333813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92881635415823844001778417 69661226561867883001333813)
                ·
                  refine ⟨6530739990175114031375045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69661226561867883001333813 6530739990175114031375045)
                  ·
                    refine ⟨1224513748157833880882821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530739990175114031375045 1224513748157833880882821)
                    ·
                      rfl

theorem cell22_3577098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3577098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577098 prefixEnd_3577098 := by exact prefixLift 3577098
  have htrace : WordTrace (prefixWord ++ tailWord_3577098) baseStart_3577098 baseEnd_3577098 := by
    simpa [prefixWord, tailWord_3577098, baseEnd_3577098] using wordTrace_append hprefix tailTrace_3577098
  have hstable : (prefixWord ++ tailWord_3577098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577098).length < 2 ^ (prefixWord ++ tailWord_3577098).sum := by decide
  have hdescent : baseEnd_3577098 < baseStart_3577098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577106 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3577106 : Nat := 118140960795 + 3577106 * 2 ^ 59
def prefixEnd_3577106 : Nat := 4983230072969 + 3 ^ 40 * 3577106 * 2
def baseEnd_3577106 : Nat := 1224516486721324526682797

theorem tailTrace_3577106 : CollatzResearch.WordTrace tailWord_3577106 prefixEnd_3577106 1224516486721324526682797 := by
  unfold tailWord_3577106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32616943544690839477999793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86978516119175571941332781 32616943544690839477999793)
  ·
    refine ⟨24462707658518129608499845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32616943544690839477999793 24462707658518129608499845)
    ·
      refine ⟨4586757685972149301593721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24462707658518129608499845 4586757685972149301593721)
      ·
        refine ⟨3440068264479111976195291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4586757685972149301593721 3440068264479111976195291)
        ·
          refine ⟨5160102396718667964292937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440068264479111976195291 5160102396718667964292937)
          ·
            refine ⟨3870076797539000973219703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160102396718667964292937 3870076797539000973219703)
            ·
              refine ⟨5805115196308501459829555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870076797539000973219703 5805115196308501459829555)
              ·
                refine ⟨8707672794462752189744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805115196308501459829555 8707672794462752189744333)
                ·
                  refine ⟨3265377297923532071154125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8707672794462752189744333 3265377297923532071154125)
                  ·
                    refine ⟨1224516486721324526682797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265377297923532071154125 1224516486721324526682797)
                    ·
                      rfl

theorem cell22_3577106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3577106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577106 prefixEnd_3577106 := by exact prefixLift 3577106
  have htrace : WordTrace (prefixWord ++ tailWord_3577106) baseStart_3577106 baseEnd_3577106 := by
    simpa [prefixWord, tailWord_3577106, baseEnd_3577106] using wordTrace_append hprefix tailTrace_3577106
  have hstable : (prefixWord ++ tailWord_3577106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577106).length < 2 ^ (prefixWord ++ tailWord_3577106).sum := by decide
  have hdescent : baseEnd_3577106 < baseStart_3577106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
