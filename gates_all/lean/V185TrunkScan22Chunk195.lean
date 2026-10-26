import V185TrunkScan22Chunk194

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1737287 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1737287 : Nat := 118140960795 + 1737287 * 2 ^ 59
def prefixEnd_1737287 : Nat := 4983230072969 + 3 ^ 40 * 1737287 * 2
def baseEnd_1737287 : Nat := 594708843871766393548579

theorem tailTrace_1737287 : CollatzResearch.WordTrace tailWord_1737287 prefixEnd_1737287 594708843871766393548579 := by
  unfold tailWord_1737287
  simp only [CollatzResearch.WordTrace]
  refine ⟨63364062457113378842818115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42242708304742252561878743 63364062457113378842818115)
  ·
    refine ⟨95046093685670068264227173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63364062457113378842818115 95046093685670068264227173)
    ·
      refine ⟨17821142566063137799542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95046093685670068264227173 17821142566063137799542595)
      ·
        refine ⟨26731713849094706699313893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17821142566063137799542595 26731713849094706699313893)
        ·
          refine ⟨5012196346705257506121355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26731713849094706699313893 5012196346705257506121355)
          ·
            refine ⟨7518294520057886259182033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012196346705257506121355 7518294520057886259182033)
            ·
              refine ⟨5638720890043414694386525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518294520057886259182033 5638720890043414694386525)
              ·
                refine ⟨2114520333766280510394947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5638720890043414694386525 2114520333766280510394947)
                ·
                  refine ⟨3171780500649420765592421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114520333766280510394947 3171780500649420765592421)
                  ·
                    refine ⟨594708843871766393548579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171780500649420765592421 594708843871766393548579)
                    ·
                      rfl

theorem cell22_1737287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1737287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737287 prefixEnd_1737287 := by exact prefixLift 1737287
  have htrace : WordTrace (prefixWord ++ tailWord_1737287) baseStart_1737287 baseEnd_1737287 := by
    simpa [prefixWord, tailWord_1737287, baseEnd_1737287] using wordTrace_append hprefix tailTrace_1737287
  have hstable : (prefixWord ++ tailWord_1737287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737287).length < 2 ^ (prefixWord ++ tailWord_1737287).sum := by decide
  have hdescent : baseEnd_1737287 < baseStart_1737287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737315 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_1737315 : Nat := 118140960795 + 1737315 * 2 ^ 59
def prefixEnd_1737315 : Nat := 4983230072969 + 3 ^ 40 * 1737315 * 2
def baseEnd_1737315 : Nat := 594718428843983653848493

theorem tailTrace_1737315 : CollatzResearch.WordTrace tailWord_1737315 prefixEnd_1737315 594718428843983653848493 := by
  unfold tailWord_1737315
  simp only [CollatzResearch.WordTrace]
  refine ⟨63365083701011939624837399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42243389134007959749891599 63365083701011939624837399)
  ·
    refine ⟨95047625551517909437256099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63365083701011939624837399 95047625551517909437256099)
    ·
      refine ⟨142571438327276864155884149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95047625551517909437256099 142571438327276864155884149)
      ·
        refine ⟨13366072343182206014614139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142571438327276864155884149 13366072343182206014614139)
        ·
          refine ⟨20049108514773309021921209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13366072343182206014614139 20049108514773309021921209)
          ·
            refine ⟨15036831386079981766440907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20049108514773309021921209 15036831386079981766440907)
            ·
              refine ⟨22555247079119972649661361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036831386079981766440907 22555247079119972649661361)
              ·
                refine ⟨16916435309339979487246021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22555247079119972649661361 16916435309339979487246021)
                ·
                  refine ⟨3171831620501246153858629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16916435309339979487246021 3171831620501246153858629)
                  ·
                    refine ⟨594718428843983653848493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171831620501246153858629 594718428843983653848493)
                    ·
                      rfl

theorem cell22_1737315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_1737315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737315 prefixEnd_1737315 := by exact prefixLift 1737315
  have htrace : WordTrace (prefixWord ++ tailWord_1737315) baseStart_1737315 baseEnd_1737315 := by
    simpa [prefixWord, tailWord_1737315, baseEnd_1737315] using wordTrace_append hprefix tailTrace_1737315
  have hstable : (prefixWord ++ tailWord_1737315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737315).length < 2 ^ (prefixWord ++ tailWord_1737315).sum := by decide
  have hdescent : baseEnd_1737315 < baseStart_1737315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737334 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1737334 : Nat := 118140960795 + 1737334 * 2 ^ 59
def prefixEnd_1737334 : Nat := 4983230072969 + 3 ^ 40 * 1737334 * 2
def baseEnd_1737334 : Nat := 594724932932273937623435

theorem tailTrace_1737334 : CollatzResearch.WordTrace tailWord_1737334 prefixEnd_1737334 594724932932273937623435 := by
  unfold tailWord_1737334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960361042996444116861191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42243851125295403913186037 3960361042996444116861191)
  ·
    refine ⟨5940541564494666175291787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960361042996444116861191 5940541564494666175291787)
    ·
      refine ⟨8910812346741999262937681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940541564494666175291787 8910812346741999262937681)
      ·
        refine ⟨6683109260056499447203261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8910812346741999262937681 6683109260056499447203261)
        ·
          refine ⟨2506165972521187292701223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6683109260056499447203261 2506165972521187292701223)
          ·
            refine ⟨3759248958781780939051835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506165972521187292701223 3759248958781780939051835)
            ·
              refine ⟨5638873438172671408577753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759248958781780939051835 5638873438172671408577753)
              ·
                refine ⟨4229155078629503556433315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638873438172671408577753 4229155078629503556433315)
                ·
                  refine ⟨6343732617944255334649973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229155078629503556433315 6343732617944255334649973)
                  ·
                    refine ⟨594724932932273937623435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6343732617944255334649973 594724932932273937623435)
                    ·
                      rfl

theorem cell22_1737334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1737334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737334 prefixEnd_1737334 := by exact prefixLift 1737334
  have htrace : WordTrace (prefixWord ++ tailWord_1737334) baseStart_1737334 baseEnd_1737334 := by
    simpa [prefixWord, tailWord_1737334, baseEnd_1737334] using wordTrace_append hprefix tailTrace_1737334
  have hstable : (prefixWord ++ tailWord_1737334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737334).length < 2 ^ (prefixWord ++ tailWord_1737334).sum := by decide
  have hdescent : baseEnd_1737334 < baseStart_1737334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737364 : List Nat := [2, 4, 2, 2, 1, 3, 1, 7]
def baseStart_1737364 : Nat := 118140960795 + 1737364 * 2 ^ 59
def prefixEnd_1737364 : Nat := 4983230072969 + 3 ^ 40 * 1737364 * 2
def baseEnd_1737364 : Nat := 66081689171707095485927

theorem tailTrace_1737364 : CollatzResearch.WordTrace tailWord_1737364 prefixEnd_1737364 66081689171707095485927 := by
  unfold tailWord_1737364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31683435438917210496685573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42244580585222947328914097 31683435438917210496685573)
  ·
    refine ⟨5940644144796976968128545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31683435438917210496685573 5940644144796976968128545)
    ·
      refine ⟨4455483108597732726096409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940644144796976968128545 4455483108597732726096409)
      ·
        refine ⟨3341612331448299544572307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4455483108597732726096409 3341612331448299544572307)
        ·
          refine ⟨5012418497172449316858461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341612331448299544572307 5012418497172449316858461)
          ·
            refine ⟨1879656936439668493821923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5012418497172449316858461 1879656936439668493821923)
            ·
              refine ⟨2819485404659502740732885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879656936439668493821923 2819485404659502740732885)
              ·
                refine ⟨66081689171707095485927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2819485404659502740732885 66081689171707095485927)
                ·
                  rfl

theorem cell22_1737364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_1737364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737364 prefixEnd_1737364 := by exact prefixLift 1737364
  have htrace : WordTrace (prefixWord ++ tailWord_1737364) baseStart_1737364 baseEnd_1737364 := by
    simpa [prefixWord, tailWord_1737364, baseEnd_1737364] using wordTrace_append hprefix tailTrace_1737364
  have hstable : (prefixWord ++ tailWord_1737364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737364).length < 2 ^ (prefixWord ++ tailWord_1737364).sum := by decide
  have hdescent : baseEnd_1737364 < baseStart_1737364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737383 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1737383 : Nat := 118140960795 + 1737383 * 2 ^ 59
def prefixEnd_1737383 : Nat := 4983230072969 + 3 ^ 40 * 1737383 * 2
def baseEnd_1737383 : Nat := 594741706633654143148285

theorem tailTrace_1737383 : CollatzResearch.WordTrace tailWord_1737383 prefixEnd_1737383 594741706633654143148285 := by
  unfold tailWord_1737383
  simp only [CollatzResearch.WordTrace]
  refine ⟨63367563864765587238312803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42245042576510391492208535 63367563864765587238312803)
  ·
    refine ⟨95051345797148380857469205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63367563864765587238312803 95051345797148380857469205)
    ·
      refine ⟨4455531834241330352693869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95051345797148380857469205 4455531834241330352693869)
      ·
        refine ⟨1670824437840498882260201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4455531834241330352693869 1670824437840498882260201)
        ·
          refine ⟨1253118328380374161695151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670824437840498882260201 1253118328380374161695151)
          ·
            refine ⟨1879677492570561242542727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253118328380374161695151 1879677492570561242542727)
            ·
              refine ⟨2819516238855841863814091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879677492570561242542727 2819516238855841863814091)
              ·
                refine ⟨4229274358283762795721137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819516238855841863814091 4229274358283762795721137)
                ·
                  refine ⟨3171955768712822096790853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229274358283762795721137 3171955768712822096790853)
                  ·
                    refine ⟨594741706633654143148285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171955768712822096790853 594741706633654143148285)
                    ·
                      rfl

theorem cell22_1737383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1737383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737383 prefixEnd_1737383 := by exact prefixLift 1737383
  have htrace : WordTrace (prefixWord ++ tailWord_1737383) baseStart_1737383 baseEnd_1737383 := by
    simpa [prefixWord, tailWord_1737383, baseEnd_1737383] using wordTrace_append hprefix tailTrace_1737383
  have hstable : (prefixWord ++ tailWord_1737383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737383).length < 2 ^ (prefixWord ++ tailWord_1737383).sum := by decide
  have hdescent : baseEnd_1737383 < baseStart_1737383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737426 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1737426 : Nat := 118140960795 + 1737426 * 2 ^ 59
def prefixEnd_1737426 : Nat := 4983230072969 + 3 ^ 40 * 1737426 * 2
def baseEnd_1737426 : Nat := 198252142137472121441051

theorem tailTrace_1737426 : CollatzResearch.WordTrace tailWord_1737426 prefixEnd_1737426 198252142137472121441051 := by
  unfold tailWord_1737426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842283050902451395532033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42246088135739870388085421 15842283050902451395532033)
  ·
    refine ⟨11881712288176838546649025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15842283050902451395532033 11881712288176838546649025)
    ·
      refine ⟨8911284216132628909986769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11881712288176838546649025 8911284216132628909986769)
      ·
        refine ⟨6683463162099471682490077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8911284216132628909986769 6683463162099471682490077)
        ·
          refine ⟨2506298685787301880933779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6683463162099471682490077 2506298685787301880933779)
          ·
            refine ⟨3759448028680952821400669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506298685787301880933779 3759448028680952821400669)
            ·
              refine ⟨1409793010755357308025251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3759448028680952821400669 1409793010755357308025251)
              ·
                refine ⟨2114689516133035962037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409793010755357308025251 2114689516133035962037877)
                ·
                  refine ⟨198252142137472121441051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2114689516133035962037877 198252142137472121441051)
                  ·
                    rfl

theorem cell22_1737426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1737426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737426 prefixEnd_1737426 := by exact prefixLift 1737426
  have htrace : WordTrace (prefixWord ++ tailWord_1737426) baseStart_1737426 baseEnd_1737426 := by
    simpa [prefixWord, tailWord_1737426, baseEnd_1737426] using wordTrace_append hprefix tailTrace_1737426
  have hstable : (prefixWord ++ tailWord_1737426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737426).length < 2 ^ (prefixWord ++ tailWord_1737426).sum := by decide
  have hdescent : baseEnd_1737426 < baseStart_1737426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737435 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_1737435 : Nat := 118140960795 + 1737435 * 2 ^ 59
def prefixEnd_1737435 : Nat := 4983230072969 + 3 ^ 40 * 1737435 * 2
def baseEnd_1737435 : Nat := 594759507296343340848125

theorem tailTrace_1737435 : CollatzResearch.WordTrace tailWord_1737435 prefixEnd_1737435 594759507296343340848125 := by
  unfold tailWord_1737435
  simp only [CollatzResearch.WordTrace]
  refine ⟨63369460460577200119205759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42246306973718133412803839 63369460460577200119205759)
  ·
    refine ⟨95054190690865800178808639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63369460460577200119205759 95054190690865800178808639)
    ·
      refine ⟨142581286036298700268212959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95054190690865800178808639 142581286036298700268212959)
      ·
        refine ⟨213871929054448050402319439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142581286036298700268212959 213871929054448050402319439)
        ·
          refine ⟨320807893581672075603479159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213871929054448050402319439 320807893581672075603479159)
          ·
            refine ⟨481211840372508113405218739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320807893581672075603479159 481211840372508113405218739)
            ·
              refine ⟨721817760558762170107828109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481211840372508113405218739 721817760558762170107828109)
              ·
                refine ⟨270681660209535813790435541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721817760558762170107828109 270681660209535813790435541)
                ·
                  refine ⟨6344101411160995635713333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 270681660209535813790435541 6344101411160995635713333)
                  ·
                    refine ⟨594759507296343340848125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6344101411160995635713333 594759507296343340848125)
                    ·
                      rfl

theorem cell22_1737435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_1737435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737435 prefixEnd_1737435 := by exact prefixLift 1737435
  have htrace : WordTrace (prefixWord ++ tailWord_1737435) baseStart_1737435 baseEnd_1737435 := by
    simpa [prefixWord, tailWord_1737435, baseEnd_1737435] using wordTrace_append hprefix tailTrace_1737435
  have hstable : (prefixWord ++ tailWord_1737435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737435).length < 2 ^ (prefixWord ++ tailWord_1737435).sum := by decide
  have hdescent : baseEnd_1737435 < baseStart_1737435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737439 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 1, 4]
def baseStart_1737439 : Nat := 118140960795 + 1737439 * 2 ^ 59
def prefixEnd_1737439 : Nat := 4983230072969 + 3 ^ 40 * 1737439 * 2
def baseEnd_1737439 : Nat := 594760876578088663748113

theorem tailTrace_1737439 : CollatzResearch.WordTrace tailWord_1737439 prefixEnd_1737439 594760876578088663748113 := by
  unfold tailWord_1737439
  simp only [CollatzResearch.WordTrace]
  refine ⟨63369606352562708802351371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42246404235041805868234247 63369606352562708802351371)
  ·
    refine ⟨95054409528844063203527057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63369606352562708802351371 95054409528844063203527057)
    ·
      refine ⟨71290807146633047402645293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95054409528844063203527057 71290807146633047402645293)
      ·
        refine ⟨26734052679987392775991985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71290807146633047402645293 26734052679987392775991985)
        ·
          refine ⟨20050539509990544581993989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26734052679987392775991985 20050539509990544581993989)
          ·
            refine ⟨3759476158123227109123873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20050539509990544581993989 3759476158123227109123873)
            ·
              refine ⟨2819607118592420331842905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759476158123227109123873 2819607118592420331842905)
              ·
                refine ⟨2114705338944315248882179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819607118592420331842905 2114705338944315248882179)
                ·
                  refine ⟨3172058008416472873323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114705338944315248882179 3172058008416472873323269)
                  ·
                    refine ⟨594760876578088663748113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3172058008416472873323269 594760876578088663748113)
                    ·
                      rfl

theorem cell22_1737439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_1737439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737439 prefixEnd_1737439 := by exact prefixLift 1737439
  have htrace : WordTrace (prefixWord ++ tailWord_1737439) baseStart_1737439 baseEnd_1737439 := by
    simpa [prefixWord, tailWord_1737439, baseEnd_1737439] using wordTrace_append hprefix tailTrace_1737439
  have hstable : (prefixWord ++ tailWord_1737439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737439).length < 2 ^ (prefixWord ++ tailWord_1737439).sum := by decide
  have hdescent : baseEnd_1737439 < baseStart_1737439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737469 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1737469 : Nat := 118140960795 + 1737469 * 2 ^ 59
def prefixEnd_1737469 : Nat := 4983230072969 + 3 ^ 40 * 1737469 * 2
def baseEnd_1737469 : Nat := 594771146191178585498021

theorem tailTrace_1737469 : CollatzResearch.WordTrace tailWord_1737469 prefixEnd_1737469 594771146191178585498021 := by
  unfold tailWord_1737469
  simp only [CollatzResearch.WordTrace]
  refine ⟨63370700542454023925943461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42247133694969349283962307 63370700542454023925943461)
  ·
    refine ⟨11882006351710129486114399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63370700542454023925943461 11882006351710129486114399)
    ·
      refine ⟨17823009527565194229171599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882006351710129486114399 17823009527565194229171599)
      ·
        refine ⟨26734514291347791343757399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17823009527565194229171599 26734514291347791343757399)
        ·
          refine ⟨40101771437021687015636099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26734514291347791343757399 40101771437021687015636099)
          ·
            refine ⟨60152657155532530523454149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40101771437021687015636099 60152657155532530523454149)
            ·
              refine ⟨11278623216662349473147653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60152657155532530523454149 11278623216662349473147653)
              ·
                refine ⟨2114741853124190526215185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11278623216662349473147653 2114741853124190526215185)
                ·
                  refine ⟨1586056389843142894661389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114741853124190526215185 1586056389843142894661389)
                  ·
                    refine ⟨594771146191178585498021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586056389843142894661389 594771146191178585498021)
                    ·
                      rfl

theorem cell22_1737469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1737469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737469 prefixEnd_1737469 := by exact prefixLift 1737469
  have htrace : WordTrace (prefixWord ++ tailWord_1737469) baseStart_1737469 baseEnd_1737469 := by
    simpa [prefixWord, tailWord_1737469, baseEnd_1737469] using wordTrace_append hprefix tailTrace_1737469
  have hstable : (prefixWord ++ tailWord_1737469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737469).length < 2 ^ (prefixWord ++ tailWord_1737469).sum := by decide
  have hdescent : baseEnd_1737469 < baseStart_1737469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737482 : List Nat := [3, 1, 2, 2, 1, 2, 4, 7]
def baseStart_1737482 : Nat := 118140960795 + 1737482 * 2 ^ 59
def prefixEnd_1737482 : Nat := 4983230072969 + 3 ^ 40 * 1737482 * 2
def baseEnd_1737482 : Nat := 66086177372983431658109

theorem tailTrace_1737482 : CollatzResearch.WordTrace tailWord_1737482 prefixEnd_1737482 66086177372983431658109 := by
  unfold tailWord_1737482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842793672851731786541675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42247449794271284764111133 15842793672851731786541675)
  ·
    refine ⟨23764190509277597679812513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15842793672851731786541675 23764190509277597679812513)
    ·
      refine ⟨17823142881958198259859385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23764190509277597679812513 17823142881958198259859385)
      ·
        refine ⟨13367357161468648694894539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17823142881958198259859385 13367357161468648694894539)
        ·
          refine ⟨20051035742202973042341809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367357161468648694894539 20051035742202973042341809)
          ·
            refine ⟨15038276806652229781756357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20051035742202973042341809 15038276806652229781756357)
            ·
              refine ⟨2819676901247293084079317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15038276806652229781756357 2819676901247293084079317)
              ·
                refine ⟨66086177372983431658109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2819676901247293084079317 66086177372983431658109)
                ·
                  rfl

theorem cell22_1737482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_1737482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737482 prefixEnd_1737482 := by exact prefixLift 1737482
  have htrace : WordTrace (prefixWord ++ tailWord_1737482) baseStart_1737482 baseEnd_1737482 := by
    simpa [prefixWord, tailWord_1737482, baseEnd_1737482] using wordTrace_append hprefix tailTrace_1737482
  have hstable : (prefixWord ++ tailWord_1737482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737482).length < 2 ^ (prefixWord ++ tailWord_1737482).sum := by decide
  have hdescent : baseEnd_1737482 < baseStart_1737482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737490 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1737490 : Nat := 118140960795 + 1737490 * 2 ^ 59
def prefixEnd_1737490 : Nat := 4983230072969 + 3 ^ 40 * 1737490 * 2
def baseEnd_1737490 : Nat := 594778334920341530722957

theorem tailTrace_1737490 : CollatzResearch.WordTrace tailWord_1737490 prefixEnd_1737490 594778334920341530722957 := by
  unfold tailWord_1737490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842866618844486128114481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42247644316918629674971949 15842866618844486128114481)
  ·
    refine ⟨11882149964133364596085861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15842866618844486128114481 11882149964133364596085861)
    ·
      refine ⟨2227903118275005861766099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11882149964133364596085861 2227903118275005861766099)
      ·
        refine ⟨3341854677412508792649149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227903118275005861766099 3341854677412508792649149)
        ·
          refine ⟨1253195504029690797243431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3341854677412508792649149 1253195504029690797243431)
          ·
            refine ⟨1879793256044536195865147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253195504029690797243431 1879793256044536195865147)
            ·
              refine ⟨2819689884066804293797721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879793256044536195865147 2819689884066804293797721)
              ·
                refine ⟨2114767413050103220348291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819689884066804293797721 2114767413050103220348291)
                ·
                  refine ⟨3172151119575154830522437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114767413050103220348291 3172151119575154830522437)
                  ·
                    refine ⟨594778334920341530722957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3172151119575154830522437 594778334920341530722957)
                    ·
                      rfl

theorem cell22_1737490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1737490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737490 prefixEnd_1737490 := by exact prefixLift 1737490
  have htrace : WordTrace (prefixWord ++ tailWord_1737490) baseStart_1737490 baseEnd_1737490 := by
    simpa [prefixWord, tailWord_1737490, baseEnd_1737490] using wordTrace_append hprefix tailTrace_1737490
  have hstable : (prefixWord ++ tailWord_1737490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737490).length < 2 ^ (prefixWord ++ tailWord_1737490).sum := by decide
  have hdescent : baseEnd_1737490 < baseStart_1737490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737587 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_1737587 : Nat := 118140960795 + 1737587 * 2 ^ 59
def prefixEnd_1737587 : Nat := 4983230072969 + 3 ^ 40 * 1737587 * 2
def baseEnd_1737587 : Nat := 594811540002665611047659

theorem tailTrace_1737587 : CollatzResearch.WordTrace tailWord_1737587 prefixEnd_1737587 594811540002665611047659 := by
  unfold tailWord_1737587
  simp only [CollatzResearch.WordTrace]
  refine ⟨63375004356026530078739015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42250002904017686719159343 63375004356026530078739015)
  ·
    refine ⟨95062506534039795118108523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63375004356026530078739015 95062506534039795118108523)
    ·
      refine ⟨142593759801059692677162785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95062506534039795118108523 142593759801059692677162785)
      ·
        refine ⟨106945319850794769507872089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142593759801059692677162785 106945319850794769507872089)
        ·
          refine ⟨80208989888096077130904067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106945319850794769507872089 80208989888096077130904067)
          ·
            refine ⟨120313484832144115696356101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80208989888096077130904067 120313484832144115696356101)
            ·
              refine ⟨22558778406027021693066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120313484832144115696356101 22558778406027021693066769)
              ·
                refine ⟨16919083804520266269800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22558778406027021693066769 16919083804520266269800077)
                ·
                  refine ⟨6344656426695099851175029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16919083804520266269800077 6344656426695099851175029)
                  ·
                    refine ⟨594811540002665611047659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6344656426695099851175029 594811540002665611047659)
                    ·
                      rfl

theorem cell22_1737587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_1737587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737587 prefixEnd_1737587 := by exact prefixLift 1737587
  have htrace : WordTrace (prefixWord ++ tailWord_1737587) baseStart_1737587 baseEnd_1737587 := by
    simpa [prefixWord, tailWord_1737587, baseEnd_1737587] using wordTrace_append hprefix tailTrace_1737587
  have hstable : (prefixWord ++ tailWord_1737587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737587).length < 2 ^ (prefixWord ++ tailWord_1737587).sum := by decide
  have hdescent : baseEnd_1737587 < baseStart_1737587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737589 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1737589 : Nat := 118140960795 + 1737589 * 2 ^ 59
def prefixEnd_1737589 : Nat := 4983230072969 + 3 ^ 40 * 1737589 * 2
def baseEnd_1737589 : Nat := 198270741547846090832551

theorem tailTrace_1737589 : CollatzResearch.WordTrace tailWord_1737589 prefixEnd_1737589 198270741547846090832551 := by
  unfold tailWord_1737589
  simp only [CollatzResearch.WordTrace]
  refine ⟨63375077302019284420311821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42250051534679522946874547 63375077302019284420311821)
  ·
    refine ⟨23765653988257231657616933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63375077302019284420311821 23765653988257231657616933)
    ·
      refine ⟨4456060122798230935803175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23765653988257231657616933 4456060122798230935803175)
      ·
        refine ⟨6684090184197346403704763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456060122798230935803175 6684090184197346403704763)
        ·
          refine ⟨10026135276296019605557145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684090184197346403704763 10026135276296019605557145)
          ·
            refine ⟨7519601457222014704167859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10026135276296019605557145 7519601457222014704167859)
            ·
              refine ⟨11279402185833022056251789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519601457222014704167859 11279402185833022056251789)
              ·
                refine ⟨4229775819687383271094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11279402185833022056251789 4229775819687383271094421)
                ·
                  refine ⟨198270741547846090832551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4229775819687383271094421 198270741547846090832551)
                  ·
                    rfl

theorem cell22_1737589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1737589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737589 prefixEnd_1737589 := by exact prefixLift 1737589
  have htrace : WordTrace (prefixWord ++ tailWord_1737589) baseStart_1737589 baseEnd_1737589 := by
    simpa [prefixWord, tailWord_1737589, baseEnd_1737589] using wordTrace_append hprefix tailTrace_1737589
  have hstable : (prefixWord ++ tailWord_1737589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737589).length < 2 ^ (prefixWord ++ tailWord_1737589).sum := by decide
  have hdescent : baseEnd_1737589 < baseStart_1737589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737634 : List Nat := [3, 3, 1, 2, 2, 1, 10]
def baseStart_1737634 : Nat := 118140960795 + 1737634 * 2 ^ 59
def prefixEnd_1737634 : Nat := 4983230072969 + 3 ^ 40 * 1737634 * 2
def baseEnd_1737634 : Nat := 22030652928265672411945

theorem tailTrace_1737634 : CollatzResearch.WordTrace tailWord_1737634 prefixEnd_1737634 22030652928265672411945 := by
  unfold tailWord_1737634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844179646714064276424989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42251145724570838070466637 15844179646714064276424989)
  ·
    refine ⟨5941567367517774103659371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15844179646714064276424989 5941567367517774103659371)
    ·
      refine ⟨8912351051276661155489057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5941567367517774103659371 8912351051276661155489057)
      ·
        refine ⟨6684263288457495866616793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912351051276661155489057 6684263288457495866616793)
        ·
          refine ⟨5013197466343121899962595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684263288457495866616793 5013197466343121899962595)
          ·
            refine ⟨7519796199514682849943893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013197466343121899962595 7519796199514682849943893)
            ·
              refine ⟨22030652928265672411945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7519796199514682849943893 22030652928265672411945)
              ·
                rfl

theorem cell22_1737634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 10].length) (baseStart_1737634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737634 prefixEnd_1737634 := by exact prefixLift 1737634
  have htrace : WordTrace (prefixWord ++ tailWord_1737634) baseStart_1737634 baseEnd_1737634 := by
    simpa [prefixWord, tailWord_1737634, baseEnd_1737634] using wordTrace_append hprefix tailTrace_1737634
  have hstable : (prefixWord ++ tailWord_1737634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737634).length < 2 ^ (prefixWord ++ tailWord_1737634).sum := by decide
  have hdescent : baseEnd_1737634 < baseStart_1737634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737724 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_1737724 : Nat := 118140960795 + 1737724 * 2 ^ 59
def prefixEnd_1737724 : Nat := 4983230072969 + 3 ^ 40 * 1737724 * 2
def baseEnd_1737724 : Nat := 198286145967480973457413

theorem tailTrace_1737724 : CollatzResearch.WordTrace tailWord_1737724 prefixEnd_1737724 198286145967480973457413 := by
  unfold tailWord_1737724
  simp only [CollatzResearch.WordTrace]
  refine ⟨31690000578265101238238113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42253334104353468317650817 31690000578265101238238113)
  ·
    refine ⟨23767500433698825928678585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31690000578265101238238113 23767500433698825928678585)
    ·
      refine ⟨17825625325274119446508939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23767500433698825928678585 17825625325274119446508939)
      ·
        refine ⟨26738437987911179169763409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17825625325274119446508939 26738437987911179169763409)
        ·
          refine ⟨20053828490933384377322557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26738437987911179169763409 20053828490933384377322557)
          ·
            refine ⟨7520185684100019141495959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20053828490933384377322557 7520185684100019141495959)
            ·
              refine ⟨11280278526150028712243939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520185684100019141495959 11280278526150028712243939)
              ·
                refine ⟨16920417789225043068365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11280278526150028712243939 16920417789225043068365909)
                ·
                  refine ⟨198286145967480973457413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16920417789225043068365909 198286145967480973457413)
                  ·
                    rfl

theorem cell22_1737724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_1737724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737724 prefixEnd_1737724 := by exact prefixLift 1737724
  have htrace : WordTrace (prefixWord ++ tailWord_1737724) baseStart_1737724 baseEnd_1737724 := by
    simpa [prefixWord, tailWord_1737724, baseEnd_1737724] using wordTrace_append hprefix tailTrace_1737724
  have hstable : (prefixWord ++ tailWord_1737724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737724).length < 2 ^ (prefixWord ++ tailWord_1737724).sum := by decide
  have hdescent : baseEnd_1737724 < baseStart_1737724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737786 : List Nat := [3, 1, 1, 1, 3, 1, 6, 6]
def baseStart_1737786 : Nat := 118140960795 + 1737786 * 2 ^ 59
def prefixEnd_1737786 : Nat := 4983230072969 + 3 ^ 40 * 1737786 * 2
def baseEnd_1737786 : Nat := 66097740196610602813561

theorem tailTrace_1737786 : CollatzResearch.WordTrace tailWord_1737786 prefixEnd_1737786 66097740196610602813561 := by
  unfold tailWord_1737786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845565620576396766308303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42254841654870391376822141 15845565620576396766308303)
  ·
    refine ⟨23768348430864595149462455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15845565620576396766308303 23768348430864595149462455)
    ·
      refine ⟨35652522646296892724193683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23768348430864595149462455 35652522646296892724193683)
      ·
        refine ⟨53478783969445339086290525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35652522646296892724193683 53478783969445339086290525)
        ·
          refine ⟨20054543988542002157358947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53478783969445339086290525 20054543988542002157358947)
          ·
            refine ⟨30081815982813003236038421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20054543988542002157358947 30081815982813003236038421)
            ·
              refine ⟨1410085124194359526689301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30081815982813003236038421 1410085124194359526689301)
              ·
                refine ⟨66097740196610602813561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1410085124194359526689301 66097740196610602813561)
                ·
                  rfl

theorem cell22_1737786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_1737786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737786 prefixEnd_1737786 := by exact prefixLift 1737786
  have htrace : WordTrace (prefixWord ++ tailWord_1737786) baseStart_1737786 baseEnd_1737786 := by
    simpa [prefixWord, tailWord_1737786, baseEnd_1737786] using wordTrace_append hprefix tailTrace_1737786
  have hstable : (prefixWord ++ tailWord_1737786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737786).length < 2 ^ (prefixWord ++ tailWord_1737786).sum := by decide
  have hdescent : baseEnd_1737786 < baseStart_1737786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737951 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1737951 : Nat := 118140960795 + 1737951 * 2 ^ 59
def prefixEnd_1737951 : Nat := 4983230072969 + 3 ^ 40 * 1737951 * 2
def baseEnd_1737951 : Nat := 594936144641489994946543

theorem tailTrace_1737951 : CollatzResearch.WordTrace tailWord_1737951 prefixEnd_1737951 594936144641489994946543 := by
  unfold tailWord_1737951
  simp only [CollatzResearch.WordTrace]
  refine ⟨63388280526707820244989707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42258853684471880163326471 63388280526707820244989707)
  ·
    refine ⟨95082420790061730367484561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63388280526707820244989707 95082420790061730367484561)
    ·
      refine ⟨71311815592546297775613421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95082420790061730367484561 71311815592546297775613421)
      ·
        refine ⟨26741930847204861665855033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71311815592546297775613421 26741930847204861665855033)
        ·
          refine ⟨20056448135403646249391275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26741930847204861665855033 20056448135403646249391275)
          ·
            refine ⟨30084672203105469374086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056448135403646249391275 30084672203105469374086913)
            ·
              refine ⟨22563504152329102030565185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30084672203105469374086913 22563504152329102030565185)
              ·
                refine ⟨16922628114246826522923889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22563504152329102030565185 16922628114246826522923889)
                ·
                  refine ⟨12691971085685119892192917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16922628114246826522923889 12691971085685119892192917)
                  ·
                    refine ⟨594936144641489994946543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12691971085685119892192917 594936144641489994946543)
                    ·
                      rfl

theorem cell22_1737951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1737951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1737951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1737951 prefixEnd_1737951 := by exact prefixLift 1737951
  have htrace : WordTrace (prefixWord ++ tailWord_1737951) baseStart_1737951 baseEnd_1737951 := by
    simpa [prefixWord, tailWord_1737951, baseEnd_1737951] using wordTrace_append hprefix tailTrace_1737951
  have hstable : (prefixWord ++ tailWord_1737951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737951).length < 2 ^ (prefixWord ++ tailWord_1737951).sum := by decide
  have hdescent : baseEnd_1737951 < baseStart_1737951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738011 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 8]
def baseStart_1738011 : Nat := 118140960795 + 1738011 * 2 ^ 59
def prefixEnd_1738011 : Nat := 4983230072969 + 3 ^ 40 * 1738011 * 2
def baseEnd_1738011 : Nat := 198318894622556612815453

theorem tailTrace_1738011 : CollatzResearch.WordTrace tailWord_1738011 prefixEnd_1738011 198318894622556612815453 := by
  unfold tailWord_1738011
  simp only [CollatzResearch.WordTrace]
  refine ⟨63390468906490450492173887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42260312604326966994782591 63390468906490450492173887)
  ·
    refine ⟨95085703359735675738260831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63390468906490450492173887 95085703359735675738260831)
    ·
      refine ⟨142628555039603513607391247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95085703359735675738260831 142628555039603513607391247)
      ·
        refine ⟨213942832559405270411086871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142628555039603513607391247 213942832559405270411086871)
        ·
          refine ⟨320914248839107905616630307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213942832559405270411086871 320914248839107905616630307)
          ·
            refine ⟨481371373258661858424945461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320914248839107905616630307 481371373258661858424945461)
            ·
              refine ⟨45128566242999549227338637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481371373258661858424945461 45128566242999549227338637)
              ·
                refine ⟨16923212341124830960251989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45128566242999549227338637 16923212341124830960251989)
                ·
                  refine ⟨198318894622556612815453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16923212341124830960251989 198318894622556612815453)
                  ·
                    rfl

theorem cell22_1738011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_1738011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738011 prefixEnd_1738011 := by exact prefixLift 1738011
  have htrace : WordTrace (prefixWord ++ tailWord_1738011) baseStart_1738011 baseEnd_1738011 := by
    simpa [prefixWord, tailWord_1738011, baseEnd_1738011] using wordTrace_append hprefix tailTrace_1738011
  have hstable : (prefixWord ++ tailWord_1738011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738011).length < 2 ^ (prefixWord ++ tailWord_1738011).sum := by decide
  have hdescent : baseEnd_1738011 < baseStart_1738011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738043 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 10, 3]
def baseStart_1738043 : Nat := 118140960795 + 1738043 * 2 ^ 59
def prefixEnd_1738043 : Nat := 4983230072969 + 3 ^ 40 * 1738043 * 2
def baseEnd_1738043 : Nat := 594967638121632421646261

theorem tailTrace_1738043 : CollatzResearch.WordTrace tailWord_1738043 prefixEnd_1738043 594967638121632421646261 := by
  unfold tailWord_1738043
  simp only [CollatzResearch.WordTrace]
  refine ⟨63391636042374519957338783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42261090694916346638225855 63391636042374519957338783)
  ·
    refine ⟨95087454063561779936008175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63391636042374519957338783 95087454063561779936008175)
    ·
      refine ⟨142631181095342669904012263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95087454063561779936008175 142631181095342669904012263)
      ·
        refine ⟨213946771643014004856018395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142631181095342669904012263 213946771643014004856018395)
        ·
          refine ⟨320920157464521007284027593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213946771643014004856018395 320920157464521007284027593)
          ·
            refine ⟨240690118098390755463020695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320920157464521007284027593 240690118098390755463020695)
            ·
              refine ⟨361035177147586133194531043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240690118098390755463020695 361035177147586133194531043)
              ·
                refine ⟨541552765721379199791796565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361035177147586133194531043 541552765721379199791796565)
                ·
                  refine ⟨1586580368324353124390029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 541552765721379199791796565 1586580368324353124390029)
                  ·
                    refine ⟨594967638121632421646261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586580368324353124390029 594967638121632421646261)
                    ·
                      rfl

theorem cell22_1738043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].length) (baseStart_1738043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738043 prefixEnd_1738043 := by exact prefixLift 1738043
  have htrace : WordTrace (prefixWord ++ tailWord_1738043) baseStart_1738043 baseEnd_1738043 := by
    simpa [prefixWord, tailWord_1738043, baseEnd_1738043] using wordTrace_append hprefix tailTrace_1738043
  have hstable : (prefixWord ++ tailWord_1738043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738043).length < 2 ^ (prefixWord ++ tailWord_1738043).sum := by decide
  have hdescent : baseEnd_1738043 < baseStart_1738043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738058 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1738058 : Nat := 118140960795 + 1738058 * 2 ^ 59
def prefixEnd_1738058 : Nat := 4983230072969 + 3 ^ 40 * 1738058 * 2
def baseEnd_1738058 : Nat := 594972772928177382521215

theorem tailTrace_1738058 : CollatzResearch.WordTrace tailWord_1738058 prefixEnd_1738058 594972772928177382521215 := by
  unfold tailWord_1738058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848045784330044379783707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42261455424880118346089885 15848045784330044379783707)
  ·
    refine ⟨23772068676495066569675561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15848045784330044379783707 23772068676495066569675561)
    ·
      refine ⟨17829051507371299927256671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23772068676495066569675561 17829051507371299927256671)
      ·
        refine ⟨26743577261056949890885007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17829051507371299927256671 26743577261056949890885007)
        ·
          refine ⟨40115365891585424836327511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743577261056949890885007 40115365891585424836327511)
          ·
            refine ⟨60173048837378137254491267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40115365891585424836327511 60173048837378137254491267)
            ·
              refine ⟨90259573256067205881736901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60173048837378137254491267 90259573256067205881736901)
              ·
                refine ⟨16923669985512601102825669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90259573256067205881736901 16923669985512601102825669)
                ·
                  refine ⟨3173188122283612706779813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16923669985512601102825669 3173188122283612706779813)
                  ·
                    refine ⟨594972772928177382521215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173188122283612706779813 594972772928177382521215)
                    ·
                      rfl

theorem cell22_1738058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1738058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738058 prefixEnd_1738058 := by exact prefixLift 1738058
  have htrace : WordTrace (prefixWord ++ tailWord_1738058) baseStart_1738058 baseEnd_1738058 := by
    simpa [prefixWord, tailWord_1738058, baseEnd_1738058] using wordTrace_append hprefix tailTrace_1738058
  have hstable : (prefixWord ++ tailWord_1738058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738058).length < 2 ^ (prefixWord ++ tailWord_1738058).sum := by decide
  have hdescent : baseEnd_1738058 < baseStart_1738058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738060 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1738060 : Nat := 118140960795 + 1738060 * 2 ^ 59
def prefixEnd_1738060 : Nat := 4983230072969 + 3 ^ 40 * 1738060 * 2
def baseEnd_1738060 : Nat := 594973457569050043971209

theorem tailTrace_1738060 : CollatzResearch.WordTrace tailWord_1738060 prefixEnd_1738060 594973457569050043971209 := by
  unfold tailWord_1738060
  simp only [CollatzResearch.WordTrace]
  refine ⟨31696128041656465930353817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42261504055541954573805089 31696128041656465930353817)
  ·
    refine ⟨23772096031242349447765363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31696128041656465930353817 23772096031242349447765363)
    ·
      refine ⟨35658144046863524171648045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23772096031242349447765363 35658144046863524171648045)
      ·
        refine ⟨13371804017573821564368017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35658144046863524171648045 13371804017573821564368017)
        ·
          refine ⟨10028853013180366173276013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371804017573821564368017 10028853013180366173276013)
          ·
            refine ⟨3760819879942637314978505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10028853013180366173276013 3760819879942637314978505)
            ·
              refine ⟨2820614909956977986233879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760819879942637314978505 2820614909956977986233879)
              ·
                refine ⟨4230922364935466979350819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820614909956977986233879 4230922364935466979350819)
                ·
                  refine ⟨6346383547403200469026229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230922364935466979350819 6346383547403200469026229)
                  ·
                    refine ⟨594973457569050043971209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6346383547403200469026229 594973457569050043971209)
                    ·
                      rfl

theorem cell22_1738060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1738060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738060 prefixEnd_1738060 := by exact prefixLift 1738060
  have htrace : WordTrace (prefixWord ++ tailWord_1738060) baseStart_1738060 baseEnd_1738060 := by
    simpa [prefixWord, tailWord_1738060, baseEnd_1738060] using wordTrace_append hprefix tailTrace_1738060
  have hstable : (prefixWord ++ tailWord_1738060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738060).length < 2 ^ (prefixWord ++ tailWord_1738060).sum := by decide
  have hdescent : baseEnd_1738060 < baseStart_1738060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738090 : List Nat := [3, 1, 3, 3, 2, 1, 9]
def baseStart_1738090 : Nat := 118140960795 + 1738090 * 2 ^ 59
def prefixEnd_1738090 : Nat := 4983230072969 + 3 ^ 40 * 1738090 * 2
def baseEnd_1738090 : Nat := 22036434340079257989671

theorem tailTrace_1738090 : CollatzResearch.WordTrace tailWord_1738090 prefixEnd_1738090 22036434340079257989671 := by
  unfold tailWord_1738090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848337568301061746074931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42262233515469497989533149 15848337568301061746074931)
  ·
    refine ⟨23772506352451592619112397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15848337568301061746074931 23772506352451592619112397)
    ·
      refine ⟨8914689882169347232167149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23772506352451592619112397 8914689882169347232167149)
      ·
        refine ⟨3343008705813505212062681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8914689882169347232167149 3343008705813505212062681)
        ·
          refine ⟨2507256529360128909047011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343008705813505212062681 2507256529360128909047011)
          ·
            refine ⟨3760884794040193363570517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507256529360128909047011 3760884794040193363570517)
            ·
              refine ⟨22036434340079257989671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3760884794040193363570517 22036434340079257989671)
              ·
                rfl

theorem cell22_1738090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 9].length) (baseStart_1738090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738090 prefixEnd_1738090 := by exact prefixLift 1738090
  have htrace : WordTrace (prefixWord ++ tailWord_1738090) baseStart_1738090 baseEnd_1738090 := by
    simpa [prefixWord, tailWord_1738090, baseEnd_1738090] using wordTrace_append hprefix tailTrace_1738090
  have hstable : (prefixWord ++ tailWord_1738090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738090).length < 2 ^ (prefixWord ++ tailWord_1738090).sum := by decide
  have hdescent : baseEnd_1738090 < baseStart_1738090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738094 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1738094 : Nat := 118140960795 + 1738094 * 2 ^ 59
def prefixEnd_1738094 : Nat := 4983230072969 + 3 ^ 40 * 1738094 * 2
def baseEnd_1738094 : Nat := 594985096463885288621105

theorem tailTrace_1738094 : CollatzResearch.WordTrace tailWord_1738094 prefixEnd_1738094 594985096463885288621105 := by
  unfold tailWord_1738094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924187020648719458430667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42262330776793170444963557 7924187020648719458430667)
  ·
    refine ⟨11886280530973079187646001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7924187020648719458430667 11886280530973079187646001)
    ·
      refine ⟨8914710398229809390734501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11886280530973079187646001 8914710398229809390734501)
      ·
        refine ⟨1671508199668089260762719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8914710398229809390734501 1671508199668089260762719)
        ·
          refine ⟨2507262299502133891144079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671508199668089260762719 2507262299502133891144079)
          ·
            refine ⟨3760893449253200836716119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507262299502133891144079 3760893449253200836716119)
            ·
              refine ⟨5641340173879801255074179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760893449253200836716119 5641340173879801255074179)
              ·
                refine ⟨8462010260819701882611269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641340173879801255074179 8462010260819701882611269)
                ·
                  refine ⟨1586626923903694102989613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8462010260819701882611269 1586626923903694102989613)
                  ·
                    refine ⟨594985096463885288621105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586626923903694102989613 594985096463885288621105)
                    ·
                      rfl

theorem cell22_1738094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1738094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738094 prefixEnd_1738094 := by exact prefixLift 1738094
  have htrace : WordTrace (prefixWord ++ tailWord_1738094) baseStart_1738094 baseEnd_1738094 := by
    simpa [prefixWord, tailWord_1738094, baseEnd_1738094] using wordTrace_append hprefix tailTrace_1738094
  have hstable : (prefixWord ++ tailWord_1738094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738094).length < 2 ^ (prefixWord ++ tailWord_1738094).sum := by decide
  have hdescent : baseEnd_1738094 < baseStart_1738094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738105 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_1738105 : Nat := 118140960795 + 1738105 * 2 ^ 59
def prefixEnd_1738105 : Nat := 4983230072969 + 3 ^ 40 * 1738105 * 2
def baseEnd_1738105 : Nat := 594988861988684926596071

theorem tailTrace_1738105 : CollatzResearch.WordTrace tailWord_1738105 prefixEnd_1738105 594988861988684926596071 := by
  unfold tailWord_1738105
  simp only [CollatzResearch.WordTrace]
  refine ⟨63393897368149904546095769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42262598245433269697397179 63393897368149904546095769)
  ·
    refine ⟨47545423026112428409571827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63393897368149904546095769 47545423026112428409571827)
    ·
      refine ⟨71318134539168642614357741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47545423026112428409571827 71318134539168642614357741)
      ·
        refine ⟨26744300452188240980384153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71318134539168642614357741 26744300452188240980384153)
        ·
          refine ⟨20058225339141180735288115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26744300452188240980384153 20058225339141180735288115)
          ·
            refine ⟨30087338008711771102932173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20058225339141180735288115 30087338008711771102932173)
            ·
              refine ⟨11282751753266914163599565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30087338008711771102932173 11282751753266914163599565)
              ·
                refine ⟨4231031907475092811349837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11282751753266914163599565 4231031907475092811349837)
                ·
                  refine ⟨1586636965303159804256189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4231031907475092811349837 1586636965303159804256189)
                  ·
                    refine ⟨594988861988684926596071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586636965303159804256189 594988861988684926596071)
                    ·
                      rfl

theorem cell22_1738105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_1738105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738105 prefixEnd_1738105 := by exact prefixLift 1738105
  have htrace : WordTrace (prefixWord ++ tailWord_1738105) baseStart_1738105 baseEnd_1738105 := by
    simpa [prefixWord, tailWord_1738105, baseEnd_1738105] using wordTrace_append hprefix tailTrace_1738105
  have hstable : (prefixWord ++ tailWord_1738105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738105).length < 2 ^ (prefixWord ++ tailWord_1738105).sum := by decide
  have hdescent : baseEnd_1738105 < baseStart_1738105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738133 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1738133 : Nat := 118140960795 + 1738133 * 2 ^ 59
def prefixEnd_1738133 : Nat := 4983230072969 + 3 ^ 40 * 1738133 * 2
def baseEnd_1738133 : Nat := 594998446960902186895985

theorem tailTrace_1738133 : CollatzResearch.WordTrace tailWord_1738133 prefixEnd_1738133 594998446960902186895985 := by
  unfold tailWord_1738133
  simp only [CollatzResearch.WordTrace]
  refine ⟨63394918612048465328115053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42263279074698976885410035 63394918612048465328115053)
  ·
    refine ⟨23773094479518174498043145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63394918612048465328115053 23773094479518174498043145)
    ·
      refine ⟨17829820859638630873532359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23773094479518174498043145 17829820859638630873532359)
      ·
        refine ⟨26744731289457946310298539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17829820859638630873532359 26744731289457946310298539)
        ·
          refine ⟨40117096934186919465447809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26744731289457946310298539 40117096934186919465447809)
          ·
            refine ⟨30087822700640189599085857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40117096934186919465447809 30087822700640189599085857)
            ·
              refine ⟨22565867025480142199314393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30087822700640189599085857 22565867025480142199314393)
              ·
                refine ⟨16924400269110106649485795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22565867025480142199314393 16924400269110106649485795)
                ·
                  refine ⟨25386600403665159974228693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16924400269110106649485795 25386600403665159974228693)
                  ·
                    refine ⟨594998446960902186895985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25386600403665159974228693 594998446960902186895985)
                    ·
                      rfl

theorem cell22_1738133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1738133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738133 prefixEnd_1738133 := by exact prefixLift 1738133
  have htrace : WordTrace (prefixWord ++ tailWord_1738133) baseStart_1738133 baseEnd_1738133 := by
    simpa [prefixWord, tailWord_1738133, baseEnd_1738133] using wordTrace_append hprefix tailTrace_1738133
  have hstable : (prefixWord ++ tailWord_1738133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738133).length < 2 ^ (prefixWord ++ tailWord_1738133).sum := by decide
  have hdescent : baseEnd_1738133 < baseStart_1738133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738169 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 5]
def baseStart_1738169 : Nat := 118140960795 + 1738169 * 2 ^ 59
def prefixEnd_1738169 : Nat := 4983230072969 + 3 ^ 40 * 1738169 * 2
def baseEnd_1738169 : Nat := 198336923498870030998625

theorem tailTrace_1738169 : CollatzResearch.WordTrace tailWord_1738169 prefixEnd_1738169 198336923498870030998625 := by
  unfold tailWord_1738169
  simp only [CollatzResearch.WordTrace]
  refine ⟨63396231639918043476425561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42264154426612028984283707 63396231639918043476425561)
  ·
    refine ⟨47547173729938532607319171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63396231639918043476425561 47547173729938532607319171)
    ·
      refine ⟨71320760594907798910978757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47547173729938532607319171 71320760594907798910978757)
      ·
        refine ⟨13372642611545212295808517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71320760594907798910978757 13372642611545212295808517)
        ·
          refine ⟨2507370489664727305464097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13372642611545212295808517 2507370489664727305464097)
          ·
            refine ⟨1880527867248545479098073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507370489664727305464097 1880527867248545479098073)
            ·
              refine ⟨1410395900436409109323555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880527867248545479098073 1410395900436409109323555)
              ·
                refine ⟨2115593850654613663985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410395900436409109323555 2115593850654613663985333)
                ·
                  refine ⟨198336923498870030998625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2115593850654613663985333 198336923498870030998625)
                  ·
                    rfl

theorem cell22_1738169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_1738169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738169 prefixEnd_1738169 := by exact prefixLift 1738169
  have htrace : WordTrace (prefixWord ++ tailWord_1738169) baseStart_1738169 baseEnd_1738169 := by
    simpa [prefixWord, tailWord_1738169, baseEnd_1738169] using wordTrace_append hprefix tailTrace_1738169
  have hstable : (prefixWord ++ tailWord_1738169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738169).length < 2 ^ (prefixWord ++ tailWord_1738169).sum := by decide
  have hdescent : baseEnd_1738169 < baseStart_1738169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738197 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 4]
def baseStart_1738197 : Nat := 118140960795 + 1738197 * 2 ^ 59
def prefixEnd_1738197 : Nat := 4983230072969 + 3 ^ 40 * 1738197 * 2
def baseEnd_1738197 : Nat := 198340118489609117765263

theorem tailTrace_1738197 : CollatzResearch.WordTrace tailWord_1738197 prefixEnd_1738197 198340118489609117765263 := by
  unfold tailWord_1738197
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397252883816604258444845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42264835255877736172296563 63397252883816604258444845)
  ·
    refine ⟨23773969831431226596916817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63397252883816604258444845 23773969831431226596916817)
    ·
      refine ⟨17830477373573419947687613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23773969831431226596916817 17830477373573419947687613)
      ·
        refine ⟨6686429015090032480382855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17830477373573419947687613 6686429015090032480382855)
        ·
          refine ⟨10029643522635048720574283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686429015090032480382855 10029643522635048720574283)
          ·
            refine ⟨15044465283952573080861425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029643522635048720574283 15044465283952573080861425)
            ·
              refine ⟨11283348962964429810646069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15044465283952573080861425 11283348962964429810646069)
              ·
                refine ⟨1057813965277915294748069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11283348962964429810646069 1057813965277915294748069)
                ·
                  refine ⟨198340118489609117765263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1057813965277915294748069 198340118489609117765263)
                  ·
                    rfl

theorem cell22_1738197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_1738197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738197 prefixEnd_1738197 := by exact prefixLift 1738197
  have htrace : WordTrace (prefixWord ++ tailWord_1738197) baseStart_1738197 baseEnd_1738197 := by
    simpa [prefixWord, tailWord_1738197, baseEnd_1738197] using wordTrace_append hprefix tailTrace_1738197
  have hstable : (prefixWord ++ tailWord_1738197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738197).length < 2 ^ (prefixWord ++ tailWord_1738197).sum := by decide
  have hdescent : baseEnd_1738197 < baseStart_1738197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738225 : List Nat := [1, 2, 2, 2, 3, 2, 3, 7]
def baseStart_1738225 : Nat := 118140960795 + 1738225 * 2 ^ 59
def prefixEnd_1738225 : Nat := 4983230072969 + 3 ^ 40 * 1738225 * 2
def baseEnd_1738225 : Nat := 66114437826782734843967

theorem tailTrace_1738225 : CollatzResearch.WordTrace tailWord_1738225 prefixEnd_1738225 66114437826782734843967 := by
  unfold tailWord_1738225
  simp only [CollatzResearch.WordTrace]
  refine ⟨63398274127715165040464129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42265516085143443360309419 63398274127715165040464129)
  ·
    refine ⟨47548705595786373780348097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63398274127715165040464129 47548705595786373780348097)
    ·
      refine ⟨35661529196839780335261073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47548705595786373780348097 35661529196839780335261073)
      ·
        refine ⟨26746146897629835251445805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35661529196839780335261073 26746146897629835251445805)
        ·
          refine ⟨10029805086611188219292177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26746146897629835251445805 10029805086611188219292177)
          ·
            refine ⟨7522353814958391164469133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10029805086611188219292177 7522353814958391164469133)
            ·
              refine ⟨2820882680609396686675925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522353814958391164469133 2820882680609396686675925)
              ·
                refine ⟨66114437826782734843967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2820882680609396686675925 66114437826782734843967)
                ·
                  rfl

theorem cell22_1738225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 7].length) (baseStart_1738225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738225 prefixEnd_1738225 := by exact prefixLift 1738225
  have htrace : WordTrace (prefixWord ++ tailWord_1738225) baseStart_1738225 baseEnd_1738225 := by
    simpa [prefixWord, tailWord_1738225, baseEnd_1738225] using wordTrace_append hprefix tailTrace_1738225
  have hstable : (prefixWord ++ tailWord_1738225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738225).length < 2 ^ (prefixWord ++ tailWord_1738225).sum := by decide
  have hdescent : baseEnd_1738225 < baseStart_1738225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738229 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1738229 : Nat := 118140960795 + 1738229 * 2 ^ 59
def prefixEnd_1738229 : Nat := 4983230072969 + 3 ^ 40 * 1738229 * 2
def baseEnd_1738229 : Nat := 595031309722789936495691

theorem tailTrace_1738229 : CollatzResearch.WordTrace tailWord_1738229 prefixEnd_1738229 595031309722789936495691 := by
  unfold tailWord_1738229
  simp only [CollatzResearch.WordTrace]
  refine ⟨63398420019700673723609741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42265613346467115815739827 63398420019700673723609741)
  ·
    refine ⟨23774407507387752646353653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63398420019700673723609741 23774407507387752646353653)
    ·
      refine ⟨2228850703817601810595655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23774407507387752646353653 2228850703817601810595655)
      ·
        refine ⟨3343276055726402715893483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228850703817601810595655 3343276055726402715893483)
        ·
          refine ⟨5014914083589604073840225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343276055726402715893483 5014914083589604073840225)
          ·
            refine ⟨3761185562692203055380169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014914083589604073840225 3761185562692203055380169)
            ·
              refine ⟨2820889172019152291535127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761185562692203055380169 2820889172019152291535127)
              ·
                refine ⟨4231333758028728437302691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820889172019152291535127 4231333758028728437302691)
                ·
                  refine ⟨6347000637043092655954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231333758028728437302691 6347000637043092655954037)
                  ·
                    refine ⟨595031309722789936495691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6347000637043092655954037 595031309722789936495691)
                    ·
                      rfl

theorem cell22_1738229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1738229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738229 prefixEnd_1738229 := by exact prefixLift 1738229
  have htrace : WordTrace (prefixWord ++ tailWord_1738229) baseStart_1738229 baseEnd_1738229 := by
    simpa [prefixWord, tailWord_1738229, baseEnd_1738229] using wordTrace_append hprefix tailTrace_1738229
  have hstable : (prefixWord ++ tailWord_1738229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738229).length < 2 ^ (prefixWord ++ tailWord_1738229).sum := by decide
  have hdescent : baseEnd_1738229 < baseStart_1738229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738345 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1738345 : Nat := 118140960795 + 1738345 * 2 ^ 59
def prefixEnd_1738345 : Nat := 4983230072969 + 3 ^ 40 * 1738345 * 2
def baseEnd_1738345 : Nat := 595071018893404300595335

theorem tailTrace_1738345 : CollatzResearch.WordTrace tailWord_1738345 prefixEnd_1738345 595071018893404300595335 := by
  unfold tailWord_1738345
  simp only [CollatzResearch.WordTrace]
  refine ⟨63402650887280425534832489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42268433924853617023221659 63402650887280425534832489)
  ·
    refine ⟨47551988165460319151124367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63402650887280425534832489 47551988165460319151124367)
    ·
      refine ⟨71327982248190478726686551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47551988165460319151124367 71327982248190478726686551)
      ·
        refine ⟨106991973372285718090029827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71327982248190478726686551 106991973372285718090029827)
        ·
          refine ⟨160487960058428577135044741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106991973372285718090029827 160487960058428577135044741)
          ·
            refine ⟨30091492510955358212820889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160487960058428577135044741 30091492510955358212820889)
            ·
              refine ⟨22568619383216518659615667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30091492510955358212820889 22568619383216518659615667)
              ·
                refine ⟨33852929074824777989423501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22568619383216518659615667 33852929074824777989423501)
                ·
                  refine ⟨12694848403059291746033813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33852929074824777989423501 12694848403059291746033813)
                  ·
                    refine ⟨595071018893404300595335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12694848403059291746033813 595071018893404300595335)
                    ·
                      rfl

theorem cell22_1738345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1738345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738345 prefixEnd_1738345 := by exact prefixLift 1738345
  have htrace : WordTrace (prefixWord ++ tailWord_1738345) baseStart_1738345 baseEnd_1738345 := by
    simpa [prefixWord, tailWord_1738345, baseEnd_1738345] using wordTrace_append hprefix tailTrace_1738345
  have hstable : (prefixWord ++ tailWord_1738345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738345).length < 2 ^ (prefixWord ++ tailWord_1738345).sum := by decide
  have hdescent : baseEnd_1738345 < baseStart_1738345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738426 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_1738426 : Nat := 118140960795 + 1738426 * 2 ^ 59
def prefixEnd_1738426 : Nat := 4983230072969 + 3 ^ 40 * 1738426 * 2
def baseEnd_1738426 : Nat := 595098746848747089320087

theorem tailTrace_1738426 : CollatzResearch.WordTrace tailWord_1738426 prefixEnd_1738426 595098746848747089320087 := by
  unfold tailWord_1738426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851401299996744092132783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42270403466657984245687421 15851401299996744092132783)
  ·
    refine ⟨23777101949995116138199175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15851401299996744092132783 23777101949995116138199175)
    ·
      refine ⟨35665652924992674207298763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23777101949995116138199175 35665652924992674207298763)
      ·
        refine ⟨53498479387489011310948145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35665652924992674207298763 53498479387489011310948145)
        ·
          refine ⟨40123859540616758483211109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53498479387489011310948145 40123859540616758483211109)
          ·
            refine ⟨7523223663865642215602083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40123859540616758483211109 7523223663865642215602083)
            ·
              refine ⟨11284835495798463323403125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523223663865642215602083 11284835495798463323403125)
              ·
                refine ⟨1057953327731105936569043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11284835495798463323403125 1057953327731105936569043)
                ·
                  refine ⟨1586929991596658904853565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057953327731105936569043 1586929991596658904853565)
                  ·
                    refine ⟨595098746848747089320087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586929991596658904853565 595098746848747089320087)
                    ·
                      rfl

theorem cell22_1738426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_1738426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738426 prefixEnd_1738426 := by exact prefixLift 1738426
  have htrace : WordTrace (prefixWord ++ tailWord_1738426) baseStart_1738426 baseEnd_1738426 := by
    simpa [prefixWord, tailWord_1738426, baseEnd_1738426] using wordTrace_append hprefix tailTrace_1738426
  have hstable : (prefixWord ++ tailWord_1738426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738426).length < 2 ^ (prefixWord ++ tailWord_1738426).sum := by decide
  have hdescent : baseEnd_1738426 < baseStart_1738426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738486 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1738486 : Nat := 118140960795 + 1738486 * 2 ^ 59
def prefixEnd_1738486 : Nat := 4983230072969 + 3 ^ 40 * 1738486 * 2
def baseEnd_1738486 : Nat := 595119286074926932819903

theorem tailTrace_1738486 : CollatzResearch.WordTrace tailWord_1738486 prefixEnd_1738486 595119286074926932819903 := by
  unfold tailWord_1738486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962987098735600413482207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42271862386513071077143541 3962987098735600413482207)
  ·
    refine ⟨5944480648103400620223311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962987098735600413482207 5944480648103400620223311)
    ·
      refine ⟨8916720972155100930334967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5944480648103400620223311 8916720972155100930334967)
      ·
        refine ⟨13375081458232651395502451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916720972155100930334967 13375081458232651395502451)
        ·
          refine ⟨20062622187348977093253677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13375081458232651395502451 20062622187348977093253677)
          ·
            refine ⟨7523483320255866409970129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20062622187348977093253677 7523483320255866409970129)
            ·
              refine ⟨5642612490191899807477597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7523483320255866409970129 5642612490191899807477597)
              ·
                refine ⟨2115979683821962427804099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5642612490191899807477597 2115979683821962427804099)
                ·
                  refine ⟨3173969525732943641706149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115979683821962427804099 3173969525732943641706149)
                  ·
                    refine ⟨595119286074926932819903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173969525732943641706149 595119286074926932819903)
                    ·
                      rfl

theorem cell22_1738486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1738486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738486 prefixEnd_1738486 := by exact prefixLift 1738486
  have htrace : WordTrace (prefixWord ++ tailWord_1738486) baseStart_1738486 baseEnd_1738486 := by
    simpa [prefixWord, tailWord_1738486, baseEnd_1738486] using wordTrace_append hprefix tailTrace_1738486
  have hstable : (prefixWord ++ tailWord_1738486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738486).length < 2 ^ (prefixWord ++ tailWord_1738486).sum := by decide
  have hdescent : baseEnd_1738486 < baseStart_1738486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738499 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 4, 3]
def baseStart_1738499 : Nat := 118140960795 + 1738499 * 2 ^ 59
def prefixEnd_1738499 : Nat := 4983230072969 + 3 ^ 40 * 1738499 * 2
def baseEnd_1738499 : Nat := 595123736240599232244863

theorem tailTrace_1738499 : CollatzResearch.WordTrace tailWord_1738499 prefixEnd_1738499 595123736240599232244863 := by
  unfold tailWord_1738499
  simp only [CollatzResearch.WordTrace]
  refine ⟨63408267728722509835938551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42272178485815006557292367 63408267728722509835938551)
  ·
    refine ⟨95112401593083764753907827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63408267728722509835938551 95112401593083764753907827)
    ·
      refine ⟨142668602389625647130861741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95112401593083764753907827 142668602389625647130861741)
      ·
        refine ⟨53500725896109617674073153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142668602389625647130861741 53500725896109617674073153)
        ·
          refine ⟨40125544422082213255554865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53500725896109617674073153 40125544422082213255554865)
          ·
            refine ⟨30094158316561659941666149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40125544422082213255554865 30094158316561659941666149)
            ·
              refine ⟨5642654684355311239062403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30094158316561659941666149 5642654684355311239062403)
              ·
                refine ⟨8463982026532966858593605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642654684355311239062403 8463982026532966858593605)
                ·
                  refine ⟨1586996629974931285986301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8463982026532966858593605 1586996629974931285986301)
                  ·
                    refine ⟨595123736240599232244863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586996629974931285986301 595123736240599232244863)
                    ·
                      rfl

theorem cell22_1738499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].length) (baseStart_1738499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738499 prefixEnd_1738499 := by exact prefixLift 1738499
  have htrace : WordTrace (prefixWord ++ tailWord_1738499) baseStart_1738499 baseEnd_1738499 := by
    simpa [prefixWord, tailWord_1738499, baseEnd_1738499] using wordTrace_append hprefix tailTrace_1738499
  have hstable : (prefixWord ++ tailWord_1738499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738499).length < 2 ^ (prefixWord ++ tailWord_1738499).sum := by decide
  have hdescent : baseEnd_1738499 < baseStart_1738499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738550 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1738550 : Nat := 118140960795 + 1738550 * 2 ^ 59
def prefixEnd_1738550 : Nat := 4983230072969 + 3 ^ 40 * 1738550 * 2
def baseEnd_1738550 : Nat := 595141194582852099219707

theorem tailTrace_1738550 : CollatzResearch.WordTrace tailWord_1738550 prefixEnd_1738550 595141194582852099219707 := by
  unfold tailWord_1738550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963132990721109096627819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42273418567691830364030069 3963132990721109096627819)
  ·
    refine ⟨5944699486081663644941729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963132990721109096627819 5944699486081663644941729)
    ·
      refine ⟨4458524614561247733706297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5944699486081663644941729 4458524614561247733706297)
      ·
        refine ⟨3343893460920935800279723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4458524614561247733706297 3343893460920935800279723)
        ·
          refine ⟨5015840191381403700419585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343893460920935800279723 5015840191381403700419585)
          ·
            refine ⟨3761880143536052775314689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5015840191381403700419585 3761880143536052775314689)
            ·
              refine ⟨2821410107652039581486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761880143536052775314689 2821410107652039581486017)
              ·
                refine ⟨2116057580739029686114513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821410107652039581486017 2116057580739029686114513)
                ·
                  refine ⟨1587043185554272264585885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2116057580739029686114513 1587043185554272264585885)
                  ·
                    refine ⟨595141194582852099219707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587043185554272264585885 595141194582852099219707)
                    ·
                      rfl

theorem cell22_1738550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1738550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738550 prefixEnd_1738550 := by exact prefixLift 1738550
  have htrace : WordTrace (prefixWord ++ tailWord_1738550) baseStart_1738550 baseEnd_1738550 := by
    simpa [prefixWord, tailWord_1738550, baseEnd_1738550] using wordTrace_append hprefix tailTrace_1738550
  have hstable : (prefixWord ++ tailWord_1738550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738550).length < 2 ^ (prefixWord ++ tailWord_1738550).sum := by decide
  have hdescent : baseEnd_1738550 < baseStart_1738550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738595 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 1, 3]
def baseStart_1738595 : Nat := 118140960795 + 1738595 * 2 ^ 59
def prefixEnd_1738595 : Nat := 4983230072969 + 3 ^ 40 * 1738595 * 2
def baseEnd_1738595 : Nat := 595156599002486981844569

theorem tailTrace_1738595 : CollatzResearch.WordTrace tailWord_1738595 prefixEnd_1738595 595156599002486981844569 := by
  unfold tailWord_1738595
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411769136374718231433239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42274512757583145487622159 63411769136374718231433239)
  ·
    refine ⟨95117653704562077347149859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63411769136374718231433239 95117653704562077347149859)
    ·
      refine ⟨142676480556843116020724789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95117653704562077347149859 142676480556843116020724789)
      ·
        refine ⟨13375920052204042126942949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142676480556843116020724789 13375920052204042126942949)
        ·
          refine ⟨2507985009788257898801803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13375920052204042126942949 2507985009788257898801803)
          ·
            refine ⟨3761977514682386848202705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507985009788257898801803 3761977514682386848202705)
            ·
              refine ⟨2821483136011790136152029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761977514682386848202705 2821483136011790136152029)
              ·
                refine ⟨1058056176004421301057011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821483136011790136152029 1058056176004421301057011)
                ·
                  refine ⟨1587084264006631951585517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058056176004421301057011 1587084264006631951585517)
                  ·
                    refine ⟨595156599002486981844569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587084264006631951585517 595156599002486981844569)
                    ·
                      rfl

theorem cell22_1738595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 3].length) (baseStart_1738595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738595 prefixEnd_1738595 := by exact prefixLift 1738595
  have htrace : WordTrace (prefixWord ++ tailWord_1738595) baseStart_1738595 baseEnd_1738595 := by
    simpa [prefixWord, tailWord_1738595, baseEnd_1738595] using wordTrace_append hprefix tailTrace_1738595
  have hstable : (prefixWord ++ tailWord_1738595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738595).length < 2 ^ (prefixWord ++ tailWord_1738595).sum := by decide
  have hdescent : baseEnd_1738595 < baseStart_1738595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738606 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1738606 : Nat := 118140960795 + 1738606 * 2 ^ 59
def prefixEnd_1738606 : Nat := 4983230072969 + 3 ^ 40 * 1738606 * 2
def baseEnd_1738606 : Nat := 595160364527286619819535

theorem tailTrace_1738606 : CollatzResearch.WordTrace tailWord_1738606 prefixEnd_1738606 595160364527286619819535 := by
  unfold tailWord_1738606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926521292416858388760459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42274780226223244740055781 7926521292416858388760459)
  ·
    refine ⟨11889781938625287583140689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7926521292416858388760459 11889781938625287583140689)
    ·
      refine ⟨8917336453968965687355517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11889781938625287583140689 8917336453968965687355517)
      ·
        refine ⟨3344001170238362132758319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8917336453968965687355517 3344001170238362132758319)
        ·
          refine ⟨5016001755357543199137479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344001170238362132758319 5016001755357543199137479)
          ·
            refine ⟨7524002633036314798706219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016001755357543199137479 7524002633036314798706219)
            ·
              refine ⟨11286003949554472198059329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524002633036314798706219 11286003949554472198059329)
              ·
                refine ⟨8464502962165854148544497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11286003949554472198059329 8464502962165854148544497)
                ·
                  refine ⟨6348377221624390611408373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8464502962165854148544497 6348377221624390611408373)
                  ·
                    refine ⟨595160364527286619819535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6348377221624390611408373 595160364527286619819535)
                    ·
                      rfl

theorem cell22_1738606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1738606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738606 prefixEnd_1738606 := by exact prefixLift 1738606
  have htrace : WordTrace (prefixWord ++ tailWord_1738606) baseStart_1738606 baseEnd_1738606 := by
    simpa [prefixWord, tailWord_1738606, baseEnd_1738606] using wordTrace_append hprefix tailTrace_1738606
  have hstable : (prefixWord ++ tailWord_1738606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738606).length < 2 ^ (prefixWord ++ tailWord_1738606).sum := by decide
  have hdescent : baseEnd_1738606 < baseStart_1738606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738625 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 5]
def baseStart_1738625 : Nat := 118140960795 + 1738625 * 2 ^ 59
def prefixEnd_1738625 : Nat := 4983230072969 + 3 ^ 40 * 1738625 * 2
def baseEnd_1738625 : Nat := 198388956205192301198159

theorem tailTrace_1738625 : CollatzResearch.WordTrace tailWord_1738625 prefixEnd_1738625 198388956205192301198159 := by
  unfold tailWord_1738625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63412863326266033355025329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42275242217510688903350219 63412863326266033355025329)
  ·
    refine ⟨47559647494699525016268997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63412863326266033355025329 47559647494699525016268997)
    ·
      refine ⟨8917433905256160940550437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47559647494699525016268997 8917433905256160940550437)
      ·
        refine ⟨1672018857235530176353207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8917433905256160940550437 1672018857235530176353207)
        ·
          refine ⟨2508028285853295264529811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672018857235530176353207 2508028285853295264529811)
          ·
            refine ⟨3762042428779942896794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508028285853295264529811 3762042428779942896794717)
            ·
              refine ⟨1410765910792478586298019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762042428779942896794717 1410765910792478586298019)
              ·
                refine ⟨2116148866188717879447029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410765910792478586298019 2116148866188717879447029)
                ·
                  refine ⟨198388956205192301198159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116148866188717879447029 198388956205192301198159)
                  ·
                    rfl

theorem cell22_1738625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_1738625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738625 prefixEnd_1738625 := by exact prefixLift 1738625
  have htrace : WordTrace (prefixWord ++ tailWord_1738625) baseStart_1738625 baseEnd_1738625 := by
    simpa [prefixWord, tailWord_1738625, baseEnd_1738625] using wordTrace_append hprefix tailTrace_1738625
  have hstable : (prefixWord ++ tailWord_1738625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738625).length < 2 ^ (prefixWord ++ tailWord_1738625).sum := by decide
  have hdescent : baseEnd_1738625 < baseStart_1738625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738646 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1738646 : Nat := 118140960795 + 1738646 * 2 ^ 59
def prefixEnd_1738646 : Nat := 4983230072969 + 3 ^ 40 * 1738646 * 2
def baseEnd_1738646 : Nat := 595174057344739848819413

theorem tailTrace_1738646 : CollatzResearch.WordTrace tailWord_1738646 prefixEnd_1738646 595174057344739848819413 := by
  unfold tailWord_1738646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963351828699372121346237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42275752839459969294359861 3963351828699372121346237)
  ·
    refine ⟨1486256935762264545504839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3963351828699372121346237 1486256935762264545504839)
    ·
      refine ⟨2229385403643396818257259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486256935762264545504839 2229385403643396818257259)
      ·
        refine ⟨3344078105465095227385889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229385403643396818257259 3344078105465095227385889)
        ·
          refine ⟨2508058579098821420539417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344078105465095227385889 2508058579098821420539417)
          ·
            refine ⟨1881043934324116065404563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508058579098821420539417 1881043934324116065404563)
            ·
              refine ⟨2821565901486174098106845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881043934324116065404563 2821565901486174098106845)
              ·
                refine ⟨1058087213057315286790067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821565901486174098106845 1058087213057315286790067)
                ·
                  refine ⟨1587130819585972930185101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058087213057315286790067 1587130819585972930185101)
                  ·
                    refine ⟨595174057344739848819413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587130819585972930185101 595174057344739848819413)
                    ·
                      rfl

theorem cell22_1738646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1738646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738646 prefixEnd_1738646 := by exact prefixLift 1738646
  have htrace : WordTrace (prefixWord ++ tailWord_1738646) baseStart_1738646 baseEnd_1738646 := by
    simpa [prefixWord, tailWord_1738646, baseEnd_1738646] using wordTrace_append hprefix tailTrace_1738646
  have hstable : (prefixWord ++ tailWord_1738646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738646).length < 2 ^ (prefixWord ++ tailWord_1738646).sum := by decide
  have hdescent : baseEnd_1738646 < baseStart_1738646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738649 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1738649 : Nat := 118140960795 + 1738649 * 2 ^ 59
def prefixEnd_1738649 : Nat := 4983230072969 + 3 ^ 40 * 1738649 * 2
def baseEnd_1738649 : Nat := 595175084306048840994403

theorem tailTrace_1738649 : CollatzResearch.WordTrace tailWord_1738649 prefixEnd_1738649 595175084306048840994403 := by
  unfold tailWord_1738649
  simp only [CollatzResearch.WordTrace]
  refine ⟨63413738678179085453899001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42275825785452723635932667 63413738678179085453899001)
  ·
    refine ⟨47560304008634314090424251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63413738678179085453899001 47560304008634314090424251)
    ·
      refine ⟨71340456012951471135636377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47560304008634314090424251 71340456012951471135636377)
      ·
        refine ⟨53505342009713603351727283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71340456012951471135636377 53505342009713603351727283)
        ·
          refine ⟨80258013014570405027590925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53505342009713603351727283 80258013014570405027590925)
          ·
            refine ⟨30096754880463901885346597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80258013014570405027590925 30096754880463901885346597)
            ·
              refine ⟨5643141540086981603502487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30096754880463901885346597 5643141540086981603502487)
              ·
                refine ⟨8464712310130472405253731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643141540086981603502487 8464712310130472405253731)
                ·
                  refine ⟨12697068465195708607880597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464712310130472405253731 12697068465195708607880597)
                  ·
                    refine ⟨595175084306048840994403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12697068465195708607880597 595175084306048840994403)
                    ·
                      rfl

theorem cell22_1738649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1738649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738649 prefixEnd_1738649 := by exact prefixLift 1738649
  have htrace : WordTrace (prefixWord ++ tailWord_1738649) baseStart_1738649 baseEnd_1738649 := by
    simpa [prefixWord, tailWord_1738649, baseEnd_1738649] using wordTrace_append hprefix tailTrace_1738649
  have hstable : (prefixWord ++ tailWord_1738649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738649).length < 2 ^ (prefixWord ++ tailWord_1738649).sum := by decide
  have hdescent : baseEnd_1738649 < baseStart_1738649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738653 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1738653 : Nat := 118140960795 + 1738653 * 2 ^ 59
def prefixEnd_1738653 : Nat := 4983230072969 + 3 ^ 40 * 1738653 * 2
def baseEnd_1738653 : Nat := 198392151195931387964797

theorem tailTrace_1738653 : CollatzResearch.WordTrace tailWord_1738653 prefixEnd_1738653 198392151195931387964797 := by
  unfold tailWord_1738653
  simp only [CollatzResearch.WordTrace]
  refine ⟨63413884570164594137044613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42275923046776396091363075 63413884570164594137044613)
  ·
    refine ⟨11890103356905861400695865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63413884570164594137044613 11890103356905861400695865)
    ·
      refine ⟨8917577517679396050521899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890103356905861400695865 8917577517679396050521899)
      ·
        refine ⟨13376366276519094075782849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917577517679396050521899 13376366276519094075782849)
        ·
          refine ⟨10032274707389320556837137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13376366276519094075782849 10032274707389320556837137)
          ·
            refine ⟨7524206030541990417627853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10032274707389320556837137 7524206030541990417627853)
            ·
              refine ⟨2821577261453246406610445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7524206030541990417627853 2821577261453246406610445)
              ·
                refine ⟨1058091473044967402478917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821577261453246406610445 1058091473044967402478917)
                ·
                  refine ⟨198392151195931387964797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058091473044967402478917 198392151195931387964797)
                  ·
                    rfl

theorem cell22_1738653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1738653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738653 prefixEnd_1738653 := by exact prefixLift 1738653
  have htrace : WordTrace (prefixWord ++ tailWord_1738653) baseStart_1738653 baseEnd_1738653 := by
    simpa [prefixWord, tailWord_1738653, baseEnd_1738653] using wordTrace_append hprefix tailTrace_1738653
  have hstable : (prefixWord ++ tailWord_1738653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738653).length < 2 ^ (prefixWord ++ tailWord_1738653).sum := by decide
  have hdescent : baseEnd_1738653 < baseStart_1738653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738685 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_1738685 : Nat := 118140960795 + 1738685 * 2 ^ 59
def prefixEnd_1738685 : Nat := 4983230072969 + 3 ^ 40 * 1738685 * 2
def baseEnd_1738685 : Nat := 595187407841756747094293

theorem tailTrace_1738685 : CollatzResearch.WordTrace tailWord_1738685 prefixEnd_1738685 595187407841756747094293 := by
  unfold tailWord_1738685
  simp only [CollatzResearch.WordTrace]
  refine ⟨63415051706048663602209509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42276701137365775734806339 63415051706048663602209509)
  ·
    refine ⟨11890322194884124425414283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63415051706048663602209509 11890322194884124425414283)
    ·
      refine ⟨17835483292326186638121425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11890322194884124425414283 17835483292326186638121425)
      ·
        refine ⟨13376612469244639978591069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17835483292326186638121425 13376612469244639978591069)
        ·
          refine ⟨5016229675966739991971651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13376612469244639978591069 5016229675966739991971651)
          ·
            refine ⟨7524344513950109987957477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016229675966739991971651 7524344513950109987957477)
            ·
              refine ⟨1410814596365645622742027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7524344513950109987957477 1410814596365645622742027)
              ·
                refine ⟨2116221894548468434113041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410814596365645622742027 2116221894548468434113041)
                ·
                  refine ⟨1587166420911351325584781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2116221894548468434113041 1587166420911351325584781)
                  ·
                    refine ⟨595187407841756747094293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587166420911351325584781 595187407841756747094293)
                    ·
                      rfl

theorem cell22_1738685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_1738685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738685 prefixEnd_1738685 := by exact prefixLift 1738685
  have htrace : WordTrace (prefixWord ++ tailWord_1738685) baseStart_1738685 baseEnd_1738685 := by
    simpa [prefixWord, tailWord_1738685, baseEnd_1738685] using wordTrace_append hprefix tailTrace_1738685
  have hstable : (prefixWord ++ tailWord_1738685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738685).length < 2 ^ (prefixWord ++ tailWord_1738685).sum := by decide
  have hdescent : baseEnd_1738685 < baseStart_1738685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738730 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1738730 : Nat := 118140960795 + 1738730 * 2 ^ 59
def prefixEnd_1738730 : Nat := 4983230072969 + 3 ^ 40 * 1738730 * 2
def baseEnd_1738730 : Nat := 595202812261391629719155

theorem tailTrace_1738730 : CollatzResearch.WordTrace tailWord_1738730 prefixEnd_1738730 595202812261391629719155 := by
  unfold tailWord_1738730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854173247721409071899411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42277795327257090858398429 15854173247721409071899411)
  ·
    refine ⟨23781259871582113607849117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854173247721409071899411 23781259871582113607849117)
    ·
      refine ⟨8917972451843292602943419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23781259871582113607849117 8917972451843292602943419)
      ·
        refine ⟨13376958677764938904415129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917972451843292602943419 13376958677764938904415129)
        ·
          refine ⟨10032719008323704178311347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13376958677764938904415129 10032719008323704178311347)
          ·
            refine ⟨15049078512485556267467021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10032719008323704178311347 15049078512485556267467021)
            ·
              refine ⟨5643404442182083600300133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15049078512485556267467021 5643404442182083600300133)
              ·
                refine ⟨1058138332909140675056275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5643404442182083600300133 1058138332909140675056275)
                ·
                  refine ⟨1587207499363711012584413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058138332909140675056275 1587207499363711012584413)
                  ·
                    refine ⟨595202812261391629719155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587207499363711012584413 595202812261391629719155)
                    ·
                      rfl

theorem cell22_1738730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1738730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738730 prefixEnd_1738730 := by exact prefixLift 1738730
  have htrace : WordTrace (prefixWord ++ tailWord_1738730) baseStart_1738730 baseEnd_1738730 := by
    simpa [prefixWord, tailWord_1738730, baseEnd_1738730] using wordTrace_append hprefix tailTrace_1738730
  have hstable : (prefixWord ++ tailWord_1738730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738730).length < 2 ^ (prefixWord ++ tailWord_1738730).sum := by decide
  have hdescent : baseEnd_1738730 < baseStart_1738730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738801 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1738801 : Nat := 118140960795 + 1738801 * 2 ^ 59
def prefixEnd_1738801 : Nat := 4983230072969 + 3 ^ 40 * 1738801 * 2
def baseEnd_1738801 : Nat := 595227117012371111193937

theorem tailTrace_1738801 : CollatzResearch.WordTrace tailWord_1738801 prefixEnd_1738801 595227117012371111193937 := by
  unfold tailWord_1738801
  simp only [CollatzResearch.WordTrace]
  refine ⟨63419282573628415413432257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42279521715752276942288171 63419282573628415413432257)
  ·
    refine ⟨47564461930221311560074193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63419282573628415413432257 47564461930221311560074193)
    ·
      refine ⟨35673346447665983670055645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47564461930221311560074193 35673346447665983670055645)
      ·
        refine ⟨13377504917874743876270867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35673346447665983670055645 13377504917874743876270867)
        ·
          refine ⟨20066257376812115814406301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377504917874743876270867 20066257376812115814406301)
          ·
            refine ⟨7524846516304543430402363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20066257376812115814406301 7524846516304543430402363)
            ·
              refine ⟨11287269774456815145603545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524846516304543430402363 11287269774456815145603545)
              ·
                refine ⟨8465452330842611359202659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11287269774456815145603545 8465452330842611359202659)
                ·
                  refine ⟨12698178496263917038803989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8465452330842611359202659 12698178496263917038803989)
                  ·
                    refine ⟨595227117012371111193937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12698178496263917038803989 595227117012371111193937)
                    ·
                      rfl

theorem cell22_1738801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1738801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738801 prefixEnd_1738801 := by exact prefixLift 1738801
  have htrace : WordTrace (prefixWord ++ tailWord_1738801) baseStart_1738801 baseEnd_1738801 := by
    simpa [prefixWord, tailWord_1738801, baseEnd_1738801] using wordTrace_append hprefix tailTrace_1738801
  have hstable : (prefixWord ++ tailWord_1738801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738801).length < 2 ^ (prefixWord ++ tailWord_1738801).sum := by decide
  have hdescent : baseEnd_1738801 < baseStart_1738801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738803 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 2, 3]
def baseStart_1738803 : Nat := 118140960795 + 1738803 * 2 ^ 59
def prefixEnd_1738803 : Nat := 4983230072969 + 3 ^ 40 * 1738803 * 2
def baseEnd_1738803 : Nat := 595227801653243772643931

theorem tailTrace_1738803 : CollatzResearch.WordTrace tailWord_1738803 prefixEnd_1738803 595227801653243772643931 := by
  unfold tailWord_1738803
  simp only [CollatzResearch.WordTrace]
  refine ⟨63419355519621169755005063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42279570346414113170003375 63419355519621169755005063)
  ·
    refine ⟨95129033279431754632507595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63419355519621169755005063 95129033279431754632507595)
    ·
      refine ⟨142693549919147631948761393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95129033279431754632507595 142693549919147631948761393)
      ·
        refine ⟨107020162439360723961571045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142693549919147631948761393 107020162439360723961571045)
        ·
          refine ⟨20066280457380135742794571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107020162439360723961571045 20066280457380135742794571)
          ·
            refine ⟨30099420686070203614191857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20066280457380135742794571 30099420686070203614191857)
            ·
              refine ⟨22574565514552652710643893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30099420686070203614191857 22574565514552652710643893)
              ·
                refine ⟨2116365516989311191622865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22574565514552652710643893 2116365516989311191622865)
                ·
                  refine ⟨1587274137741983393717149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2116365516989311191622865 1587274137741983393717149)
                  ·
                    refine ⟨595227801653243772643931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587274137741983393717149 595227801653243772643931)
                    ·
                      rfl

theorem cell22_1738803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].length) (baseStart_1738803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738803 prefixEnd_1738803 := by exact prefixLift 1738803
  have htrace : WordTrace (prefixWord ++ tailWord_1738803) baseStart_1738803 baseEnd_1738803 := by
    simpa [prefixWord, tailWord_1738803, baseEnd_1738803] using wordTrace_append hprefix tailTrace_1738803
  have hstable : (prefixWord ++ tailWord_1738803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738803).length < 2 ^ (prefixWord ++ tailWord_1738803).sum := by decide
  have hdescent : baseEnd_1738803 < baseStart_1738803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738816 : List Nat := [2, 1, 1, 2, 2, 5, 1, 8]
def baseStart_1738816 : Nat := 118140960795 + 1738816 * 2 ^ 59
def prefixEnd_1738816 : Nat := 4983230072969 + 3 ^ 40 * 1738816 * 2
def baseEnd_1738816 : Nat := 66136916868768452452099

theorem tailTrace_1738816 : CollatzResearch.WordTrace tailWord_1738816 prefixEnd_1738816 66136916868768452452099 := by
  unfold tailWord_1738816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709914834287036487614151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42279886445716048650152201 31709914834287036487614151)
  ·
    refine ⟨47564872251430554731421227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31709914834287036487614151 47564872251430554731421227)
    ·
      refine ⟨71347308377145832097131841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564872251430554731421227 71347308377145832097131841)
      ·
        refine ⟨53510481282859374072848881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71347308377145832097131841 53510481282859374072848881)
        ·
          refine ⟨40132860962144530554636661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53510481282859374072848881 40132860962144530554636661)
          ·
            refine ⟨3762455715201049739497187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40132860962144530554636661 3762455715201049739497187)
            ·
              refine ⟨5643683572801574609245781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762455715201049739497187 5643683572801574609245781)
              ·
                refine ⟨66136916868768452452099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5643683572801574609245781 66136916868768452452099)
                ·
                  rfl

theorem cell22_1738816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_1738816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738816 prefixEnd_1738816 := by exact prefixLift 1738816
  have htrace : WordTrace (prefixWord ++ tailWord_1738816) baseStart_1738816 baseEnd_1738816 := by
    simpa [prefixWord, tailWord_1738816, baseEnd_1738816] using wordTrace_append hprefix tailTrace_1738816
  have hstable : (prefixWord ++ tailWord_1738816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738816).length < 2 ^ (prefixWord ++ tailWord_1738816).sum := by decide
  have hdescent : baseEnd_1738816 < baseStart_1738816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738850 : List Nat := [3, 3, 2, 2, 2, 1, 2, 7]
def baseStart_1738850 : Nat := 118140960795 + 1738850 * 2 ^ 59
def prefixEnd_1738850 : Nat := 4983230072969 + 3 ^ 40 * 1738850 * 2
def baseEnd_1738850 : Nat := 66138210079305701857643

theorem tailTrace_1738850 : CollatzResearch.WordTrace tailWord_1738850 prefixEnd_1738850 66138210079305701857643 := by
  unfold tailWord_1738850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855267437612724195491501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42280713166967264521310669 15855267437612724195491501)
  ·
    refine ⟨5945725289104771573309313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15855267437612724195491501 5945725289104771573309313)
    ·
      refine ⟨4459293966828578679981985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945725289104771573309313 4459293966828578679981985)
      ·
        refine ⟨3344470475121434009986489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459293966828578679981985 3344470475121434009986489)
        ·
          refine ⟨2508352856341075507489867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344470475121434009986489 2508352856341075507489867)
          ·
            refine ⟨3762529284511613261234801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508352856341075507489867 3762529284511613261234801)
            ·
              refine ⟨2821896963383709945926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762529284511613261234801 2821896963383709945926101)
              ·
                refine ⟨66138210079305701857643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2821896963383709945926101 66138210079305701857643)
                ·
                  rfl

theorem cell22_1738850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_1738850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738850 prefixEnd_1738850 := by exact prefixLift 1738850
  have htrace : WordTrace (prefixWord ++ tailWord_1738850) baseStart_1738850 baseEnd_1738850 := by
    simpa [prefixWord, tailWord_1738850, baseEnd_1738850] using wordTrace_append hprefix tailTrace_1738850
  have hstable : (prefixWord ++ tailWord_1738850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738850).length < 2 ^ (prefixWord ++ tailWord_1738850).sum := by decide
  have hdescent : baseEnd_1738850 < baseStart_1738850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738908 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1738908 : Nat := 118140960795 + 1738908 * 2 ^ 59
def prefixEnd_1738908 : Nat := 4983230072969 + 3 ^ 40 * 1738908 * 2
def baseEnd_1738908 : Nat := 595263745299058498768609

theorem tailTrace_1738908 : CollatzResearch.WordTrace tailWord_1738908 prefixEnd_1738908 595263745299058498768609 := by
  unfold tailWord_1738908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31711592592120386343788689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42282123456160515125051585 31711592592120386343788689)
  ·
    refine ⟨23783694444090289757841517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31711592592120386343788689 23783694444090289757841517)
    ·
      refine ⟨8918885416533858659190569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23783694444090289757841517 8918885416533858659190569)
      ·
        refine ⟨6689164062400393994392927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918885416533858659190569 6689164062400393994392927)
        ·
          refine ⟨10033746093600590991589391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689164062400393994392927 10033746093600590991589391)
          ·
            refine ⟨15050619140400886487384087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033746093600590991589391 15050619140400886487384087)
            ·
              refine ⟨22575928710601329731076131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15050619140400886487384087 22575928710601329731076131)
              ·
                refine ⟨33863893065901994596614197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22575928710601329731076131 33863893065901994596614197)
                ·
                  refine ⟨3174739974928311993432581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33863893065901994596614197 3174739974928311993432581)
                  ·
                    refine ⟨595263745299058498768609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174739974928311993432581 595263745299058498768609)
                    ·
                      rfl

theorem cell22_1738908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1738908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738908 prefixEnd_1738908 := by exact prefixLift 1738908
  have htrace : WordTrace (prefixWord ++ tailWord_1738908) baseStart_1738908 baseEnd_1738908 := by
    simpa [prefixWord, tailWord_1738908, baseEnd_1738908] using wordTrace_append hprefix tailTrace_1738908
  have hstable : (prefixWord ++ tailWord_1738908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738908).length < 2 ^ (prefixWord ++ tailWord_1738908).sum := by decide
  have hdescent : baseEnd_1738908 < baseStart_1738908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738925 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1738925 : Nat := 118140960795 + 1738925 * 2 ^ 59
def prefixEnd_1738925 : Nat := 4983230072969 + 3 ^ 40 * 1738925 * 2
def baseEnd_1738925 : Nat := 595269564746476121093557

theorem tailTrace_1738925 : CollatzResearch.WordTrace tailWord_1738925 prefixEnd_1738925 595269564746476121093557 := by
  unfold tailWord_1738925
  simp only [CollatzResearch.WordTrace]
  refine ⟨63423805225179184590946229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42282536816786123060630819 63423805225179184590946229)
  ·
    refine ⟨5945981739860548555401209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63423805225179184590946229 5945981739860548555401209)
    ·
      refine ⟨4459486304895411416550907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945981739860548555401209 4459486304895411416550907)
      ·
        refine ⟨6689229457343117124826361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459486304895411416550907 6689229457343117124826361)
        ·
          refine ⟨5016922093007337843619771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6689229457343117124826361 5016922093007337843619771)
          ·
            refine ⟨7525383139511006765429657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016922093007337843619771 7525383139511006765429657)
            ·
              refine ⟨5644037354633255074072243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525383139511006765429657 5644037354633255074072243)
              ·
                refine ⟨8466056031949882611108365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644037354633255074072243 8466056031949882611108365)
                ·
                  refine ⟨3174771011981205979165637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8466056031949882611108365 3174771011981205979165637)
                  ·
                    refine ⟨595269564746476121093557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174771011981205979165637 595269564746476121093557)
                    ·
                      rfl

theorem cell22_1738925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1738925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738925 prefixEnd_1738925 := by exact prefixLift 1738925
  have htrace : WordTrace (prefixWord ++ tailWord_1738925) baseStart_1738925 baseEnd_1738925 := by
    simpa [prefixWord, tailWord_1738925, baseEnd_1738925] using wordTrace_append hprefix tailTrace_1738925
  have hstable : (prefixWord ++ tailWord_1738925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738925).length < 2 ^ (prefixWord ++ tailWord_1738925).sum := by decide
  have hdescent : baseEnd_1738925 < baseStart_1738925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738938 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1738938 : Nat := 118140960795 + 1738938 * 2 ^ 59
def prefixEnd_1738938 : Nat := 4983230072969 + 3 ^ 40 * 1738938 * 2
def baseEnd_1738938 : Nat := 595274014912148420518517

theorem tailTrace_1738938 : CollatzResearch.WordTrace tailWord_1738938 prefixEnd_1738938 595274014912148420518517 := by
  unfold tailWord_1738938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856069843533021952792367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42282852916088058540779645 15856069843533021952792367)
  ·
    refine ⟨23784104765299532929188551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15856069843533021952792367 23784104765299532929188551)
    ·
      refine ⟨35676157147949299393782827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23784104765299532929188551 35676157147949299393782827)
      ·
        refine ⟨53514235721923949090674241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35676157147949299393782827 53514235721923949090674241)
        ·
          refine ⟨40135676791442961818005681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53514235721923949090674241 40135676791442961818005681)
          ·
            refine ⟨30101757593582221363504261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40135676791442961818005681 30101757593582221363504261)
            ·
              refine ⟨5644079548796666505657049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30101757593582221363504261 5644079548796666505657049)
              ·
                refine ⟨4233059661597499879242787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644079548796666505657049 4233059661597499879242787)
                ·
                  refine ⟨6349589492396249818864181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233059661597499879242787 6349589492396249818864181)
                  ·
                    refine ⟨595274014912148420518517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6349589492396249818864181 595274014912148420518517)
                    ·
                      rfl

theorem cell22_1738938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1738938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738938 prefixEnd_1738938 := by exact prefixLift 1738938
  have htrace : WordTrace (prefixWord ++ tailWord_1738938) baseStart_1738938 baseEnd_1738938 := by
    simpa [prefixWord, tailWord_1738938, baseEnd_1738938] using wordTrace_append hprefix tailTrace_1738938
  have hstable : (prefixWord ++ tailWord_1738938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738938).length < 2 ^ (prefixWord ++ tailWord_1738938).sum := by decide
  have hdescent : baseEnd_1738938 < baseStart_1738938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738942 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1738942 : Nat := 118140960795 + 1738942 * 2 ^ 59
def prefixEnd_1738942 : Nat := 4983230072969 + 3 ^ 40 * 1738942 * 2
def baseEnd_1738942 : Nat := 595275384193893743418505

theorem tailTrace_1738942 : CollatzResearch.WordTrace tailWord_1738942 prefixEnd_1738942 595275384193893743418505 := by
  unfold tailWord_1738942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928053158264699561789385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42282950177411730996210053 7928053158264699561789385)
  ·
    refine ⟨5946039868698524671342039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7928053158264699561789385 5946039868698524671342039)
    ·
      refine ⟨8919059803047787007013059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946039868698524671342039 8919059803047787007013059)
      ·
        refine ⟨13378589704571680510519589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919059803047787007013059 13378589704571680510519589)
        ·
          refine ⟨2508485569607190095722423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13378589704571680510519589 2508485569607190095722423)
          ·
            refine ⟨3762728354410785143583635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508485569607190095722423 3762728354410785143583635)
            ·
              refine ⟨5644092531616177715375453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762728354410785143583635 5644092531616177715375453)
              ·
                refine ⟨2116534699356066643265795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5644092531616177715375453 2116534699356066643265795)
                ·
                  refine ⟨3174802049034099964898693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116534699356066643265795 3174802049034099964898693)
                  ·
                    refine ⟨595275384193893743418505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3174802049034099964898693 595275384193893743418505)
                    ·
                      rfl

theorem cell22_1738942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1738942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1738942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1738942 prefixEnd_1738942 := by exact prefixLift 1738942
  have htrace : WordTrace (prefixWord ++ tailWord_1738942) baseStart_1738942 baseEnd_1738942 := by
    simpa [prefixWord, tailWord_1738942, baseEnd_1738942] using wordTrace_append hprefix tailTrace_1738942
  have hstable : (prefixWord ++ tailWord_1738942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738942).length < 2 ^ (prefixWord ++ tailWord_1738942).sum := by decide
  have hdescent : baseEnd_1738942 < baseStart_1738942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739017 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_1739017 : Nat := 118140960795 + 1739017 * 2 ^ 59
def prefixEnd_1739017 : Nat := 4983230072969 + 3 ^ 40 * 1739017 * 2
def baseEnd_1739017 : Nat := 595301058226618547793275

theorem tailTrace_1739017 : CollatzResearch.WordTrace tailWord_1739017 prefixEnd_1739017 595301058226618547793275 := by
  unfold tailWord_1739017
  simp only [CollatzResearch.WordTrace]
  refine ⟨63427160740845884303295305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42284773827230589535530203 63427160740845884303295305)
  ·
    refine ⟨47570370555634413227471479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63427160740845884303295305 47570370555634413227471479)
    ·
      refine ⟨71355555833451619841207219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47570370555634413227471479 71355555833451619841207219)
      ·
        refine ⟨107033333750177429761810829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71355555833451619841207219 107033333750177429761810829)
        ·
          refine ⟨40137500156316536160679061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107033333750177429761810829 40137500156316536160679061)
          ·
            refine ⟨1881445319827337632531831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40137500156316536160679061 1881445319827337632531831)
            ·
              refine ⟨2822167979741006448797747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881445319827337632531831 2822167979741006448797747)
              ·
                refine ⟨4233251969611509673196621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822167979741006448797747 4233251969611509673196621)
                ·
                  refine ⟨1587469488604316127448733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4233251969611509673196621 1587469488604316127448733)
                  ·
                    refine ⟨595301058226618547793275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587469488604316127448733 595301058226618547793275)
                    ·
                      rfl

theorem cell22_1739017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_1739017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739017 prefixEnd_1739017 := by exact prefixLift 1739017
  have htrace : WordTrace (prefixWord ++ tailWord_1739017) baseStart_1739017 baseEnd_1739017 := by
    simpa [prefixWord, tailWord_1739017, baseEnd_1739017] using wordTrace_append hprefix tailTrace_1739017
  have hstable : (prefixWord ++ tailWord_1739017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739017).length < 2 ^ (prefixWord ++ tailWord_1739017).sum := by decide
  have hdescent : baseEnd_1739017 < baseStart_1739017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739090 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1739090 : Nat := 118140960795 + 1739090 * 2 ^ 59
def prefixEnd_1739090 : Nat := 4983230072969 + 3 ^ 40 * 1739090 * 2
def baseEnd_1739090 : Nat := 595326047618470690718051

theorem tailTrace_1739090 : CollatzResearch.WordTrace tailWord_1739090 prefixEnd_1739090 595326047618470690718051 := by
  unfold tailWord_1739090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15857455817395354442675681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42286548846387611847135149 15857455817395354442675681)
  ·
    refine ⟨11893091863046515832006761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15857455817395354442675681 11893091863046515832006761)
    ·
      refine ⟨8919818897284886874005071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11893091863046515832006761 8919818897284886874005071)
      ·
        refine ⟨13379728345927330311007607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919818897284886874005071 13379728345927330311007607)
        ·
          refine ⟨20069592518890995466511411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13379728345927330311007607 20069592518890995466511411)
          ·
            refine ⟨30104388778336493199767117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20069592518890995466511411 30104388778336493199767117)
            ·
              refine ⟨11289145791876184949912669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30104388778336493199767117 11289145791876184949912669)
              ·
                refine ⟨4233429671953569356217251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11289145791876184949912669 4233429671953569356217251)
                ·
                  refine ⟨6350144507930354034325877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233429671953569356217251 6350144507930354034325877)
                  ·
                    refine ⟨595326047618470690718051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6350144507930354034325877 595326047618470690718051)
                    ·
                      rfl

theorem cell22_1739090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1739090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739090 prefixEnd_1739090 := by exact prefixLift 1739090
  have htrace : WordTrace (prefixWord ++ tailWord_1739090) baseStart_1739090 baseEnd_1739090 := by
    simpa [prefixWord, tailWord_1739090, baseEnd_1739090] using wordTrace_append hprefix tailTrace_1739090
  have hstable : (prefixWord ++ tailWord_1739090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739090).length < 2 ^ (prefixWord ++ tailWord_1739090).sum := by decide
  have hdescent : baseEnd_1739090 < baseStart_1739090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739102 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1739102 : Nat := 118140960795 + 1739102 * 2 ^ 59
def prefixEnd_1739102 : Nat := 4983230072969 + 3 ^ 40 * 1739102 * 2
def baseEnd_1739102 : Nat := 595330155463706659418015

theorem tailTrace_1739102 : CollatzResearch.WordTrace tailWord_1739102 prefixEnd_1739102 595330155463706659418015 := by
  unfold tailWord_1739102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928782618192242977517445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42286840630358629213426373 7928782618192242977517445)
  ·
    refine ⟨1486646740911045558284521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7928782618192242977517445 1486646740911045558284521)
    ·
      refine ⟨1114985055683284168713391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486646740911045558284521 1114985055683284168713391)
      ·
        refine ⟨1672477583524926253070087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114985055683284168713391 1672477583524926253070087)
        ·
          refine ⟨2508716375287389379605131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672477583524926253070087 2508716375287389379605131)
          ·
            refine ⟨3763074562931084069407697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508716375287389379605131 3763074562931084069407697)
            ·
              refine ⟨2822305922198313052055773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763074562931084069407697 2822305922198313052055773)
              ·
                refine ⟨1058364720824367394520915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2822305922198313052055773 1058364720824367394520915)
                ·
                  refine ⟨1587547081236551091781373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058364720824367394520915 1587547081236551091781373)
                  ·
                    refine ⟨595330155463706659418015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587547081236551091781373 595330155463706659418015)
                    ·
                      rfl

theorem cell22_1739102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1739102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739102 prefixEnd_1739102 := by exact prefixLift 1739102
  have htrace : WordTrace (prefixWord ++ tailWord_1739102) baseStart_1739102 baseEnd_1739102 := by
    simpa [prefixWord, tailWord_1739102, baseEnd_1739102] using wordTrace_append hprefix tailTrace_1739102
  have hstable : (prefixWord ++ tailWord_1739102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739102).length < 2 ^ (prefixWord ++ tailWord_1739102).sum := by decide
  have hdescent : baseEnd_1739102 < baseStart_1739102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739103 : List Nat := [1, 1, 2, 3, 1, 2, 2, 10]
def baseStart_1739103 : Nat := 118140960795 + 1739103 * 2 ^ 59
def prefixEnd_1739103 : Nat := 4983230072969 + 3 ^ 40 * 1739103 * 2
def baseEnd_1739103 : Nat := 66147833087126998904779

theorem tailTrace_1739103 : CollatzResearch.WordTrace tailWord_1739103 prefixEnd_1739103 66147833087126998904779 := by
  unfold tailWord_1739103
  simp only [CollatzResearch.WordTrace]
  refine ⟨63430297418534320990925963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42286864945689547327283975 63430297418534320990925963)
  ·
    refine ⟨95145446127801481486388945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63430297418534320990925963 95145446127801481486388945)
    ·
      refine ⟨71359084595851111114791709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95145446127801481486388945 71359084595851111114791709)
      ·
        refine ⟨26759656723444166668046891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71359084595851111114791709 26759656723444166668046891)
        ·
          refine ⟨40139485085166250002070337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26759656723444166668046891 40139485085166250002070337)
          ·
            refine ⟨30104613813874687501552753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40139485085166250002070337 30104613813874687501552753)
            ·
              refine ⟨22578460360406015626164565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30104613813874687501552753 22578460360406015626164565)
              ·
                refine ⟨66147833087126998904779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22578460360406015626164565 66147833087126998904779)
                ·
                  rfl

theorem cell22_1739103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 10].length) (baseStart_1739103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739103 prefixEnd_1739103 := by exact prefixLift 1739103
  have htrace : WordTrace (prefixWord ++ tailWord_1739103) baseStart_1739103 baseEnd_1739103 := by
    simpa [prefixWord, tailWord_1739103, baseEnd_1739103] using wordTrace_append hprefix tailTrace_1739103
  have hstable : (prefixWord ++ tailWord_1739103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739103).length < 2 ^ (prefixWord ++ tailWord_1739103).sum := by decide
  have hdescent : baseEnd_1739103 < baseStart_1739103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739135 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 7, 3]
def baseStart_1739135 : Nat := 118140960795 + 1739135 * 2 ^ 59
def prefixEnd_1739135 : Nat := 4983230072969 + 3 ^ 40 * 1739135 * 2
def baseEnd_1739135 : Nat := 595341452038105573342913

theorem tailTrace_1739135 : CollatzResearch.WordTrace tailWord_1739135 prefixEnd_1739135 595341452038105573342913 := by
  unfold tailWord_1739135
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431464554418390456090859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42287643036278926970727239 63431464554418390456090859)
  ·
    refine ⟨95147196831627585684136289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63431464554418390456090859 95147196831627585684136289)
    ·
      refine ⟨71360397623720689263102217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95147196831627585684136289 71360397623720689263102217)
      ·
        refine ⟨53520298217790516947326663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71360397623720689263102217 53520298217790516947326663)
        ·
          refine ⟨80280447326685775420989995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53520298217790516947326663 80280447326685775420989995)
          ·
            refine ⟨120420670990028663131484993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80280447326685775420989995 120420670990028663131484993)
            ·
              refine ⟨90315503242521497348613745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120420670990028663131484993 90315503242521497348613745)
              ·
                refine ⟨67736627431891123011460309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90315503242521497348613745 67736627431891123011460309)
                ·
                  refine ⟨1587577205434948195581101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 67736627431891123011460309 1587577205434948195581101)
                  ·
                    refine ⟨595341452038105573342913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587577205434948195581101 595341452038105573342913)
                    ·
                      rfl

theorem cell22_1739135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_1739135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739135 prefixEnd_1739135 := by exact prefixLift 1739135
  have htrace : WordTrace (prefixWord ++ tailWord_1739135) baseStart_1739135 baseEnd_1739135 := by
    simpa [prefixWord, tailWord_1739135, baseEnd_1739135] using wordTrace_append hprefix tailTrace_1739135
  have hstable : (prefixWord ++ tailWord_1739135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739135).length < 2 ^ (prefixWord ++ tailWord_1739135).sum := by decide
  have hdescent : baseEnd_1739135 < baseStart_1739135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739186 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1739186 : Nat := 118140960795 + 1739186 * 2 ^ 59
def prefixEnd_1739186 : Nat := 4983230072969 + 3 ^ 40 * 1739186 * 2
def baseEnd_1739186 : Nat := 595358910380358440317757

theorem tailTrace_1739186 : CollatzResearch.WordTrace tailWord_1739186 prefixEnd_1739186 595358910380358440317757 := by
  unfold tailWord_1739186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858331169308406541549353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42288883118155750777464941 15858331169308406541549353)
  ·
    refine ⟨11893748376981304906162015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15858331169308406541549353 11893748376981304906162015)
    ·
      refine ⟨17840622565471957359243023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893748376981304906162015 17840622565471957359243023)
      ·
        refine ⟨26760933848207936038864535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17840622565471957359243023 26760933848207936038864535)
        ·
          refine ⟨40141400772311904058296803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26760933848207936038864535 40141400772311904058296803)
          ·
            refine ⟨60212101158467856087445205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40141400772311904058296803 60212101158467856087445205)
            ·
              refine ⟨1411221120901590377049497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60212101158467856087445205 1411221120901590377049497)
              ·
                refine ⟨1058415840676192782787123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411221120901590377049497 1058415840676192782787123)
                ·
                  refine ⟨1587623761014289174180685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058415840676192782787123 1587623761014289174180685)
                  ·
                    refine ⟨595358910380358440317757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587623761014289174180685 595358910380358440317757)
                    ·
                      rfl

theorem cell22_1739186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1739186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739186 prefixEnd_1739186 := by exact prefixLift 1739186
  have htrace : WordTrace (prefixWord ++ tailWord_1739186) baseStart_1739186 baseEnd_1739186 := by
    simpa [prefixWord, tailWord_1739186, baseEnd_1739186] using wordTrace_append hprefix tailTrace_1739186
  have hstable : (prefixWord ++ tailWord_1739186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739186).length < 2 ^ (prefixWord ++ tailWord_1739186).sum := by decide
  have hdescent : baseEnd_1739186 < baseStart_1739186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739210 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1739210 : Nat := 118140960795 + 1739210 * 2 ^ 59
def prefixEnd_1739210 : Nat := 4983230072969 + 3 ^ 40 * 1739210 * 2
def baseEnd_1739210 : Nat := 198455708690276792572561

theorem tailTrace_1739210 : CollatzResearch.WordTrace tailWord_1739210 prefixEnd_1739210 198455708690276792572561 := by
  unfold tailWord_1739210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858550007286669566267771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42289466686097785510047389 15858550007286669566267771)
  ·
    refine ⟨23787825010930004349401657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15858550007286669566267771 23787825010930004349401657)
    ·
      refine ⟨17840868758197503262051243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23787825010930004349401657 17840868758197503262051243)
      ·
        refine ⟨26761303137296254893076865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17840868758197503262051243 26761303137296254893076865)
        ·
          refine ⟨20070977352972191169807649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26761303137296254893076865 20070977352972191169807649)
          ·
            refine ⟨15053233014729143377355737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20070977352972191169807649 15053233014729143377355737)
            ·
              refine ⟨11289924761046857533016803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15053233014729143377355737 11289924761046857533016803)
              ·
                refine ⟨16934887141570286299525205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289924761046857533016803 16934887141570286299525205)
                ·
                  refine ⟨198455708690276792572561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16934887141570286299525205 198455708690276792572561)
                  ·
                    rfl

theorem cell22_1739210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1739210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739210 prefixEnd_1739210 := by exact prefixLift 1739210
  have htrace : WordTrace (prefixWord ++ tailWord_1739210) baseStart_1739210 baseEnd_1739210 := by
    simpa [prefixWord, tailWord_1739210, baseEnd_1739210] using wordTrace_append hprefix tailTrace_1739210
  have hstable : (prefixWord ++ tailWord_1739210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739210).length < 2 ^ (prefixWord ++ tailWord_1739210).sum := by decide
  have hdescent : baseEnd_1739210 < baseStart_1739210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739338 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1739338 : Nat := 118140960795 + 1739338 * 2 ^ 59
def prefixEnd_1739338 : Nat := 4983230072969 + 3 ^ 40 * 1739338 * 2
def baseEnd_1739338 : Nat := 595410943086680710517291

theorem tailTrace_1739338 : CollatzResearch.WordTrace tailWord_1739338 prefixEnd_1739338 595410943086680710517291 := by
  unfold tailWord_1739338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859717143170739031432667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42292579048455304083820445 15859717143170739031432667)
  ·
    refine ⟨23789575714756108547149001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15859717143170739031432667 23789575714756108547149001)
    ·
      refine ⟨17842181786067081410361751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23789575714756108547149001 17842181786067081410361751)
      ·
        refine ⟨26763272679100622115542627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17842181786067081410361751 26763272679100622115542627)
        ·
          refine ⟨40144909018650933173313941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26763272679100622115542627 40144909018650933173313941)
          ·
            refine ⟨1881792610249262492499091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40144909018650933173313941 1881792610249262492499091)
            ·
              refine ⟨2822688915373893738748637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881792610249262492499091 2822688915373893738748637)
              ·
                refine ⟨1058508343265210152030739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2822688915373893738748637 1058508343265210152030739)
                ·
                  refine ⟨1587762514897815228046109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058508343265210152030739 1587762514897815228046109)
                  ·
                    refine ⟨595410943086680710517291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587762514897815228046109 595410943086680710517291)
                    ·
                      rfl

theorem cell22_1739338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1739338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739338 prefixEnd_1739338 := by exact prefixLift 1739338
  have htrace : WordTrace (prefixWord ++ tailWord_1739338) baseStart_1739338 baseEnd_1739338 := by
    simpa [prefixWord, tailWord_1739338, baseEnd_1739338] using wordTrace_append hprefix tailTrace_1739338
  have hstable : (prefixWord ++ tailWord_1739338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739338).length < 2 ^ (prefixWord ++ tailWord_1739338).sum := by decide
  have hdescent : baseEnd_1739338 < baseStart_1739338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739368 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_1739368 : Nat := 118140960795 + 1739368 * 2 ^ 59
def prefixEnd_1739368 : Nat := 4983230072969 + 3 ^ 40 * 1739368 * 2
def baseEnd_1739368 : Nat := 198473737566590210755733

theorem tailTrace_1739368 : CollatzResearch.WordTrace tailWord_1739368 prefixEnd_1739368 198473737566590210755733 := by
  unfold tailWord_1739368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719981381287135624661379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42293308508382847499548505 31719981381287135624661379)
  ·
    refine ⟨47579972071930703436992069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31719981381287135624661379 47579972071930703436992069)
    ·
      refine ⟨8921244763487006894436013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47579972071930703436992069 8921244763487006894436013)
      ·
        refine ⟨3345466786307627585413505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8921244763487006894436013 3345466786307627585413505)
        ·
          refine ⟨2509100089730720689060129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345466786307627585413505 2509100089730720689060129)
          ·
            refine ⟨1881825067298040516795097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509100089730720689060129 1881825067298040516795097)
            ·
              refine ⟨1411368800473530387596323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881825067298040516795097 1411368800473530387596323)
              ·
                refine ⟨2117053200710295581394485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411368800473530387596323 2117053200710295581394485)
                ·
                  refine ⟨198473737566590210755733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117053200710295581394485 198473737566590210755733)
                  ·
                    rfl

theorem cell22_1739368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_1739368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739368 prefixEnd_1739368 := by exact prefixLift 1739368
  have htrace : WordTrace (prefixWord ++ tailWord_1739368) baseStart_1739368 baseEnd_1739368 := by
    simpa [prefixWord, tailWord_1739368, baseEnd_1739368] using wordTrace_append hprefix tailTrace_1739368
  have hstable : (prefixWord ++ tailWord_1739368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739368).length < 2 ^ (prefixWord ++ tailWord_1739368).sum := by decide
  have hdescent : baseEnd_1739368 < baseStart_1739368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739381 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1739381 : Nat := 118140960795 + 1739381 * 2 ^ 59
def prefixEnd_1739381 : Nat := 4983230072969 + 3 ^ 40 * 1739381 * 2
def baseEnd_1739381 : Nat := 595425662865442931692159

theorem tailTrace_1739381 : CollatzResearch.WordTrace tailWord_1739381 prefixEnd_1739381 595425662865442931692159 := by
  unfold tailWord_1739381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63440436911527174469545997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42293624607684782979697331 63440436911527174469545997)
  ·
    refine ⟨23790163841822690426079749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63440436911527174469545997 23790163841822690426079749)
    ·
      refine ⟨4460655720341754454889953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23790163841822690426079749 4460655720341754454889953)
      ·
        refine ⟨3345491790256315841167465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4460655720341754454889953 3345491790256315841167465)
        ·
          refine ⟨2509118842692236880875599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345491790256315841167465 2509118842692236880875599)
          ·
            refine ⟨3763678264038355321313399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509118842692236880875599 3763678264038355321313399)
            ·
              refine ⟨5645517396057532981970099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763678264038355321313399 5645517396057532981970099)
              ·
                refine ⟨8468276094086299472955149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645517396057532981970099 8468276094086299472955149)
                ·
                  refine ⟨3175603535282362302358181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8468276094086299472955149 3175603535282362302358181)
                  ·
                    refine ⟨595425662865442931692159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175603535282362302358181 595425662865442931692159)
                    ·
                      rfl

theorem cell22_1739381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1739381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739381 prefixEnd_1739381 := by exact prefixLift 1739381
  have htrace : WordTrace (prefixWord ++ tailWord_1739381) baseStart_1739381 baseEnd_1739381 := by
    simpa [prefixWord, tailWord_1739381, baseEnd_1739381] using wordTrace_append hprefix tailTrace_1739381
  have hstable : (prefixWord ++ tailWord_1739381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739381).length < 2 ^ (prefixWord ++ tailWord_1739381).sum := by decide
  have hdescent : baseEnd_1739381 < baseStart_1739381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739439 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 5, 3]
def baseStart_1739439 : Nat := 118140960795 + 1739439 * 2 ^ 59
def prefixEnd_1739439 : Nat := 4983230072969 + 3 ^ 40 * 1739439 * 2
def baseEnd_1739439 : Nat := 595445517450750113741981

theorem tailTrace_1739439 : CollatzResearch.WordTrace tailWord_1739439 prefixEnd_1739439 595445517450750113741981 := by
  unfold tailWord_1739439
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442552345317050375157371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42295034896878033583438247 63442552345317050375157371)
  ·
    refine ⟨95163828517975575562736057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63442552345317050375157371 95163828517975575562736057)
    ·
      refine ⟨71372871388481681672052043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95163828517975575562736057 71372871388481681672052043)
      ·
        refine ⟨107059307082722522508078065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71372871388481681672052043 107059307082722522508078065)
        ·
          refine ⟨80294480312041891881058549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107059307082722522508078065 80294480312041891881058549)
          ·
            refine ⟨7527607529253927363849239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80294480312041891881058549 7527607529253927363849239)
            ·
              refine ⟨11291411293880891045773859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527607529253927363849239 11291411293880891045773859)
              ·
                refine ⟨16937116940821336568660789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291411293880891045773859 16937116940821336568660789)
                ·
                  refine ⟨1587854713202000303311949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16937116940821336568660789 1587854713202000303311949)
                  ·
                    refine ⟨595445517450750113741981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587854713202000303311949 595445517450750113741981)
                    ·
                      rfl

theorem cell22_1739439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_1739439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739439 prefixEnd_1739439 := by exact prefixLift 1739439
  have htrace : WordTrace (prefixWord ++ tailWord_1739439) baseStart_1739439 baseEnd_1739439 := by
    simpa [prefixWord, tailWord_1739439, baseEnd_1739439] using wordTrace_append hprefix tailTrace_1739439
  have hstable : (prefixWord ++ tailWord_1739439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739439).length < 2 ^ (prefixWord ++ tailWord_1739439).sum := by decide
  have hdescent : baseEnd_1739439 < baseStart_1739439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739516 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_1739516 : Nat := 118140960795 + 1739516 * 2 ^ 59
def prefixEnd_1739516 : Nat := 4983230072969 + 3 ^ 40 * 1739516 * 2
def baseEnd_1739516 : Nat := 595471876124347579566745

theorem tailTrace_1739516 : CollatzResearch.WordTrace tailWord_1739516 prefixEnd_1739516 595471876124347579566745 := by
  unfold tailWord_1739516
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722680383019046262855201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42296907177358728350473601 31722680383019046262855201)
  ·
    refine ⟨23792010287264284697141401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31722680383019046262855201 23792010287264284697141401)
    ·
      refine ⟨17844007715448213522856051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23792010287264284697141401 17844007715448213522856051)
      ·
        refine ⟨26766011573172320284284077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844007715448213522856051 26766011573172320284284077)
        ·
          refine ⟨10037254339939620106606529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26766011573172320284284077 10037254339939620106606529)
          ·
            refine ⟨7527940754954715079954897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10037254339939620106606529 7527940754954715079954897)
            ·
              refine ⟨5645955566216036309966173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7527940754954715079954897 5645955566216036309966173)
              ·
                refine ⟨2117233337331013616237315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645955566216036309966173 2117233337331013616237315)
                ·
                  refine ⟨3175850005996520424355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117233337331013616237315 3175850005996520424355973)
                  ·
                    refine ⟨595471876124347579566745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175850005996520424355973 595471876124347579566745)
                    ·
                      rfl

theorem cell22_1739516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_1739516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739516 prefixEnd_1739516 := by exact prefixLift 1739516
  have htrace : WordTrace (prefixWord ++ tailWord_1739516) baseStart_1739516 baseEnd_1739516 := by
    simpa [prefixWord, tailWord_1739516, baseEnd_1739516] using wordTrace_append hprefix tailTrace_1739516
  have hstable : (prefixWord ++ tailWord_1739516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739516).length < 2 ^ (prefixWord ++ tailWord_1739516).sum := by decide
  have hdescent : baseEnd_1739516 < baseStart_1739516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739544 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_1739544 : Nat := 118140960795 + 1739544 * 2 ^ 59
def prefixEnd_1739544 : Nat := 4983230072969 + 3 ^ 40 * 1739544 * 2
def baseEnd_1739544 : Nat := 595481461096564839866659

theorem tailTrace_1739544 : CollatzResearch.WordTrace tailWord_1739544 prefixEnd_1739544 595481461096564839866659 := by
  unfold tailWord_1739544
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723191004968326653864843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42297588006624435538486457 31723191004968326653864843)
  ·
    refine ⟨47584786507452489980797265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31723191004968326653864843 47584786507452489980797265)
    ·
      refine ⟨35688589880589367485597949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47584786507452489980797265 35688589880589367485597949)
      ·
        refine ⟨13383221205221012807099231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35688589880589367485597949 13383221205221012807099231)
        ·
          refine ⟨20074831807831519210648847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383221205221012807099231 20074831807831519210648847)
          ·
            refine ⟨30112247711747278815973271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20074831807831519210648847 30112247711747278815973271)
            ·
              refine ⟨45168371567620918223959907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30112247711747278815973271 45168371567620918223959907)
              ·
                refine ⟨67752557351431377335939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45168371567620918223959907 67752557351431377335939861)
                ·
                  refine ⟨3175901125848345812622181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67752557351431377335939861 3175901125848345812622181)
                  ·
                    refine ⟨595481461096564839866659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3175901125848345812622181 595481461096564839866659)
                    ·
                      rfl

theorem cell22_1739544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_1739544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739544 prefixEnd_1739544 := by exact prefixLift 1739544
  have htrace : WordTrace (prefixWord ++ tailWord_1739544) baseStart_1739544 baseEnd_1739544 := by
    simpa [prefixWord, tailWord_1739544, baseEnd_1739544] using wordTrace_append hprefix tailTrace_1739544
  have hstable : (prefixWord ++ tailWord_1739544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739544).length < 2 ^ (prefixWord ++ tailWord_1739544).sum := by decide
  have hdescent : baseEnd_1739544 < baseStart_1739544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739582 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1739582 : Nat := 118140960795 + 1739582 * 2 ^ 59
def prefixEnd_1739582 : Nat := 4983230072969 + 3 ^ 40 * 1739582 * 2
def baseEnd_1739582 : Nat := 198498156424381802472181

theorem tailTrace_1739582 : CollatzResearch.WordTrace tailWord_1739582 prefixEnd_1739582 198498156424381802472181 := by
  unfold tailWord_1739582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930970997974873224701625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42298511989199323865075333 7930970997974873224701625)
  ·
    refine ⟨5948228248481154918526219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7930970997974873224701625 5948228248481154918526219)
    ·
      refine ⟨8922342372721732377789329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948228248481154918526219 8922342372721732377789329)
      ·
        refine ⟨6691756779541299283341997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8922342372721732377789329 6691756779541299283341997)
        ·
          refine ⟨2509408792327987231253249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6691756779541299283341997 2509408792327987231253249)
          ·
            refine ⟨1882056594245990423439937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509408792327987231253249 1882056594245990423439937)
            ·
              refine ⟨1411542445684492817579953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882056594245990423439937 1411542445684492817579953)
              ·
                refine ⟨1058656834263369613184965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411542445684492817579953 1058656834263369613184965)
                ·
                  refine ⟨198498156424381802472181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058656834263369613184965 198498156424381802472181)
                  ·
                    rfl

theorem cell22_1739582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1739582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739582 prefixEnd_1739582 := by exact prefixLift 1739582
  have htrace : WordTrace (prefixWord ++ tailWord_1739582) baseStart_1739582 baseEnd_1739582 := by
    simpa [prefixWord, tailWord_1739582, baseEnd_1739582] using wordTrace_append hprefix tailTrace_1739582
  have hstable : (prefixWord ++ tailWord_1739582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739582).length < 2 ^ (prefixWord ++ tailWord_1739582).sum := by decide
  have hdescent : baseEnd_1739582 < baseStart_1739582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739591 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1739591 : Nat := 118140960795 + 1739591 * 2 ^ 59
def prefixEnd_1739591 : Nat := 4983230072969 + 3 ^ 40 * 1739591 * 2
def baseEnd_1739591 : Nat := 595497550157072383941515

theorem tailTrace_1739591 : CollatzResearch.WordTrace tailWord_1739591 prefixEnd_1739591 595497550157072383941515 := by
  unfold tailWord_1739591
  simp only [CollatzResearch.WordTrace]
  refine ⟨63448096240766380334690627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42298730827177586889793751 63448096240766380334690627)
  ·
    refine ⟨95172144361149570502035941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63448096240766380334690627 95172144361149570502035941)
    ·
      refine ⟨17844777067715544469131739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95172144361149570502035941 17844777067715544469131739)
      ·
        refine ⟨26767165601573316703697609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844777067715544469131739 26767165601573316703697609)
        ·
          refine ⟨20075374201179987527773207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26767165601573316703697609 20075374201179987527773207)
          ·
            refine ⟨30113061301769981291659811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075374201179987527773207 30113061301769981291659811)
            ·
              refine ⟨45169591952654971937489717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30113061301769981291659811 45169591952654971937489717)
              ·
                refine ⟨4234649245561403619139661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45169591952654971937489717 4234649245561403619139661)
                ·
                  refine ⟨1587993467085526357177373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4234649245561403619139661 1587993467085526357177373)
                  ·
                    refine ⟨595497550157072383941515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1587993467085526357177373 595497550157072383941515)
                    ·
                      rfl

theorem cell22_1739591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1739591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739591 prefixEnd_1739591 := by exact prefixLift 1739591
  have htrace : WordTrace (prefixWord ++ tailWord_1739591) baseStart_1739591 baseEnd_1739591 := by
    simpa [prefixWord, tailWord_1739591, baseEnd_1739591] using wordTrace_append hprefix tailTrace_1739591
  have hstable : (prefixWord ++ tailWord_1739591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739591).length < 2 ^ (prefixWord ++ tailWord_1739591).sum := by decide
  have hdescent : baseEnd_1739591 < baseStart_1739591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739638 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1739638 : Nat := 118140960795 + 1739638 * 2 ^ 59
def prefixEnd_1739638 : Nat := 4983230072969 + 3 ^ 40 * 1739638 * 2
def baseEnd_1739638 : Nat := 198504546405859976005457

theorem tailTrace_1739638 : CollatzResearch.WordTrace tailWord_1739638 prefixEnd_1739638 198504546405859976005457 := by
  unfold tailWord_1739638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965613154474756710103223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42299873647730738241101045 3965613154474756710103223)
  ·
    refine ⟨5948419731712135065154835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965613154474756710103223 5948419731712135065154835)
    ·
      refine ⟨8922629597568202597732253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948419731712135065154835 8922629597568202597732253)
      ·
        refine ⟨3345986099088075974149595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8922629597568202597732253 3345986099088075974149595)
        ·
          refine ⟨5018979148632113961224393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345986099088075974149595 5018979148632113961224393)
          ·
            refine ⟨3764234361474085470918295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018979148632113961224393 3764234361474085470918295)
            ·
              refine ⟨5646351542211128206377443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764234361474085470918295 5646351542211128206377443)
              ·
                refine ⟨8469527313316692309566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646351542211128206377443 8469527313316692309566165)
                ·
                  refine ⟨198504546405859976005457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8469527313316692309566165 198504546405859976005457)
                  ·
                    rfl

theorem cell22_1739638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1739638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739638 prefixEnd_1739638 := by exact prefixLift 1739638
  have htrace : WordTrace (prefixWord ++ tailWord_1739638) baseStart_1739638 baseEnd_1739638 := by
    simpa [prefixWord, tailWord_1739638, baseEnd_1739638] using wordTrace_append hprefix tailTrace_1739638
  have hstable : (prefixWord ++ tailWord_1739638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739638).length < 2 ^ (prefixWord ++ tailWord_1739638).sum := by decide
  have hdescent : baseEnd_1739638 < baseStart_1739638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739683 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 4]
def baseStart_1739683 : Nat := 118140960795 + 1739683 * 2 ^ 59
def prefixEnd_1739683 : Nat := 4983230072969 + 3 ^ 40 * 1739683 * 2
def baseEnd_1739683 : Nat := 198509681212404936880411

theorem tailTrace_1739683 : CollatzResearch.WordTrace tailWord_1739683 prefixEnd_1739683 198509681212404936880411 := by
  unfold tailWord_1739683
  simp only [CollatzResearch.WordTrace]
  refine ⟨63451451756433080047039703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42300967837622053364693135 63451451756433080047039703)
  ·
    refine ⟨95177177634649620070559555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63451451756433080047039703 95177177634649620070559555)
    ·
      refine ⟨142765766451974430105839333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95177177634649620070559555 142765766451974430105839333)
      ·
        refine ⟨26768581209745205644844875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142765766451974430105839333 26768581209745205644844875)
        ·
          refine ⟨40152871814617808467267313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26768581209745205644844875 40152871814617808467267313)
          ·
            refine ⟨30114653860963356350450485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40152871814617808467267313 30114653860963356350450485)
            ·
              refine ⟨2823248799465314657854733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30114653860963356350450485 2823248799465314657854733)
              ·
                refine ⟨1058718299799492996695525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2823248799465314657854733 1058718299799492996695525)
                ·
                  refine ⟨198509681212404936880411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058718299799492996695525 198509681212404936880411)
                  ·
                    rfl

theorem cell22_1739683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 4].length) (baseStart_1739683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739683 prefixEnd_1739683 := by exact prefixLift 1739683
  have htrace : WordTrace (prefixWord ++ tailWord_1739683) baseStart_1739683 baseEnd_1739683 := by
    simpa [prefixWord, tailWord_1739683, baseEnd_1739683] using wordTrace_append hprefix tailTrace_1739683
  have hstable : (prefixWord ++ tailWord_1739683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739683).length < 2 ^ (prefixWord ++ tailWord_1739683).sum := by decide
  have hdescent : baseEnd_1739683 < baseStart_1739683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739700 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1739700 : Nat := 118140960795 + 1739700 * 2 ^ 59
def prefixEnd_1739700 : Nat := 4983230072969 + 3 ^ 40 * 1739700 * 2
def baseEnd_1739700 : Nat := 198511621028210810988727

theorem tailTrace_1739700 : CollatzResearch.WordTrace tailWord_1739700 prefixEnd_1739700 198511621028210810988727 := by
  unfold tailWord_1739700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726035898685745975204277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42301381198247661300272369 31726035898685745975204277)
  ·
    refine ⟨2974315865501788685175401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31726035898685745975204277 2974315865501788685175401)
    ·
      refine ⟨2230736899126341513881551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2974315865501788685175401 2230736899126341513881551)
      ·
        refine ⟨3346105348689512270822327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230736899126341513881551 3346105348689512270822327)
        ·
          refine ⟨5019158023034268406233491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346105348689512270822327 5019158023034268406233491)
          ·
            refine ⟨7528737034551402609350237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019158023034268406233491 7528737034551402609350237)
            ·
              refine ⟨2823276387956775978506339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7528737034551402609350237 2823276387956775978506339)
              ·
                refine ⟨4234914581935163967759509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823276387956775978506339 4234914581935163967759509)
                ·
                  refine ⟨198511621028210810988727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4234914581935163967759509 198511621028210810988727)
                  ·
                    rfl

theorem cell22_1739700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1739700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739700 prefixEnd_1739700 := by exact prefixLift 1739700
  have htrace : WordTrace (prefixWord ++ tailWord_1739700) baseStart_1739700 baseEnd_1739700 := by
    simpa [prefixWord, tailWord_1739700, baseEnd_1739700] using wordTrace_append hprefix tailTrace_1739700
  have hstable : (prefixWord ++ tailWord_1739700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739700).length < 2 ^ (prefixWord ++ tailWord_1739700).sum := by decide
  have hdescent : baseEnd_1739700 < baseStart_1739700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739730 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1739730 : Nat := 118140960795 + 1739730 * 2 ^ 59
def prefixEnd_1739730 : Nat := 4983230072969 + 3 ^ 40 * 1739730 * 2
def baseEnd_1739730 : Nat := 595545132697722354716089

theorem tailTrace_1739730 : CollatzResearch.WordTrace tailWord_1739730 prefixEnd_1739730 595545132697722354716089 := by
  unfold tailWord_1739730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863291496815701768500161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42302110658175204716000429 15863291496815701768500161)
  ·
    refine ⟨11897468622611776326375121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15863291496815701768500161 11897468622611776326375121)
    ·
      refine ⟨8923101466958832244781341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11897468622611776326375121 8923101466958832244781341)
      ·
        refine ⟨3346163050109562091793003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8923101466958832244781341 3346163050109562091793003)
        ·
          refine ⟨5019244575164343137689505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346163050109562091793003 5019244575164343137689505)
          ·
            refine ⟨3764433431373257353267129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019244575164343137689505 3764433431373257353267129)
            ·
              refine ⟨2823325073529943014950347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764433431373257353267129 2823325073529943014950347)
              ·
                refine ⟨4234987610294914522425521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823325073529943014950347 4234987610294914522425521)
                ·
                  refine ⟨3176240707721185891819141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234987610294914522425521 3176240707721185891819141)
                  ·
                    refine ⟨595545132697722354716089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176240707721185891819141 595545132697722354716089)
                    ·
                      rfl

theorem cell22_1739730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1739730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739730 prefixEnd_1739730 := by exact prefixLift 1739730
  have htrace : WordTrace (prefixWord ++ tailWord_1739730) baseStart_1739730 baseEnd_1739730 := by
    simpa [prefixWord, tailWord_1739730, baseEnd_1739730] using wordTrace_append hprefix tailTrace_1739730
  have hstable : (prefixWord ++ tailWord_1739730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739730).length < 2 ^ (prefixWord ++ tailWord_1739730).sum := by decide
  have hdescent : baseEnd_1739730 < baseStart_1739730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739762 : List Nat := [3, 2, 1, 5, 2, 1, 1, 7]
def baseStart_1739762 : Nat := 118140960795 + 1739762 * 2 ^ 59
def prefixEnd_1739762 : Nat := 4983230072969 + 3 ^ 40 * 1739762 * 2
def baseEnd_1739762 : Nat := 66172898550187215323999

theorem tailTrace_1739762 : CollatzResearch.WordTrace tailWord_1739762 prefixEnd_1739762 66172898550187215323999 := by
  unfold tailWord_1739762
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863583280786719134791385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42302888748764584359443693 15863583280786719134791385)
  ·
    refine ⟨11897687460590039351093539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15863583280786719134791385 11897687460590039351093539)
    ·
      refine ⟨17846531190885059026640309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897687460590039351093539 17846531190885059026640309)
      ·
        refine ⟨1673112299145474283747529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17846531190885059026640309 1673112299145474283747529)
        ·
          refine ⟨1254834224359105712810647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1673112299145474283747529 1254834224359105712810647)
          ·
            refine ⟨1882251336538658569215971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254834224359105712810647 1882251336538658569215971)
            ·
              refine ⟨2823377004807987853823957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882251336538658569215971 2823377004807987853823957)
              ·
                refine ⟨66172898550187215323999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2823377004807987853823957 66172898550187215323999)
                ·
                  rfl

theorem cell22_1739762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_1739762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739762 prefixEnd_1739762 := by exact prefixLift 1739762
  have htrace : WordTrace (prefixWord ++ tailWord_1739762) baseStart_1739762 baseEnd_1739762 := by
    simpa [prefixWord, tailWord_1739762, baseEnd_1739762] using wordTrace_append hprefix tailTrace_1739762
  have hstable : (prefixWord ++ tailWord_1739762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739762).length < 2 ^ (prefixWord ++ tailWord_1739762).sum := by decide
  have hdescent : baseEnd_1739762 < baseStart_1739762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739848 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1739848 : Nat := 118140960795 + 1739848 * 2 ^ 59
def prefixEnd_1739848 : Nat := 4983230072969 + 3 ^ 40 * 1739848 * 2
def baseEnd_1739848 : Nat := 595585526509209380265727

theorem tailTrace_1739848 : CollatzResearch.WordTrace tailWord_1739848 prefixEnd_1739848 595585526509209380265727 := by
  unfold tailWord_1739848
  simp only [CollatzResearch.WordTrace]
  refine ⟨31728734900417656613398099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42304979867223542151197465 31728734900417656613398099)
  ·
    refine ⟨47593102350626484920097149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31728734900417656613398099 47593102350626484920097149)
    ·
      refine ⟨17847413381484931845036431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47593102350626484920097149 17847413381484931845036431)
      ·
        refine ⟨26771120072227397767554647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847413381484931845036431 26771120072227397767554647)
        ·
          refine ⟨40156680108341096651331971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26771120072227397767554647 40156680108341096651331971)
          ·
            refine ⟨60235020162511644976997957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40156680108341096651331971 60235020162511644976997957)
            ·
              refine ⟨11294066280470933433187117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60235020162511644976997957 11294066280470933433187117)
              ·
                refine ⟨4235274855176600037445169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11294066280470933433187117 4235274855176600037445169)
                ·
                  refine ⟨3176456141382450028083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235274855176600037445169 3176456141382450028083877)
                  ·
                    refine ⟨595585526509209380265727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176456141382450028083877 595585526509209380265727)
                    ·
                      rfl

theorem cell22_1739848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1739848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739848 prefixEnd_1739848 := by exact prefixLift 1739848
  have htrace : WordTrace (prefixWord ++ tailWord_1739848) baseStart_1739848 baseEnd_1739848 := by
    simpa [prefixWord, tailWord_1739848, baseEnd_1739848] using wordTrace_append hprefix tailTrace_1739848
  have hstable : (prefixWord ++ tailWord_1739848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739848).length < 2 ^ (prefixWord ++ tailWord_1739848).sum := by decide
  have hdescent : baseEnd_1739848 < baseStart_1739848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739869 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1739869 : Nat := 118140960795 + 1739869 * 2 ^ 59
def prefixEnd_1739869 : Nat := 4983230072969 + 3 ^ 40 * 1739869 * 2
def baseEnd_1739869 : Nat := 198530905079457441830221

theorem tailTrace_1739869 : CollatzResearch.WordTrace tailWord_1739869 prefixEnd_1739869 198530905079457441830221 := by
  unfold tailWord_1739869
  simp only [CollatzResearch.WordTrace]
  refine ⟨63458235733759233813310661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42305490489172822542207107 63458235733759233813310661)
  ·
    refine ⟨11898419200079856339995749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63458235733759233813310661 11898419200079856339995749)
    ·
      refine ⟨2230953600014973063749203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11898419200079856339995749 2230953600014973063749203)
      ·
        refine ⟨3346430400022459595623805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230953600014973063749203 3346430400022459595623805)
        ·
          refine ⟨1254911400008422348358927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3346430400022459595623805 1254911400008422348358927)
          ·
            refine ⟨1882367100012633522538391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254911400008422348358927 1882367100012633522538391)
            ·
              refine ⟨2823550650018950283807587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882367100012633522538391 2823550650018950283807587)
              ·
                refine ⟨4235325975028425425711381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823550650018950283807587 4235325975028425425711381)
                ·
                  refine ⟨198530905079457441830221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4235325975028425425711381 198530905079457441830221)
                  ·
                    rfl

theorem cell22_1739869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1739869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739869 prefixEnd_1739869 := by exact prefixLift 1739869
  have htrace : WordTrace (prefixWord ++ tailWord_1739869) baseStart_1739869 baseEnd_1739869 := by
    simpa [prefixWord, tailWord_1739869, baseEnd_1739869] using wordTrace_append hprefix tailTrace_1739869
  have hstable : (prefixWord ++ tailWord_1739869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739869).length < 2 ^ (prefixWord ++ tailWord_1739869).sum := by decide
  have hdescent : baseEnd_1739869 < baseStart_1739869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739940 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1739940 : Nat := 118140960795 + 1739940 * 2 ^ 59
def prefixEnd_1739940 : Nat := 4983230072969 + 3 ^ 40 * 1739940 * 2
def baseEnd_1739940 : Nat := 595617019989351806965445

theorem tailTrace_1739940 : CollatzResearch.WordTrace tailWord_1739940 prefixEnd_1739940 595617019989351806965445 := by
  unfold tailWord_1739940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730412658251006469572637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42307216877668008626096849 31730412658251006469572637)
  ·
    refine ⟨11898904746844127426089739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31730412658251006469572637 11898904746844127426089739)
    ·
      refine ⟨17848357120266191139134609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898904746844127426089739 17848357120266191139134609)
      ·
        refine ⟨13386267840199643354350957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17848357120266191139134609 13386267840199643354350957)
        ·
          refine ⟨5019850440074866257881609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13386267840199643354350957 5019850440074866257881609)
          ·
            refine ⟨3764887830056149693411207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019850440074866257881609 3764887830056149693411207)
            ·
              refine ⟨5647331745084224540116811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764887830056149693411207 5647331745084224540116811)
              ·
                refine ⟨8470997617626336810175217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647331745084224540116811 8470997617626336810175217)
                ·
                  refine ⟨6353248213219752607631413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470997617626336810175217 6353248213219752607631413)
                  ·
                    refine ⟨595617019989351806965445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6353248213219752607631413 595617019989351806965445)
                    ·
                      rfl

theorem cell22_1739940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1739940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1739940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1739940 prefixEnd_1739940 := by exact prefixLift 1739940
  have htrace : WordTrace (prefixWord ++ tailWord_1739940) baseStart_1739940 baseEnd_1739940 := by
    simpa [prefixWord, tailWord_1739940, baseEnd_1739940] using wordTrace_append hprefix tailTrace_1739940
  have hstable : (prefixWord ++ tailWord_1739940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739940).length < 2 ^ (prefixWord ++ tailWord_1739940).sum := by decide
  have hdescent : baseEnd_1739940 < baseStart_1739940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740015 : List Nat := [1, 1, 2, 1, 7, 1, 1, 8]
def baseStart_1740015 : Nat := 118140960795 + 1740015 * 2 ^ 59
def prefixEnd_1740015 : Nat := 4983230072969 + 3 ^ 40 * 1740015 * 2
def baseEnd_1740015 : Nat := 66182521558008512371135

theorem tailTrace_1740015 : CollatzResearch.WordTrace tailWord_1740015 prefixEnd_1740015 66182521558008512371135 := by
  unfold tailWord_1740015
  simp only [CollatzResearch.WordTrace]
  refine ⟨63463560791230300748125499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42309040527486867165416999 63463560791230300748125499)
  ·
    refine ⟨95195341186845451122188249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63463560791230300748125499 95195341186845451122188249)
    ·
      refine ⟨71396505890134088341641187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95195341186845451122188249 71396505890134088341641187)
      ·
        refine ⟨107094758835201132512461781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71396505890134088341641187 107094758835201132512461781)
        ·
          refine ⟨2510033410200026543260823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107094758835201132512461781 2510033410200026543260823)
          ·
            refine ⟨3765050115300039814891235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510033410200026543260823 3765050115300039814891235)
            ·
              refine ⟨5647575172950059722336853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765050115300039814891235 5647575172950059722336853)
              ·
                refine ⟨66182521558008512371135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5647575172950059722336853 66182521558008512371135)
                ·
                  rfl

theorem cell22_1740015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 8].length) (baseStart_1740015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740015 prefixEnd_1740015 := by exact prefixLift 1740015
  have htrace : WordTrace (prefixWord ++ tailWord_1740015) baseStart_1740015 baseEnd_1740015 := by
    simpa [prefixWord, tailWord_1740015, baseEnd_1740015] using wordTrace_append hprefix tailTrace_1740015
  have hstable : (prefixWord ++ tailWord_1740015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740015).length < 2 ^ (prefixWord ++ tailWord_1740015).sum := by decide
  have hdescent : baseEnd_1740015 < baseStart_1740015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740034 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1740034 : Nat := 118140960795 + 1740034 * 2 ^ 59
def prefixEnd_1740034 : Nat := 4983230072969 + 3 ^ 40 * 1740034 * 2
def baseEnd_1740034 : Nat := 595649198110366895115157

theorem tailTrace_1740034 : CollatzResearch.WordTrace tailWord_1740034 prefixEnd_1740034 595649198110366895115157 := by
  unfold tailWord_1740034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866063444540366748266789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42309502518774311328711437 15866063444540366748266789)
  ·
    refine ⟨2974886895851318765300023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15866063444540366748266789 2974886895851318765300023)
    ·
      refine ⟨4462330343776978147950035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974886895851318765300023 4462330343776978147950035)
      ·
        refine ⟨6693495515665467221925053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462330343776978147950035 6693495515665467221925053)
        ·
          refine ⟨2510060818374550208221895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6693495515665467221925053 2510060818374550208221895)
          ·
            refine ⟨3765091227561825312332843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510060818374550208221895 3765091227561825312332843)
            ·
              refine ⟨5647636841342737968499265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765091227561825312332843 5647636841342737968499265)
              ·
                refine ⟨4235727631007053476374449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647636841342737968499265 4235727631007053476374449)
                ·
                  refine ⟨3176795723255290107280837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235727631007053476374449 3176795723255290107280837)
                  ·
                    refine ⟨595649198110366895115157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176795723255290107280837 595649198110366895115157)
                    ·
                      rfl

theorem cell22_1740034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1740034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740034 prefixEnd_1740034 := by exact prefixLift 1740034
  have htrace : WordTrace (prefixWord ++ tailWord_1740034) baseStart_1740034 baseEnd_1740034 := by
    simpa [prefixWord, tailWord_1740034, baseEnd_1740034] using wordTrace_append hprefix tailTrace_1740034
  have hstable : (prefixWord ++ tailWord_1740034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740034).length < 2 ^ (prefixWord ++ tailWord_1740034).sum := by decide
  have hdescent : baseEnd_1740034 < baseStart_1740034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740141 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_1740141 : Nat := 118140960795 + 1740141 * 2 ^ 59
def prefixEnd_1740141 : Nat := 4983230072969 + 3 ^ 40 * 1740141 * 2
def baseEnd_1740141 : Nat := 595685826397054282689829

theorem tailTrace_1740141 : CollatzResearch.WordTrace tailWord_1740141 prefixEnd_1740141 595685826397054282689829 := by
  unfold tailWord_1740141
  simp only [CollatzResearch.WordTrace]
  refine ⟨63468156388773824267212277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42312104259182549511474851 63468156388773824267212277)
  ·
    refine ⟨5950139661447546025051151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63468156388773824267212277 5950139661447546025051151)
    ·
      refine ⟨8925209492171319037576727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950139661447546025051151 8925209492171319037576727)
      ·
        refine ⟨13387814238256978556365091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925209492171319037576727 13387814238256978556365091)
        ·
          refine ⟨20081721357385467834547637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13387814238256978556365091 20081721357385467834547637)
          ·
            refine ⟨1882661377254887609488841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20081721357385467834547637 1882661377254887609488841)
            ·
              refine ⟨1411996032941165707116631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882661377254887609488841 1411996032941165707116631)
              ·
                refine ⟨2117994049411748560674947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411996032941165707116631 2117994049411748560674947)
                ·
                  refine ⟨3176991074117622841012421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117994049411748560674947 3176991074117622841012421)
                  ·
                    refine ⟨595685826397054282689829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3176991074117622841012421 595685826397054282689829)
                    ·
                      rfl

theorem cell22_1740141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_1740141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740141 prefixEnd_1740141 := by exact prefixLift 1740141
  have htrace : WordTrace (prefixWord ++ tailWord_1740141) baseStart_1740141 baseEnd_1740141 := by
    simpa [prefixWord, tailWord_1740141, baseEnd_1740141] using wordTrace_append hprefix tailTrace_1740141
  have hstable : (prefixWord ++ tailWord_1740141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740141).length < 2 ^ (prefixWord ++ tailWord_1740141).sum := by decide
  have hdescent : baseEnd_1740141 < baseStart_1740141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740190 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1740190 : Nat := 118140960795 + 1740190 * 2 ^ 59
def prefixEnd_1740190 : Nat := 4983230072969 + 3 ^ 40 * 1740190 * 2
def baseEnd_1740190 : Nat := 198567533366144829404893

theorem tailTrace_1740190 : CollatzResearch.WordTrace tailWord_1740190 prefixEnd_1740190 198567533366144829404893 := by
  unfold tailWord_1740190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933742945699538204468253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42313295710397537090497349 7933742945699538204468253)
  ·
    refine ⟨2975153604637326826675595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7933742945699538204468253 2975153604637326826675595)
    ·
      refine ⟨4462730406955990240013393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975153604637326826675595 4462730406955990240013393)
      ·
        refine ⟨3347047805216992680010045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462730406955990240013393 3347047805216992680010045)
        ·
          refine ⟨1255142926956372255003767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3347047805216992680010045 1255142926956372255003767)
          ·
            refine ⟨1882714390434558382505651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255142926956372255003767 1882714390434558382505651)
            ·
              refine ⟨2824071585651837573758477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882714390434558382505651 2824071585651837573758477)
              ·
                refine ⟨1059026844619439090159429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824071585651837573758477 1059026844619439090159429)
                ·
                  refine ⟨198567533366144829404893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059026844619439090159429 198567533366144829404893)
                  ·
                    rfl

theorem cell22_1740190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1740190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740190 prefixEnd_1740190 := by exact prefixLift 1740190
  have htrace : WordTrace (prefixWord ++ tailWord_1740190) baseStart_1740190 baseEnd_1740190 := by
    simpa [prefixWord, tailWord_1740190, baseEnd_1740190] using wordTrace_append hprefix tailTrace_1740190
  have hstable : (prefixWord ++ tailWord_1740190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740190).length < 2 ^ (prefixWord ++ tailWord_1740190).sum := by decide
  have hdescent : baseEnd_1740190 < baseStart_1740190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740195 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 9]
def baseStart_1740195 : Nat := 118140960795 + 1740195 * 2 ^ 59
def prefixEnd_1740195 : Nat := 4983230072969 + 3 ^ 40 * 1740195 * 2
def baseEnd_1740195 : Nat := 198568103900205380613221

theorem tailTrace_1740195 : CollatzResearch.WordTrace tailWord_1740195 prefixEnd_1740195 198568103900205380613221 := by
  unfold tailWord_1740195
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470125930578191489678039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42313417287052127659785359 63470125930578191489678039)
  ·
    refine ⟨95205188895867287234517059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63470125930578191489678039 95205188895867287234517059)
    ·
      refine ⟨142807783343800930851775589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95205188895867287234517059 142807783343800930851775589)
      ·
        refine ⟨26776459376962674534707923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142807783343800930851775589 26776459376962674534707923)
        ·
          refine ⟨40164689065444011802061885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776459376962674534707923 40164689065444011802061885)
          ·
            refine ⟨15061758399541504425773207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40164689065444011802061885 15061758399541504425773207)
            ·
              refine ⟨22592637599312256638659811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15061758399541504425773207 22592637599312256638659811)
              ·
                refine ⟨33888956398968384957989717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22592637599312256638659811 33888956398968384957989717)
                ·
                  refine ⟨198568103900205380613221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33888956398968384957989717 198568103900205380613221)
                  ·
                    rfl

theorem cell22_1740195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_1740195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740195 prefixEnd_1740195 := by exact prefixLift 1740195
  have htrace : WordTrace (prefixWord ++ tailWord_1740195) baseStart_1740195 baseEnd_1740195 := by
    simpa [prefixWord, tailWord_1740195, baseEnd_1740195] using wordTrace_append hprefix tailTrace_1740195
  have hstable : (prefixWord ++ tailWord_1740195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740195).length < 2 ^ (prefixWord ++ tailWord_1740195).sum := by decide
  have hdescent : baseEnd_1740195 < baseStart_1740195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740323 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 2, 3]
def baseStart_1740323 : Nat := 118140960795 + 1740323 * 2 ^ 59
def prefixEnd_1740323 : Nat := 4983230072969 + 3 ^ 40 * 1740323 * 2
def baseEnd_1740323 : Nat := 595748128716466474639271

theorem tailTrace_1740323 : CollatzResearch.WordTrace tailWord_1740323 prefixEnd_1740323 595748128716466474639271 := by
  unfold tailWord_1740323
  simp only [CollatzResearch.WordTrace]
  refine ⟨63474794474114469350337623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42316529649409646233558415 63474794474114469350337623)
  ·
    refine ⟨95212191711171704025506435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63474794474114469350337623 95212191711171704025506435)
    ·
      refine ⟨142818287566757556038259653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95212191711171704025506435 142818287566757556038259653)
      ·
        refine ⟨26778428918767041757173685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142818287566757556038259653 26778428918767041757173685)
        ·
          refine ⟨2510477711134410164735033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26778428918767041757173685 2510477711134410164735033)
          ·
            refine ⟨1882858283350807623551275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510477711134410164735033 1882858283350807623551275)
            ·
              refine ⟨2824287425026211435326913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882858283350807623551275 2824287425026211435326913)
              ·
                refine ⟨2118215568769658576495185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824287425026211435326913 2118215568769658576495185)
                ·
                  refine ⟨1588661676577243932371389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118215568769658576495185 1588661676577243932371389)
                  ·
                    refine ⟨595748128716466474639271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588661676577243932371389 595748128716466474639271)
                    ·
                      rfl

theorem cell22_1740323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].length) (baseStart_1740323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740323 prefixEnd_1740323 := by exact prefixLift 1740323
  have htrace : WordTrace (prefixWord ++ tailWord_1740323) baseStart_1740323 baseEnd_1740323 := by
    simpa [prefixWord, tailWord_1740323, baseEnd_1740323] using wordTrace_append hprefix tailTrace_1740323
  have hstable : (prefixWord ++ tailWord_1740323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740323).length < 2 ^ (prefixWord ++ tailWord_1740323).sum := by decide
  have hdescent : baseEnd_1740323 < baseStart_1740323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740471 : List Nat := [1, 1, 3, 1, 5, 2, 3, 6]
def baseStart_1740471 : Nat := 118140960795 + 1740471 * 2 ^ 59
def prefixEnd_1740471 : Nat := 4983230072969 + 3 ^ 40 * 1740471 * 2
def baseEnd_1740471 : Nat := 66199865793449269104313

theorem tailTrace_1740471 : CollatzResearch.WordTrace tailWord_1740471 prefixEnd_1740471 66199865793449269104313 := by
  unfold tailWord_1740471
  simp only [CollatzResearch.WordTrace]
  refine ⟨63480192477578290626725267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42320128318385527084483511 63480192477578290626725267)
  ·
    refine ⟨95220288716367435940087901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63480192477578290626725267 95220288716367435940087901)
    ·
      refine ⟨35707608268637788477532963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95220288716367435940087901 35707608268637788477532963)
      ·
        refine ⟨53561412402956682716299445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35707608268637788477532963 53561412402956682716299445)
        ·
          refine ⟨5021382412777189004653073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53561412402956682716299445 5021382412777189004653073)
          ·
            refine ⟨3766036809582891753489805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021382412777189004653073 3766036809582891753489805)
            ·
              refine ⟨1412263803593584407558677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3766036809582891753489805 1412263803593584407558677)
              ·
                refine ⟨66199865793449269104313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1412263803593584407558677 66199865793449269104313)
                ·
                  rfl

theorem cell22_1740471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 6].length) (baseStart_1740471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740471 prefixEnd_1740471 := by exact prefixLift 1740471
  have htrace : WordTrace (prefixWord ++ tailWord_1740471) baseStart_1740471 baseEnd_1740471 := by
    simpa [prefixWord, tailWord_1740471, baseEnd_1740471] using wordTrace_append hprefix tailTrace_1740471
  have hstable : (prefixWord ++ tailWord_1740471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740471).length < 2 ^ (prefixWord ++ tailWord_1740471).sum := by decide
  have hdescent : baseEnd_1740471 < baseStart_1740471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740492 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_1740492 : Nat := 118140960795 + 1740492 * 2 ^ 59
def prefixEnd_1740492 : Nat := 4983230072969 + 3 ^ 40 * 1740492 * 2
def baseEnd_1740492 : Nat := 595805980870206367163753

theorem tailTrace_1740492 : CollatzResearch.WordTrace tailWord_1740492 prefixEnd_1740492 595805980870206367163753 := by
  unfold tailWord_1740492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31740479205251105606619865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42320638940334807475493153 31740479205251105606619865)
  ·
    refine ⟨23805359403938329204964899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31740479205251105606619865 23805359403938329204964899)
    ·
      refine ⟨35708039105907493807447349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23805359403938329204964899 35708039105907493807447349)
      ·
        refine ⟨3347628666178827544448189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35708039105907493807447349 3347628666178827544448189)
        ·
          refine ⟨1255360749817060329168071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3347628666178827544448189 1255360749817060329168071)
          ·
            refine ⟨1883041124725590493752107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255360749817060329168071 1883041124725590493752107)
            ·
              refine ⟨2824561687088385740628161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883041124725590493752107 2824561687088385740628161)
              ·
                refine ⟨2118421265316289305471121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824561687088385740628161 2118421265316289305471121)
                ·
                  refine ⟨1588815948987216979103341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118421265316289305471121 1588815948987216979103341)
                  ·
                    refine ⟨595805980870206367163753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588815948987216979103341 595805980870206367163753)
                    ·
                      rfl

theorem cell22_1740492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_1740492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740492 prefixEnd_1740492 := by exact prefixLift 1740492
  have htrace : WordTrace (prefixWord ++ tailWord_1740492) baseStart_1740492 baseEnd_1740492 := by
    simpa [prefixWord, tailWord_1740492, baseEnd_1740492] using wordTrace_append hprefix tailTrace_1740492
  have hstable : (prefixWord ++ tailWord_1740492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740492).length < 2 ^ (prefixWord ++ tailWord_1740492).sum := by decide
  have hdescent : baseEnd_1740492 < baseStart_1740492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740503 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 1, 3]
def baseStart_1740503 : Nat := 118140960795 + 1740503 * 2 ^ 59
def prefixEnd_1740503 : Nat := 4983230072969 + 3 ^ 40 * 1740503 * 2
def baseEnd_1740503 : Nat := 595809746395006005138719

theorem tailTrace_1740503 : CollatzResearch.WordTrace tailWord_1740503 prefixEnd_1740503 595809746395006005138719 := by
  unfold tailWord_1740503
  simp only [CollatzResearch.WordTrace]
  refine ⟨63481359613462360091890163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42320906408974906727926775 63481359613462360091890163)
  ·
    refine ⟨95222039420193540137835245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63481359613462360091890163 95222039420193540137835245)
    ·
      refine ⟨35708264782572577551688217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95222039420193540137835245 35708264782572577551688217)
      ·
        refine ⟨26781198586929433163766163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35708264782572577551688217 26781198586929433163766163)
        ·
          refine ⟨40171797880394149745649245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26781198586929433163766163 40171797880394149745649245)
          ·
            refine ⟨15064424205147806154618467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40171797880394149745649245 15064424205147806154618467)
            ·
              refine ⟨22596636307721709231927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15064424205147806154618467 22596636307721709231927701)
              ·
                refine ⟨1059217326924455120246611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22596636307721709231927701 1059217326924455120246611)
                ·
                  refine ⟨1588825990386682680369917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059217326924455120246611 1588825990386682680369917)
                  ·
                    refine ⟨595809746395006005138719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1588825990386682680369917 595809746395006005138719)
                    ·
                      rfl

theorem cell22_1740503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_1740503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740503 prefixEnd_1740503 := by exact prefixLift 1740503
  have htrace : WordTrace (prefixWord ++ tailWord_1740503) baseStart_1740503 baseEnd_1740503 := by
    simpa [prefixWord, tailWord_1740503, baseEnd_1740503] using wordTrace_append hprefix tailTrace_1740503
  have hstable : (prefixWord ++ tailWord_1740503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740503).length < 2 ^ (prefixWord ++ tailWord_1740503).sum := by decide
  have hdescent : baseEnd_1740503 < baseStart_1740503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740559 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1740559 : Nat := 118140960795 + 1740559 * 2 ^ 59
def prefixEnd_1740559 : Nat := 4983230072969 + 3 ^ 40 * 1740559 * 2
def baseEnd_1740559 : Nat := 595828916339440525738547

theorem tailTrace_1740559 : CollatzResearch.WordTrace tailWord_1740559 prefixEnd_1740559 595828916339440525738547 := by
  unfold tailWord_1740559
  simp only [CollatzResearch.WordTrace]
  refine ⟨63483402101259481655928731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42322268067506321103952487 63483402101259481655928731)
  ·
    refine ⟨95225103151889222483893097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63483402101259481655928731 95225103151889222483893097)
    ·
      refine ⟨71418827363916916862919823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95225103151889222483893097 71418827363916916862919823)
      ·
        refine ⟨107128241045875375294379735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71418827363916916862919823 107128241045875375294379735)
        ·
          refine ⟨160692361568813062941569603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107128241045875375294379735 160692361568813062941569603)
          ·
            refine ⟨241038542353219594412354405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160692361568813062941569603 241038542353219594412354405)
            ·
              refine ⟨45194726691228673952316451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241038542353219594412354405 45194726691228673952316451)
              ·
                refine ⟨67792090036843010928474677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45194726691228673952316451 67792090036843010928474677)
                ·
                  refine ⟨6355508440954032274544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67792090036843010928474677 6355508440954032274544501)
                  ·
                    refine ⟨595828916339440525738547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6355508440954032274544501 595828916339440525738547)
                    ·
                      rfl

theorem cell22_1740559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1740559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740559 prefixEnd_1740559 := by exact prefixLift 1740559
  have htrace : WordTrace (prefixWord ++ tailWord_1740559) baseStart_1740559 baseEnd_1740559 := by
    simpa [prefixWord, tailWord_1740559, baseEnd_1740559] using wordTrace_append hprefix tailTrace_1740559
  have hstable : (prefixWord ++ tailWord_1740559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740559).length < 2 ^ (prefixWord ++ tailWord_1740559).sum := by decide
  have hdescent : baseEnd_1740559 < baseStart_1740559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740576 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_1740576 : Nat := 118140960795 + 1740576 * 2 ^ 59
def prefixEnd_1740576 : Nat := 4983230072969 + 3 ^ 40 * 1740576 * 2
def baseEnd_1740576 : Nat := 595834735786858148063495

theorem tailTrace_1740576 : CollatzResearch.WordTrace tailWord_1740576 prefixEnd_1740576 595834735786858148063495 := by
  unfold tailWord_1740576
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742011071098946779648791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42322681428131929039531721 31742011071098946779648791)
  ·
    refine ⟨47613016606648420169473187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31742011071098946779648791 47613016606648420169473187)
    ·
      refine ⟨71419524909972630254209781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47613016606648420169473187 71419524909972630254209781)
      ·
        refine ⟨6695580460309934086332167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71419524909972630254209781 6695580460309934086332167)
        ·
          refine ⟨10043370690464901129498251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695580460309934086332167 10043370690464901129498251)
          ·
            refine ⟨15065056035697351694247377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043370690464901129498251 15065056035697351694247377)
            ·
              refine ⟨11298792026773013770685533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15065056035697351694247377 11298792026773013770685533)
              ·
                refine ⟨4237047010039880164007075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11298792026773013770685533 4237047010039880164007075)
                ·
                  refine ⟨6355570515059820246010613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237047010039880164007075 6355570515059820246010613)
                  ·
                    refine ⟨595834735786858148063495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6355570515059820246010613 595834735786858148063495)
                    ·
                      rfl

theorem cell22_1740576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_1740576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740576 prefixEnd_1740576 := by exact prefixLift 1740576
  have htrace : WordTrace (prefixWord ++ tailWord_1740576) baseStart_1740576 baseEnd_1740576 := by
    simpa [prefixWord, tailWord_1740576, baseEnd_1740576] using wordTrace_append hprefix tailTrace_1740576
  have hstable : (prefixWord ++ tailWord_1740576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740576).length < 2 ^ (prefixWord ++ tailWord_1740576).sum := by decide
  have hdescent : baseEnd_1740576 < baseStart_1740576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740580 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1740580 : Nat := 118140960795 + 1740580 * 2 ^ 59
def prefixEnd_1740580 : Nat := 4983230072969 + 3 ^ 40 * 1740580 * 2
def baseEnd_1740580 : Nat := 595836105068603470963483

theorem tailTrace_1740580 : CollatzResearch.WordTrace tailWord_1740580 prefixEnd_1740580 595836105068603470963483 := by
  unfold tailWord_1740580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742084017091701121221597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42322778689455601494962129 31742084017091701121221597)
  ·
    refine ⟨11903281506409387920458099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31742084017091701121221597 11903281506409387920458099)
    ·
      refine ⟨17854922259614081880687149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11903281506409387920458099 17854922259614081880687149)
      ·
        refine ⟨6695595847355280705257681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17854922259614081880687149 6695595847355280705257681)
        ·
          refine ⟨5021696885516460528943261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6695595847355280705257681 5021696885516460528943261)
          ·
            refine ⟨1883136332068672698353723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5021696885516460528943261 1883136332068672698353723)
            ·
              refine ⟨2824704498103009047530585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883136332068672698353723 2824704498103009047530585)
              ·
                refine ⟨2118528373577256785647939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824704498103009047530585 2118528373577256785647939)
                ·
                  refine ⟨3177792560365885178471909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118528373577256785647939 3177792560365885178471909)
                  ·
                    refine ⟨595836105068603470963483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3177792560365885178471909 595836105068603470963483)
                    ·
                      rfl

theorem cell22_1740580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1740580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740580 prefixEnd_1740580 := by exact prefixLift 1740580
  have htrace : WordTrace (prefixWord ++ tailWord_1740580) baseStart_1740580 baseEnd_1740580 := by
    simpa [prefixWord, tailWord_1740580, baseEnd_1740580] using wordTrace_append hprefix tailTrace_1740580
  have hstable : (prefixWord ++ tailWord_1740580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740580).length < 2 ^ (prefixWord ++ tailWord_1740580).sum := by decide
  have hdescent : baseEnd_1740580 < baseStart_1740580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740606 : List Nat := [4, 2, 1, 2, 2, 11]
def baseStart_1740606 : Nat := 118140960795 + 1740606 * 2 ^ 59
def prefixEnd_1740606 : Nat := 4983230072969 + 3 ^ 40 * 1740606 * 2
def baseEnd_1740606 : Nat := 7356111177777136664363

theorem tailTrace_1740606 : CollatzResearch.WordTrace tailWord_1740606 prefixEnd_1740606 7356111177777136664363 := by
  unfold tailWord_1740606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935639541511151085361209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42323410888059472455259781 7935639541511151085361209)
  ·
    refine ⟨5951729656133363314020907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7935639541511151085361209 5951729656133363314020907)
    ·
      refine ⟨8927594484200044971031361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951729656133363314020907 8927594484200044971031361)
      ·
        refine ⟨6695695863150033728273521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8927594484200044971031361 6695695863150033728273521)
        ·
          refine ⟨5021771897362525296205141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6695695863150033728273521 5021771897362525296205141)
          ·
            refine ⟨7356111177777136664363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5021771897362525296205141 7356111177777136664363)
            ·
              rfl

theorem cell22_1740606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 11].length) (baseStart_1740606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740606 prefixEnd_1740606 := by exact prefixLift 1740606
  have htrace : WordTrace (prefixWord ++ tailWord_1740606) baseStart_1740606 baseEnd_1740606 := by
    simpa [prefixWord, tailWord_1740606, baseEnd_1740606] using wordTrace_append hprefix tailTrace_1740606
  have hstable : (prefixWord ++ tailWord_1740606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740606).length < 2 ^ (prefixWord ++ tailWord_1740606).sum := by decide
  have hdescent : baseEnd_1740606 < baseStart_1740606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740666 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1740666 : Nat := 118140960795 + 1740666 * 2 ^ 59
def prefixEnd_1740666 : Nat := 4983230072969 + 3 ^ 40 * 1740666 * 2
def baseEnd_1740666 : Nat := 595865544626127913313219

theorem tailTrace_1740666 : CollatzResearch.WordTrace tailWord_1740666 prefixEnd_1740666 595865544626127913313219 := by
  unfold tailWord_1740666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871826177967959732518463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42324869807914559286715901 15871826177967959732518463)
  ·
    refine ⟨23807739266951939598777695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871826177967959732518463 23807739266951939598777695)
    ·
      refine ⟨35711608900427909398166543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23807739266951939598777695 35711608900427909398166543)
      ·
        refine ⟨53567413350641864097249815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35711608900427909398166543 53567413350641864097249815)
        ·
          refine ⟨80351120025962796145874723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53567413350641864097249815 80351120025962796145874723)
          ·
            refine ⟨120526680038944194218812085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80351120025962796145874723 120526680038944194218812085)
            ·
              refine ⟨11299376253651018208013633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120526680038944194218812085 11299376253651018208013633)
              ·
                refine ⟨8474532190238263656010225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11299376253651018208013633 8474532190238263656010225)
                ·
                  refine ⟨6355899142678697742007669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474532190238263656010225 6355899142678697742007669)
                  ·
                    refine ⟨595865544626127913313219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6355899142678697742007669 595865544626127913313219)
                    ·
                      rfl

theorem cell22_1740666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1740666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740666 prefixEnd_1740666 := by exact prefixLift 1740666
  have htrace : WordTrace (prefixWord ++ tailWord_1740666) baseStart_1740666 baseEnd_1740666 := by
    simpa [prefixWord, tailWord_1740666, baseEnd_1740666] using wordTrace_append hprefix tailTrace_1740666
  have hstable : (prefixWord ++ tailWord_1740666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740666).length < 2 ^ (prefixWord ++ tailWord_1740666).sum := by decide
  have hdescent : baseEnd_1740666 < baseStart_1740666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740706 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1740706 : Nat := 118140960795 + 1740706 * 2 ^ 59
def prefixEnd_1740706 : Nat := 4983230072969 + 3 ^ 40 * 1740706 * 2
def baseEnd_1740706 : Nat := 595879237443581142313097

theorem tailTrace_1740706 : CollatzResearch.WordTrace tailWord_1740706 prefixEnd_1740706 595879237443581142313097 := by
  unfold tailWord_1740706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872190907931731440382493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42325842421151283841019981 15872190907931731440382493)
  ·
    refine ⟨5952071590474399290143435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15872190907931731440382493 5952071590474399290143435)
    ·
      refine ⟨8928107385711598935215153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952071590474399290143435 8928107385711598935215153)
      ·
        refine ⟨6696080539283699201411365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8928107385711598935215153 6696080539283699201411365)
        ·
          refine ⟨1255515101115693600264631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6696080539283699201411365 1255515101115693600264631)
          ·
            refine ⟨1883272651673540400396947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255515101115693600264631 1883272651673540400396947)
            ·
              refine ⟨2824908977510310600595421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883272651673540400396947 2824908977510310600595421)
              ·
                refine ⟨1059340866566366475223283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824908977510310600595421 1059340866566366475223283)
                ·
                  refine ⟨1589011299849549712834925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059340866566366475223283 1589011299849549712834925)
                  ·
                    refine ⟨595879237443581142313097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589011299849549712834925 595879237443581142313097)
                    ·
                      rfl

theorem cell22_1740706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1740706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740706 prefixEnd_1740706 := by exact prefixLift 1740706
  have htrace : WordTrace (prefixWord ++ tailWord_1740706) baseStart_1740706 baseEnd_1740706 := by
    simpa [prefixWord, tailWord_1740706, baseEnd_1740706] using wordTrace_append hprefix tailTrace_1740706
  have hstable : (prefixWord ++ tailWord_1740706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740706).length < 2 ^ (prefixWord ++ tailWord_1740706).sum := by decide
  have hdescent : baseEnd_1740706 < baseStart_1740706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740713 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 4]
def baseStart_1740713 : Nat := 118140960795 + 1740713 * 2 ^ 59
def prefixEnd_1740713 : Nat := 4983230072969 + 3 ^ 40 * 1740713 * 2
def baseEnd_1740713 : Nat := 198627211228878485796025

theorem tailTrace_1740713 : CollatzResearch.WordTrace tailWord_1740713 prefixEnd_1740713 198627211228878485796025 := by
  unfold tailWord_1740713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63489018942701565957034793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42326012628467710638023195 63489018942701565957034793)
  ·
    refine ⟨47616764207026174467776095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63489018942701565957034793 47616764207026174467776095)
    ·
      refine ⟨71425146310539261701664143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47616764207026174467776095 71425146310539261701664143)
      ·
        refine ⟨107137719465808892552496215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71425146310539261701664143 107137719465808892552496215)
        ·
          refine ⟨160706579198713338828744323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107137719465808892552496215 160706579198713338828744323)
          ·
            refine ⟨241059868798070008243116485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160706579198713338828744323 241059868798070008243116485)
            ·
              refine ⟨45198725399638126545584341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241059868798070008243116485 45198725399638126545584341)
              ·
                refine ⟨1059345126554018590912133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45198725399638126545584341 1059345126554018590912133)
                ·
                  refine ⟨198627211228878485796025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059345126554018590912133 198627211228878485796025)
                  ·
                    rfl

theorem cell22_1740713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_1740713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740713 prefixEnd_1740713 := by exact prefixLift 1740713
  have htrace : WordTrace (prefixWord ++ tailWord_1740713) baseStart_1740713 baseEnd_1740713 := by
    simpa [prefixWord, tailWord_1740713, baseEnd_1740713] using wordTrace_append hprefix tailTrace_1740713
  have hstable : (prefixWord ++ tailWord_1740713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740713).length < 2 ^ (prefixWord ++ tailWord_1740713).sum := by decide
  have hdescent : baseEnd_1740713 < baseStart_1740713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740728 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_1740728 : Nat := 118140960795 + 1740728 * 2 ^ 59
def prefixEnd_1740728 : Nat := 4983230072969 + 3 ^ 40 * 1740728 * 2
def baseEnd_1740728 : Nat := 595886768493180418263029

theorem tailTrace_1740728 : CollatzResearch.WordTrace tailWord_1740728 prefixEnd_1740728 595886768493180418263029 := by
  unfold tailWord_1740728
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744783018823611759415419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42326377358431482345887225 31744783018823611759415419)
  ·
    refine ⟨47617174528235417639123129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31744783018823611759415419 47617174528235417639123129)
    ·
      refine ⟨35712880896176563229342347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47617174528235417639123129 35712880896176563229342347)
      ·
        refine ⟨53569321344264844844013521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35712880896176563229342347 53569321344264844844013521)
        ·
          refine ⟨40176991008198633633010141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53569321344264844844013521 40176991008198633633010141)
          ·
            refine ⟨15066371628074487612378803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40176991008198633633010141 15066371628074487612378803)
            ·
              refine ⟨22599557442111731418568205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15066371628074487612378803 22599557442111731418568205)
              ·
                refine ⟨8474834040791899281963077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22599557442111731418568205 8474834040791899281963077)
                ·
                  refine ⟨1589031382648481115368077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8474834040791899281963077 1589031382648481115368077)
                  ·
                    refine ⟨595886768493180418263029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589031382648481115368077 595886768493180418263029)
                    ·
                      rfl

theorem cell22_1740728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_1740728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740728 prefixEnd_1740728 := by exact prefixLift 1740728
  have htrace : WordTrace (prefixWord ++ tailWord_1740728) baseStart_1740728 baseEnd_1740728 := by
    simpa [prefixWord, tailWord_1740728, baseEnd_1740728] using wordTrace_append hprefix tailTrace_1740728
  have hstable : (prefixWord ++ tailWord_1740728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740728).length < 2 ^ (prefixWord ++ tailWord_1740728).sum := by decide
  have hdescent : baseEnd_1740728 < baseStart_1740728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740781 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1740781 : Nat := 118140960795 + 1740781 * 2 ^ 59
def prefixEnd_1740781 : Nat := 4983230072969 + 3 ^ 40 * 1740781 * 2
def baseEnd_1740781 : Nat := 198634970492101982229289

theorem tailTrace_1740781 : CollatzResearch.WordTrace tailWord_1740781 prefixEnd_1740781 198634970492101982229289 := by
  unfold tailWord_1740781
  simp only [CollatzResearch.WordTrace]
  refine ⟨63491499106455213570510197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42327666070970142380340131 63491499106455213570510197)
  ·
    refine ⟨5952328041230176272235331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63491499106455213570510197 5952328041230176272235331)
    ·
      refine ⟨8928492061845264408352997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952328041230176272235331 8928492061845264408352997)
      ·
        refine ⟨1674092261595987076566187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8928492061845264408352997 1674092261595987076566187)
        ·
          refine ⟨2511138392393980614849281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674092261595987076566187 2511138392393980614849281)
          ·
            refine ⟨1883353794295485461136961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511138392393980614849281 1883353794295485461136961)
            ·
              refine ⟨1412515345721614095852721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883353794295485461136961 1412515345721614095852721)
              ·
                refine ⟨1059386509291210571889541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412515345721614095852721 1059386509291210571889541)
                ·
                  refine ⟨198634970492101982229289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059386509291210571889541 198634970492101982229289)
                  ·
                    rfl

theorem cell22_1740781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1740781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740781 prefixEnd_1740781 := by exact prefixLift 1740781
  have htrace : WordTrace (prefixWord ++ tailWord_1740781) baseStart_1740781 baseEnd_1740781 := by
    simpa [prefixWord, tailWord_1740781, baseEnd_1740781] using wordTrace_append hprefix tailTrace_1740781
  have hstable : (prefixWord ++ tailWord_1740781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740781).length < 2 ^ (prefixWord ++ tailWord_1740781).sum := by decide
  have hdescent : baseEnd_1740781 < baseStart_1740781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740848 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_1740848 : Nat := 118140960795 + 1740848 * 2 ^ 59
def prefixEnd_1740848 : Nat := 4983230072969 + 3 ^ 40 * 1740848 * 2
def baseEnd_1740848 : Nat := 198642615648513368420887

theorem tailTrace_1740848 : CollatzResearch.WordTrace tailWord_1740848 prefixEnd_1740848 198642615648513368420887 := by
  unfold tailWord_1740848
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746971398606242006599599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42329295198141656008799465 31746971398606242006599599)
  ·
    refine ⟨47620457097909363009899399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31746971398606242006599599 47620457097909363009899399)
    ·
      refine ⟨71430685646864044514849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47620457097909363009899399 71430685646864044514849099)
      ·
        refine ⟨107146028470296066772273649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71430685646864044514849099 107146028470296066772273649)
        ·
          refine ⟨80359521352722050079205237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107146028470296066772273649 80359521352722050079205237)
          ·
            refine ⟨7533705126817692194925491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80359521352722050079205237 7533705126817692194925491)
            ·
              refine ⟨11300557690226538292388237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533705126817692194925491 11300557690226538292388237)
              ·
                refine ⟨4237709133834951859645589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11300557690226538292388237 4237709133834951859645589)
                ·
                  refine ⟨198642615648513368420887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4237709133834951859645589 198642615648513368420887)
                  ·
                    rfl

theorem cell22_1740848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_1740848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740848 prefixEnd_1740848 := by exact prefixLift 1740848
  have htrace : WordTrace (prefixWord ++ tailWord_1740848) baseStart_1740848 baseEnd_1740848 := by
    simpa [prefixWord, tailWord_1740848, baseEnd_1740848] using wordTrace_append hprefix tailTrace_1740848
  have hstable : (prefixWord ++ tailWord_1740848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740848).length < 2 ^ (prefixWord ++ tailWord_1740848).sum := by decide
  have hdescent : baseEnd_1740848 < baseStart_1740848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740865 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 6]
def baseStart_1740865 : Nat := 118140960795 + 1740865 * 2 ^ 59
def prefixEnd_1740865 : Nat := 4983230072969 + 3 ^ 40 * 1740865 * 2
def baseEnd_1740865 : Nat := 198644555464319242529203

theorem tailTrace_1740865 : CollatzResearch.WordTrace tailWord_1740865 prefixEnd_1740865 198644555464319242529203 := by
  unfold tailWord_1740865
  simp only [CollatzResearch.WordTrace]
  refine ⟨63494562838150895916568049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42329708558767263944378699 63494562838150895916568049)
  ·
    refine ⟨47620922128613171937426037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63494562838150895916568049 47620922128613171937426037)
    ·
      refine ⟨4464461449557484869133691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47620922128613171937426037 4464461449557484869133691)
      ·
        refine ⟨6696692174336227303700537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464461449557484869133691 6696692174336227303700537)
        ·
          refine ⟨5022519130752170477775403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6696692174336227303700537 5022519130752170477775403)
          ·
            refine ⟨7533778696128255716663105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022519130752170477775403 7533778696128255716663105)
            ·
              refine ⟨5650334022096191787497329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7533778696128255716663105 5650334022096191787497329)
              ·
                refine ⟨4237750516572143840622997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5650334022096191787497329 4237750516572143840622997)
                ·
                  refine ⟨198644555464319242529203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4237750516572143840622997 198644555464319242529203)
                  ·
                    rfl

theorem cell22_1740865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_1740865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740865 prefixEnd_1740865 := by exact prefixLift 1740865
  have htrace : WordTrace (prefixWord ++ tailWord_1740865) baseStart_1740865 baseEnd_1740865 := by
    simpa [prefixWord, tailWord_1740865, baseEnd_1740865] using wordTrace_append hprefix tailTrace_1740865
  have hstable : (prefixWord ++ tailWord_1740865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740865).length < 2 ^ (prefixWord ++ tailWord_1740865).sum := by decide
  have hdescent : baseEnd_1740865 < baseStart_1740865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740910 : List Nat := [4, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1740910 : Nat := 118140960795 + 1740910 * 2 ^ 59
def prefixEnd_1740910 : Nat := 4983230072969 + 3 ^ 40 * 1740910 * 2
def baseEnd_1740910 : Nat := 66216563423621401134719

theorem tailTrace_1740910 : CollatzResearch.WordTrace tailWord_1740910 prefixEnd_1740910 66216563423621401134719 := by
  unfold tailWord_1740910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937025515373483575244523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42330802748658579067970789 7937025515373483575244523)
  ·
    refine ⟨11905538273060225362866785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937025515373483575244523 11905538273060225362866785)
    ·
      refine ⟨8929153704795169022150089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11905538273060225362866785 8929153704795169022150089)
      ·
        refine ⟨6696865278596376766612567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8929153704795169022150089 6696865278596376766612567)
        ·
          refine ⟨10045297917894565149918851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6696865278596376766612567 10045297917894565149918851)
          ·
            refine ⟨15067946876841847724878277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045297917894565149918851 15067946876841847724878277)
            ·
              refine ⟨2825240039407846448414677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15067946876841847724878277 2825240039407846448414677)
              ·
                refine ⟨66216563423621401134719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2825240039407846448414677 66216563423621401134719)
                ·
                  rfl

theorem cell22_1740910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1740910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740910 prefixEnd_1740910 := by exact prefixLift 1740910
  have htrace : WordTrace (prefixWord ++ tailWord_1740910) baseStart_1740910 baseEnd_1740910 := by
    simpa [prefixWord, tailWord_1740910, baseEnd_1740910] using wordTrace_append hprefix tailTrace_1740910
  have hstable : (prefixWord ++ tailWord_1740910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740910).length < 2 ^ (prefixWord ++ tailWord_1740910).sum := by decide
  have hdescent : baseEnd_1740910 < baseStart_1740910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740914 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1740914 : Nat := 118140960795 + 1740914 * 2 ^ 59
def prefixEnd_1740914 : Nat := 4983230072969 + 3 ^ 40 * 1740914 * 2
def baseEnd_1740914 : Nat := 595950440094337933112459

theorem tailTrace_1740914 : CollatzResearch.WordTrace tailWord_1740914 prefixEnd_1740914 595950440094337933112459 := by
  unfold tailWord_1740914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874087503743344321275449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42330900009982251523401197 15874087503743344321275449)
  ·
    refine ⟨11905565627807508240956587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15874087503743344321275449 11905565627807508240956587)
    ·
      refine ⟨17858348441711262361434881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11905565627807508240956587 17858348441711262361434881)
      ·
        refine ⟨13393761331283446771076161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17858348441711262361434881 13393761331283446771076161)
        ·
          refine ⟨10045320998462585078307121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13393761331283446771076161 10045320998462585078307121)
          ·
            refine ⟨7533990748846938808730341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10045320998462585078307121 7533990748846938808730341)
            ·
              refine ⟨1412623265408801026636939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7533990748846938808730341 1412623265408801026636939)
              ·
                refine ⟨2118934898113201539955409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412623265408801026636939 2118934898113201539955409)
                ·
                  refine ⟨1589201173584901154966557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118934898113201539955409 1589201173584901154966557)
                  ·
                    refine ⟨595950440094337933112459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589201173584901154966557 595950440094337933112459)
                    ·
                      rfl

theorem cell22_1740914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1740914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740914 prefixEnd_1740914 := by exact prefixLift 1740914
  have htrace : WordTrace (prefixWord ++ tailWord_1740914) baseStart_1740914 baseEnd_1740914 := by
    simpa [prefixWord, tailWord_1740914, baseEnd_1740914] using wordTrace_append hprefix tailTrace_1740914
  have hstable : (prefixWord ++ tailWord_1740914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740914).length < 2 ^ (prefixWord ++ tailWord_1740914).sum := by decide
  have hdescent : baseEnd_1740914 < baseStart_1740914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740950 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1740950 : Nat := 118140960795 + 1740950 * 2 ^ 59
def prefixEnd_1740950 : Nat := 4983230072969 + 3 ^ 40 * 1740950 * 2
def baseEnd_1740950 : Nat := 198654254543348613070783

theorem tailTrace_1740950 : CollatzResearch.WordTrace tailWord_1740950 prefixEnd_1740950 198654254543348613070783 := by
  unfold tailWord_1740950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968603940177684714588269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42331775361895303622274869 3968603940177684714588269)
  ·
    refine ⟨1488226477566631767970601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3968603940177684714588269 1488226477566631767970601)
    ·
      refine ⟨1116169858174973825977951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488226477566631767970601 1116169858174973825977951)
      ·
        refine ⟨1674254787262460738966927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116169858174973825977951 1674254787262460738966927)
        ·
          refine ⟨2511382180893691108450391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674254787262460738966927 2511382180893691108450391)
          ·
            refine ⟨3767073271340536662675587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511382180893691108450391 3767073271340536662675587)
            ·
              refine ⟨5650609907010804994013381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767073271340536662675587 5650609907010804994013381)
              ·
                refine ⟨1059489357564525936377509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5650609907010804994013381 1059489357564525936377509)
                ·
                  refine ⟨198654254543348613070783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059489357564525936377509 198654254543348613070783)
                  ·
                    rfl

theorem cell22_1740950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1740950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740950 prefixEnd_1740950 := by exact prefixLift 1740950
  have htrace : WordTrace (prefixWord ++ tailWord_1740950) baseStart_1740950 baseEnd_1740950 := by
    simpa [prefixWord, tailWord_1740950, baseEnd_1740950] using wordTrace_append hprefix tailTrace_1740950
  have hstable : (prefixWord ++ tailWord_1740950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740950).length < 2 ^ (prefixWord ++ tailWord_1740950).sum := by decide
  have hdescent : baseEnd_1740950 < baseStart_1740950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740953 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1740953 : Nat := 118140960795 + 1740953 * 2 ^ 59
def prefixEnd_1740953 : Nat := 4983230072969 + 3 ^ 40 * 1740953 * 2
def baseEnd_1740953 : Nat := 595963790591354831387339

theorem tailTrace_1740953 : CollatzResearch.WordTrace tailWord_1740953 prefixEnd_1740953 595963790591354831387339 := by
  unfold tailWord_1740953
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497772461832086945771513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42331848307888057963847675 63497772461832086945771513)
  ·
    refine ⟨47623329346374065209328635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63497772461832086945771513 47623329346374065209328635)
    ·
      refine ⟨71434994019561097813992953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47623329346374065209328635 71434994019561097813992953)
      ·
        refine ⟨53576245514670823360494715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71434994019561097813992953 53576245514670823360494715)
        ·
          refine ⟨80364368272006235040742073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53576245514670823360494715 80364368272006235040742073)
          ·
            refine ⟨60273276204004676280556555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80364368272006235040742073 60273276204004676280556555)
            ·
              refine ⟨90409914306007014420834833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60273276204004676280556555 90409914306007014420834833)
              ·
                refine ⟨67807435729505260815626125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90409914306007014420834833 67807435729505260815626125)
                ·
                  refine ⟨25427788398564472805859797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67807435729505260815626125 25427788398564472805859797)
                  ·
                    refine ⟨595963790591354831387339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25427788398564472805859797 595963790591354831387339)
                    ·
                      rfl

theorem cell22_1740953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1740953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740953 prefixEnd_1740953 := by exact prefixLift 1740953
  have htrace : WordTrace (prefixWord ++ tailWord_1740953) baseStart_1740953 baseEnd_1740953 := by
    simpa [prefixWord, tailWord_1740953, baseEnd_1740953] using wordTrace_append hprefix tailTrace_1740953
  have hstable : (prefixWord ++ tailWord_1740953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740953).length < 2 ^ (prefixWord ++ tailWord_1740953).sum := by decide
  have hdescent : baseEnd_1740953 < baseStart_1740953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740980 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1740980 : Nat := 118140960795 + 1740980 * 2 ^ 59
def prefixEnd_1740980 : Nat := 4983230072969 + 3 ^ 40 * 1740980 * 2
def baseEnd_1740980 : Nat := 595973033243135760962257

theorem tailTrace_1740980 : CollatzResearch.WordTrace tailWord_1740980 prefixEnd_1740980 595973033243135760962257 := by
  unfold tailWord_1740980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749378616367135278502197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42332504821822847038002929 31749378616367135278502197)
  ·
    refine ⟨2976504245284418932359581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31749378616367135278502197 2976504245284418932359581)
    ·
      refine ⟨1116189091981657099634843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2976504245284418932359581 1116189091981657099634843)
      ·
        refine ⟨1674283637972485649452265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116189091981657099634843 1674283637972485649452265)
        ·
          refine ⟨1255712728479364237089199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674283637972485649452265 1255712728479364237089199)
          ·
            refine ⟨1883569092719046355633799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255712728479364237089199 1883569092719046355633799)
            ·
              refine ⟨2825353639078569533450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883569092719046355633799 2825353639078569533450699)
              ·
                refine ⟨4238030458617854300176049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825353639078569533450699 4238030458617854300176049)
                ·
                  refine ⟨3178522843963390725132037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4238030458617854300176049 3178522843963390725132037)
                  ·
                    refine ⟨595973033243135760962257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178522843963390725132037 595973033243135760962257)
                    ·
                      rfl

theorem cell22_1740980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1740980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740980 prefixEnd_1740980 := by exact prefixLift 1740980
  have htrace : WordTrace (prefixWord ++ tailWord_1740980) baseStart_1740980 baseEnd_1740980 := by
    simpa [prefixWord, tailWord_1740980, baseEnd_1740980] using wordTrace_append hprefix tailTrace_1740980
  have hstable : (prefixWord ++ tailWord_1740980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740980).length < 2 ^ (prefixWord ++ tailWord_1740980).sum := by decide
  have hdescent : baseEnd_1740980 < baseStart_1740980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740985 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1740985 : Nat := 118140960795 + 1740985 * 2 ^ 59
def prefixEnd_1740985 : Nat := 4983230072969 + 3 ^ 40 * 1740985 * 2
def baseEnd_1740985 : Nat := 595974744845317414587241

theorem tailTrace_1740985 : CollatzResearch.WordTrace tailWord_1740985 prefixEnd_1740985 595974744845317414587241 := by
  unfold tailWord_1740985
  simp only [CollatzResearch.WordTrace]
  refine ⟨63498939597716156410936409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42332626398477437607290939 63498939597716156410936409)
  ·
    refine ⟨47624204698287117308202307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63498939597716156410936409 47624204698287117308202307)
    ·
      refine ⟨71436307047430675962303461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47624204698287117308202307 71436307047430675962303461)
      ·
        refine ⟨13394307571393251742931899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71436307047430675962303461 13394307571393251742931899)
        ·
          refine ⟨20091461357089877614397849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13394307571393251742931899 20091461357089877614397849)
          ·
            refine ⟨15068596017817408210798387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20091461357089877614397849 15068596017817408210798387)
            ·
              refine ⟨22602894026726112316197581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15068596017817408210798387 22602894026726112316197581)
              ·
                refine ⟨8476085260022292118574093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22602894026726112316197581 8476085260022292118574093)
                ·
                  refine ⟨3178531972508359544465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8476085260022292118574093 3178531972508359544465285)
                  ·
                    refine ⟨595974744845317414587241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178531972508359544465285 595974744845317414587241)
                    ·
                      rfl

theorem cell22_1740985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1740985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740985 prefixEnd_1740985 := by exact prefixLift 1740985
  have htrace : WordTrace (prefixWord ++ tailWord_1740985) baseStart_1740985 baseEnd_1740985 := by
    simpa [prefixWord, tailWord_1740985, baseEnd_1740985] using wordTrace_append hprefix tailTrace_1740985
  have hstable : (prefixWord ++ tailWord_1740985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740985).length < 2 ^ (prefixWord ++ tailWord_1740985).sum := by decide
  have hdescent : baseEnd_1740985 < baseStart_1740985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740993 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1740993 : Nat := 118140960795 + 1740993 * 2 ^ 59
def prefixEnd_1740993 : Nat := 4983230072969 + 3 ^ 40 * 1740993 * 2
def baseEnd_1740993 : Nat := 595977483408808060387217

theorem tailTrace_1740993 : CollatzResearch.WordTrace tailWord_1740993 prefixEnd_1740993 595977483408808060387217 := by
  unfold tailWord_1740993
  simp only [CollatzResearch.WordTrace]
  refine ⟨63499231381687173777227633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42332820921124782518151755 63499231381687173777227633)
  ·
    refine ⟨47624423536265380332920725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63499231381687173777227633 47624423536265380332920725)
    ·
      refine ⟨2232394853262439703105659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47624423536265380332920725 2232394853262439703105659)
      ·
        refine ⟨3348592279893659554658489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232394853262439703105659 3348592279893659554658489)
        ·
          refine ⟨2511444209920244665993867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348592279893659554658489 2511444209920244665993867)
          ·
            refine ⟨3767166314880366998990801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511444209920244665993867 3767166314880366998990801)
            ·
              refine ⟨2825374736160275249243101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3767166314880366998990801 2825374736160275249243101)
              ·
                refine ⟨1059515526060103218466163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2825374736160275249243101 1059515526060103218466163)
                ·
                  refine ⟨1589273289090154827699245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059515526060103218466163 1589273289090154827699245)
                  ·
                    refine ⟨595977483408808060387217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589273289090154827699245 595977483408808060387217)
                    ·
                      rfl

theorem cell22_1740993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1740993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1740993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1740993 prefixEnd_1740993 := by exact prefixLift 1740993
  have htrace : WordTrace (prefixWord ++ tailWord_1740993) baseStart_1740993 baseEnd_1740993 := by
    simpa [prefixWord, tailWord_1740993, baseEnd_1740993] using wordTrace_append hprefix tailTrace_1740993
  have hstable : (prefixWord ++ tailWord_1740993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740993).length < 2 ^ (prefixWord ++ tailWord_1740993).sum := by decide
  have hdescent : baseEnd_1740993 < baseStart_1740993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741002 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1741002 : Nat := 118140960795 + 1741002 * 2 ^ 59
def prefixEnd_1741002 : Nat := 4983230072969 + 3 ^ 40 * 1741002 * 2
def baseEnd_1741002 : Nat := 595980564292735036912189

theorem tailTrace_1741002 : CollatzResearch.WordTrace tailWord_1741002 prefixEnd_1741002 595980564292735036912189 := by
  unfold tailWord_1741002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874889909663642078576315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42333039759103045542870173 15874889909663642078576315)
  ·
    refine ⟨23812334864495463117864473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15874889909663642078576315 23812334864495463117864473)
    ·
      refine ⟨17859251148371597338398355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23812334864495463117864473 17859251148371597338398355)
      ·
        refine ⟨26788876722557396007597533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17859251148371597338398355 26788876722557396007597533)
        ·
          refine ⟨10045828770959023502849075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26788876722557396007597533 10045828770959023502849075)
          ·
            refine ⟨15068743156438535254273613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045828770959023502849075 15068743156438535254273613)
            ·
              refine ⟨5650778683664450720352605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15068743156438535254273613 5650778683664450720352605)
              ·
                refine ⟨2119042006374169020132227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5650778683664450720352605 2119042006374169020132227)
                ·
                  refine ⟨3178563009561253530198341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119042006374169020132227 3178563009561253530198341)
                  ·
                    refine ⟨595980564292735036912189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178563009561253530198341 595980564292735036912189)
                    ·
                      rfl

theorem cell22_1741002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1741002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741002 prefixEnd_1741002 := by exact prefixLift 1741002
  have htrace : WordTrace (prefixWord ++ tailWord_1741002) baseStart_1741002 baseEnd_1741002 := by
    simpa [prefixWord, tailWord_1741002, baseEnd_1741002] using wordTrace_append hprefix tailTrace_1741002
  have hstable : (prefixWord ++ tailWord_1741002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741002).length < 2 ^ (prefixWord ++ tailWord_1741002).sum := by decide
  have hdescent : baseEnd_1741002 < baseStart_1741002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741017 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 4]
def baseStart_1741017 : Nat := 118140960795 + 1741017 * 2 ^ 59
def prefixEnd_1741017 : Nat := 4983230072969 + 3 ^ 40 * 1741017 * 2
def baseEnd_1741017 : Nat := 198661899699759999262381

theorem tailTrace_1741017 : CollatzResearch.WordTrace tailWord_1741017 prefixEnd_1741017 198661899699759999262381 := by
  unfold tailWord_1741017
  simp only [CollatzResearch.WordTrace]
  refine ⟨63500106733600225876101305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42333404489066817250734203 63500106733600225876101305)
  ·
    refine ⟨47625080050200169407075979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63500106733600225876101305 47625080050200169407075979)
    ·
      refine ⟨71437620075300254110613969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47625080050200169407075979 71437620075300254110613969)
      ·
        refine ⟨53578215056475190582960477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71437620075300254110613969 53578215056475190582960477)
        ·
          refine ⟨20091830646178196468610179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53578215056475190582960477 20091830646178196468610179)
          ·
            refine ⟨30137745969267294702915269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091830646178196468610179 30137745969267294702915269)
            ·
              refine ⟨5650827369237617756796613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30137745969267294702915269 5650827369237617756796613)
              ·
                refine ⟨1059530131732053329399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5650827369237617756796613 1059530131732053329399365)
                ·
                  refine ⟨198661899699759999262381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059530131732053329399365 198661899699759999262381)
                  ·
                    rfl

theorem cell22_1741017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_1741017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741017 prefixEnd_1741017 := by exact prefixLift 1741017
  have htrace : WordTrace (prefixWord ++ tailWord_1741017) baseStart_1741017 baseEnd_1741017 := by
    simpa [prefixWord, tailWord_1741017, baseEnd_1741017] using wordTrace_append hprefix tailTrace_1741017
  have hstable : (prefixWord ++ tailWord_1741017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741017).length < 2 ^ (prefixWord ++ tailWord_1741017).sum := by decide
  have hdescent : baseEnd_1741017 < baseStart_1741017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741032 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1741032 : Nat := 118140960795 + 1741032 * 2 ^ 59
def prefixEnd_1741032 : Nat := 4983230072969 + 3 ^ 40 * 1741032 * 2
def baseEnd_1741032 : Nat := 595990833905824958662097

theorem tailTrace_1741032 : CollatzResearch.WordTrace tailWord_1741032 prefixEnd_1741032 595990833905824958662097 := by
  unfold tailWord_1741032
  simp only [CollatzResearch.WordTrace]
  refine ⟨31750326914272941718948675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42333769219030588958598233 31750326914272941718948675)
  ·
    refine ⟨47625490371409412578423013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31750326914272941718948675 47625490371409412578423013)
    ·
      refine ⟨8929779444639264858454315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47625490371409412578423013 8929779444639264858454315)
      ·
        refine ⟨13394669166958897287681473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8929779444639264858454315 13394669166958897287681473)
        ·
          refine ⟨10046001875219172965761105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13394669166958897287681473 10046001875219172965761105)
          ·
            refine ⟨7534501406414379724320829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046001875219172965761105 7534501406414379724320829)
            ·
              refine ⟨2825438027405392396620311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7534501406414379724320829 2825438027405392396620311)
              ·
                refine ⟨4238157041108088594930467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825438027405392396620311 4238157041108088594930467)
                ·
                  refine ⟨6357235561662132892395701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238157041108088594930467 6357235561662132892395701)
                  ·
                    refine ⟨595990833905824958662097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6357235561662132892395701 595990833905824958662097)
                    ·
                      rfl

theorem cell22_1741032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1741032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741032 prefixEnd_1741032 := by exact prefixLift 1741032
  have htrace : WordTrace (prefixWord ++ tailWord_1741032) baseStart_1741032 baseEnd_1741032 := by
    simpa [prefixWord, tailWord_1741032, baseEnd_1741032] using wordTrace_append hprefix tailTrace_1741032
  have hstable : (prefixWord ++ tailWord_1741032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741032).length < 2 ^ (prefixWord ++ tailWord_1741032).sum := by decide
  have hdescent : baseEnd_1741032 < baseStart_1741032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741137 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1741137 : Nat := 118140960795 + 1741137 * 2 ^ 59
def prefixEnd_1741137 : Nat := 4983230072969 + 3 ^ 40 * 1741137 * 2
def baseEnd_1741137 : Nat := 596026777551639684786775

theorem tailTrace_1741137 : CollatzResearch.WordTrace tailWord_1741137 prefixEnd_1741137 596026777551639684786775 := by
  unfold tailWord_1741137
  simp only [CollatzResearch.WordTrace]
  refine ⟨63504483493165486370469665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42336322328776990913646443 63504483493165486370469665)
  ·
    refine ⟨47628362619874114777852249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63504483493165486370469665 47628362619874114777852249)
    ·
      refine ⟨35721271964905586083389187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47628362619874114777852249 35721271964905586083389187)
      ·
        refine ⟨53581907947358379125083781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35721271964905586083389187 53581907947358379125083781)
        ·
          refine ⟨10046607740129696085953209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53581907947358379125083781 10046607740129696085953209)
          ·
            refine ⟨7534955805097272064464907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046607740129696085953209 7534955805097272064464907)
            ·
              refine ⟨11302433707645908096697361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534955805097272064464907 11302433707645908096697361)
              ·
                refine ⟨8476825280734431072523021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11302433707645908096697361 8476825280734431072523021)
                ·
                  refine ⟨3178809480275411652196133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8476825280734431072523021 3178809480275411652196133)
                  ·
                    refine ⟨596026777551639684786775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178809480275411652196133 596026777551639684786775)
                    ·
                      rfl

theorem cell22_1741137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1741137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741137 prefixEnd_1741137 := by exact prefixLift 1741137
  have htrace : WordTrace (prefixWord ++ tailWord_1741137) baseStart_1741137 baseEnd_1741137 := by
    simpa [prefixWord, tailWord_1741137, baseEnd_1741137] using wordTrace_append hprefix tailTrace_1741137
  have hstable : (prefixWord ++ tailWord_1741137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741137).length < 2 ^ (prefixWord ++ tailWord_1741137).sum := by decide
  have hdescent : baseEnd_1741137 < baseStart_1741137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741154 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1741154 : Nat := 118140960795 + 1741154 * 2 ^ 59
def prefixEnd_1741154 : Nat := 4983230072969 + 3 ^ 40 * 1741154 * 2
def baseEnd_1741154 : Nat := 596032596999057307111723

theorem tailTrace_1741154 : CollatzResearch.WordTrace tailWord_1741154 prefixEnd_1741154 596032596999057307111723 := by
  unfold tailWord_1741154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876275883525974568459629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42336735689402598849225677 15876275883525974568459629)
  ·
    refine ⟨5953603456322240463172361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15876275883525974568459629 5953603456322240463172361)
    ·
      refine ⟨4465202592241680347379271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5953603456322240463172361 4465202592241680347379271)
      ·
        refine ⟨6697803888362520521068907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465202592241680347379271 6697803888362520521068907)
        ·
          refine ⟨10046705832543780781603361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697803888362520521068907 10046705832543780781603361)
          ·
            refine ⟨7535029374407835586202521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046705832543780781603361 7535029374407835586202521)
            ·
              refine ⟨5651272030805876689651891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7535029374407835586202521 5651272030805876689651891)
              ·
                refine ⟨8476908046208815034477837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5651272030805876689651891 8476908046208815034477837)
                ·
                  refine ⟨3178840517328305637929189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8476908046208815034477837 3178840517328305637929189)
                  ·
                    refine ⟨596032596999057307111723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3178840517328305637929189 596032596999057307111723)
                    ·
                      rfl

theorem cell22_1741154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1741154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741154 prefixEnd_1741154 := by exact prefixLift 1741154
  have htrace : WordTrace (prefixWord ++ tailWord_1741154) baseStart_1741154 baseEnd_1741154 := by
    simpa [prefixWord, tailWord_1741154, baseEnd_1741154] using wordTrace_append hprefix tailTrace_1741154
  have hstable : (prefixWord ++ tailWord_1741154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741154).length < 2 ^ (prefixWord ++ tailWord_1741154).sum := by decide
  have hdescent : baseEnd_1741154 < baseStart_1741154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741246 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1741246 : Nat := 118140960795 + 1741246 * 2 ^ 59
def prefixEnd_1741246 : Nat := 4983230072969 + 3 ^ 40 * 1741246 * 2
def baseEnd_1741246 : Nat := 596064090479199733811441

theorem tailTrace_1741246 : CollatzResearch.WordTrace tailWord_1741246 prefixEnd_1741246 596064090479199733811441 := by
  unfold tailWord_1741246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938557381221324748273449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42338972699847065324125061 7938557381221324748273449)
  ·
    refine ⟨5953918035915993561205087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7938557381221324748273449 5953918035915993561205087)
    ·
      refine ⟨8930877053873990341807631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953918035915993561205087 8930877053873990341807631)
      ·
        refine ⟨13396315580810985512711447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930877053873990341807631 13396315580810985512711447)
        ·
          refine ⟨20094473371216478269067171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396315580810985512711447 20094473371216478269067171)
          ·
            refine ⟨30141710056824717403600757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094473371216478269067171 30141710056824717403600757)
            ·
              refine ⟨2825785317827317256587571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30141710056824717403600757 2825785317827317256587571)
              ·
                refine ⟨4238677976740975884881357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825785317827317256587571 4238677976740975884881357)
                ·
                  refine ⟨1589504241277865956830509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4238677976740975884881357 1589504241277865956830509)
                  ·
                    refine ⟨596064090479199733811441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589504241277865956830509 596064090479199733811441)
                    ·
                      rfl

theorem cell22_1741246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1741246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741246 prefixEnd_1741246 := by exact prefixLift 1741246
  have htrace : WordTrace (prefixWord ++ tailWord_1741246) baseStart_1741246 baseEnd_1741246 := by
    simpa [prefixWord, tailWord_1741246, baseEnd_1741246] using wordTrace_append hprefix tailTrace_1741246
  have hstable : (prefixWord ++ tailWord_1741246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741246).length < 2 ^ (prefixWord ++ tailWord_1741246).sum := by decide
  have hdescent : baseEnd_1741246 < baseStart_1741246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741252 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1741252 : Nat := 118140960795 + 1741252 * 2 ^ 59
def prefixEnd_1741252 : Nat := 4983230072969 + 3 ^ 40 * 1741252 * 2
def baseEnd_1741252 : Nat := 596066144401817718161423

theorem tailTrace_1741252 : CollatzResearch.WordTrace tailWord_1741252 prefixEnd_1741252 596066144401817718161423 := by
  unfold tailWord_1741252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754338943874430505453005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42339118591832574007270673 31754338943874430505453005)
  ·
    refine ⟨11907877103952911439544877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31754338943874430505453005 11907877103952911439544877)
    ·
      refine ⟨4465453913982341789829329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11907877103952911439544877 4465453913982341789829329)
      ·
        refine ⟨3349090435486756342371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465453913982341789829329 3349090435486756342371997)
        ·
          refine ⟨1255908913307533628389499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3349090435486756342371997 1255908913307533628389499)
          ·
            refine ⟨1883863369961300442584249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255908913307533628389499 1883863369961300442584249)
            ·
              refine ⟨1412897527470975331938187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883863369961300442584249 1412897527470975331938187)
              ·
                refine ⟨2119346291206462997907281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412897527470975331938187 2119346291206462997907281)
                ·
                  refine ⟨1589509718404847248430461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119346291206462997907281 1589509718404847248430461)
                  ·
                    refine ⟨596066144401817718161423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589509718404847248430461 596066144401817718161423)
                    ·
                      rfl

theorem cell22_1741252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1741252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741252 prefixEnd_1741252 := by exact prefixLift 1741252
  have htrace : WordTrace (prefixWord ++ tailWord_1741252) baseStart_1741252 baseEnd_1741252 := by
    simpa [prefixWord, tailWord_1741252, baseEnd_1741252] using wordTrace_append hprefix tailTrace_1741252
  have hstable : (prefixWord ++ tailWord_1741252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741252).length < 2 ^ (prefixWord ++ tailWord_1741252).sum := by decide
  have hdescent : baseEnd_1741252 < baseStart_1741252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741257 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1741257 : Nat := 118140960795 + 1741257 * 2 ^ 59
def prefixEnd_1741257 : Nat := 4983230072969 + 3 ^ 40 * 1741257 * 2
def baseEnd_1741257 : Nat := 596067856003999371786407

theorem tailTrace_1741257 : CollatzResearch.WordTrace tailWord_1741257 prefixEnd_1741257 596067856003999371786407 := by
  unfold tailWord_1741257
  simp only [CollatzResearch.WordTrace]
  refine ⟨63508860252730746864838025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42339240168487164576558683 63508860252730746864838025)
  ·
    refine ⟨47631645189548060148628519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63508860252730746864838025 47631645189548060148628519)
    ·
      refine ⟨71447467784322090222942779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47631645189548060148628519 71447467784322090222942779)
      ·
        refine ⟨107171201676483135334414169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71447467784322090222942779 107171201676483135334414169)
        ·
          refine ⟨80378401257362351500810627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107171201676483135334414169 80378401257362351500810627)
          ·
            refine ⟨120567601886043527251215941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80378401257362351500810627 120567601886043527251215941)
            ·
              refine ⟨22606425353633161359602989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120567601886043527251215941 22606425353633161359602989)
              ·
                refine ⟨8477409507612435509851121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22606425353633161359602989 8477409507612435509851121)
                ·
                  refine ⟨6358057130709326632388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8477409507612435509851121 6358057130709326632388341)
                  ·
                    refine ⟨596067856003999371786407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6358057130709326632388341 596067856003999371786407)
                    ·
                      rfl

theorem cell22_1741257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1741257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741257 prefixEnd_1741257 := by exact prefixLift 1741257
  have htrace : WordTrace (prefixWord ++ tailWord_1741257) baseStart_1741257 baseEnd_1741257 := by
    simpa [prefixWord, tailWord_1741257, baseEnd_1741257] using wordTrace_append hprefix tailTrace_1741257
  have hstable : (prefixWord ++ tailWord_1741257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741257).length < 2 ^ (prefixWord ++ tailWord_1741257).sum := by decide
  have hdescent : baseEnd_1741257 < baseStart_1741257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741381 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1741381 : Nat := 118140960795 + 1741381 * 2 ^ 59
def prefixEnd_1741381 : Nat := 4983230072969 + 3 ^ 40 * 1741381 * 2
def baseEnd_1741381 : Nat := 596110303738104381686027

theorem tailTrace_1741381 : CollatzResearch.WordTrace tailWord_1741381 prefixEnd_1741381 596110303738104381686027 := by
  unfold tailWord_1741381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63513382904281516042351997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42342255269521010694901331 63513382904281516042351997)
  ·
    refine ⟨23817518589105568515881999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63513382904281516042351997 23817518589105568515881999)
    ·
      refine ⟨35726277883658352773822999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23817518589105568515881999 35726277883658352773822999)
      ·
        refine ⟨53589416825487529160734499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726277883658352773822999 53589416825487529160734499)
        ·
          refine ⟨80384125238231293741101749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53589416825487529160734499 80384125238231293741101749)
          ·
            refine ⟨7536011741084183788228289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80384125238231293741101749 7536011741084183788228289)
            ·
              refine ⟨5652008805813137841171217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536011741084183788228289 5652008805813137841171217)
              ·
                refine ⟨4239006604359853380878413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652008805813137841171217 4239006604359853380878413)
                ·
                  refine ⟨1589627476634945017829405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4239006604359853380878413 1589627476634945017829405)
                  ·
                    refine ⟨596110303738104381686027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589627476634945017829405 596110303738104381686027)
                    ·
                      rfl

theorem cell22_1741381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1741381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741381 prefixEnd_1741381 := by exact prefixLift 1741381
  have htrace : WordTrace (prefixWord ++ tailWord_1741381) baseStart_1741381 baseEnd_1741381 := by
    simpa [prefixWord, tailWord_1741381, baseEnd_1741381] using wordTrace_append hprefix tailTrace_1741381
  have hstable : (prefixWord ++ tailWord_1741381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741381).length < 2 ^ (prefixWord ++ tailWord_1741381).sum := by decide
  have hdescent : baseEnd_1741381 < baseStart_1741381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741394 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1741394 : Nat := 118140960795 + 1741394 * 2 ^ 59
def prefixEnd_1741394 : Nat := 4983230072969 + 3 ^ 40 * 1741394 * 2
def baseEnd_1741394 : Nat := 198704917967925560370329

theorem tailTrace_1741394 : CollatzResearch.WordTrace tailWord_1741394 prefixEnd_1741394 198704917967925560370329 := by
  unfold tailWord_1741394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878464263308604815643809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42342571368822946175050157 15878464263308604815643809)
  ·
    refine ⟨11908848197481453611732857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15878464263308604815643809 11908848197481453611732857)
    ·
      refine ⟨8931636148111090208799643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11908848197481453611732857 8931636148111090208799643)
      ·
        refine ⟨13397454222166635313199465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931636148111090208799643 13397454222166635313199465)
        ·
          refine ⟨10048090666624976484899599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13397454222166635313199465 10048090666624976484899599)
          ·
            refine ⟨15072135999937464727349399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048090666624976484899599 15072135999937464727349399)
            ·
              refine ⟨22608203999906197091024099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072135999937464727349399 22608203999906197091024099)
              ·
                refine ⟨33912305999859295636536149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22608203999906197091024099 33912305999859295636536149)
                ·
                  refine ⟨198704917967925560370329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33912305999859295636536149 198704917967925560370329)
                  ·
                    rfl

theorem cell22_1741394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1741394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741394 prefixEnd_1741394 := by exact prefixLift 1741394
  have htrace : WordTrace (prefixWord ++ tailWord_1741394) baseStart_1741394 baseEnd_1741394 := by
    simpa [prefixWord, tailWord_1741394, baseEnd_1741394] using wordTrace_append hprefix tailTrace_1741394
  have hstable : (prefixWord ++ tailWord_1741394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741394).length < 2 ^ (prefixWord ++ tailWord_1741394).sum := by decide
  have hdescent : baseEnd_1741394 < baseStart_1741394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741441 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1741441 : Nat := 118140960795 + 1741441 * 2 ^ 59
def prefixEnd_1741441 : Nat := 4983230072969 + 3 ^ 40 * 1741441 * 2
def baseEnd_1741441 : Nat := 596130842964284225185843

theorem tailTrace_1741441 : CollatzResearch.WordTrace tailWord_1741441 prefixEnd_1741441 596130842964284225185843 := by
  unfold tailWord_1741441
  simp only [CollatzResearch.WordTrace]
  refine ⟨63515571284064146289536177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42343714189376097526357451 63515571284064146289536177)
  ·
    refine ⟨47636678463048109717152133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63515571284064146289536177 47636678463048109717152133)
    ·
      refine ⟨8931877211821520571966025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47636678463048109717152133 8931877211821520571966025)
      ·
        refine ⟨6698907908866140428974519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8931877211821520571966025 6698907908866140428974519)
        ·
          refine ⟨10048361863299210643461779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698907908866140428974519 10048361863299210643461779)
          ·
            refine ⟨15072542794948815965192669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048361863299210643461779 15072542794948815965192669)
            ·
              refine ⟨5652203548105805986947251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15072542794948815965192669 5652203548105805986947251)
              ·
                refine ⟨8478305322158708980420877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5652203548105805986947251 8478305322158708980420877)
                ·
                  refine ⟨3179364495809515867657829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8478305322158708980420877 3179364495809515867657829)
                  ·
                    refine ⟨596130842964284225185843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179364495809515867657829 596130842964284225185843)
                    ·
                      rfl

theorem cell22_1741441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1741441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741441 prefixEnd_1741441 := by exact prefixLift 1741441
  have htrace : WordTrace (prefixWord ++ tailWord_1741441) baseStart_1741441 baseEnd_1741441 := by
    simpa [prefixWord, tailWord_1741441, baseEnd_1741441] using wordTrace_append hprefix tailTrace_1741441
  have hstable : (prefixWord ++ tailWord_1741441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741441).length < 2 ^ (prefixWord ++ tailWord_1741441).sum := by decide
  have hdescent : baseEnd_1741441 < baseStart_1741441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741466 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_1741466 : Nat := 118140960795 + 1741466 * 2 ^ 59
def prefixEnd_1741466 : Nat := 4983230072969 + 3 ^ 40 * 1741466 * 2
def baseEnd_1741466 : Nat := 596139400975192493310767

theorem tailTrace_1741466 : CollatzResearch.WordTrace tailWord_1741466 prefixEnd_1741466 596139400975192493310767 := by
  unfold tailWord_1741466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879120777243393889799063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42344322072649050372797501 15879120777243393889799063)
  ·
    refine ⟨23818681165865090834698595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15879120777243393889799063 23818681165865090834698595)
    ·
      refine ⟨35728021748797636252047893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23818681165865090834698595 35728021748797636252047893)
      ·
        refine ⟨1674751019474889199314745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35728021748797636252047893 1674751019474889199314745)
        ·
          refine ⟨1256063264606166899486059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674751019474889199314745 1256063264606166899486059)
          ·
            refine ⟨1884094896909250349229089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256063264606166899486059 1884094896909250349229089)
            ·
              refine ⟨1413071172681937761921817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884094896909250349229089 1413071172681937761921817)
              ·
                refine ⟨1059803379511453321441363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413071172681937761921817 1059803379511453321441363)
                ·
                  refine ⟨1589705069267179982162045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059803379511453321441363 1589705069267179982162045)
                  ·
                    refine ⟨596139400975192493310767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589705069267179982162045 596139400975192493310767)
                    ·
                      rfl

theorem cell22_1741466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_1741466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741466 prefixEnd_1741466 := by exact prefixLift 1741466
  have htrace : WordTrace (prefixWord ++ tailWord_1741466) baseStart_1741466 baseEnd_1741466 := by
    simpa [prefixWord, tailWord_1741466, baseEnd_1741466] using wordTrace_append hprefix tailTrace_1741466
  have hstable : (prefixWord ++ tailWord_1741466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741466).length < 2 ^ (prefixWord ++ tailWord_1741466).sum := by decide
  have hdescent : baseEnd_1741466 < baseStart_1741466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741503 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 2, 4]
def baseStart_1741503 : Nat := 118140960795 + 1741503 * 2 ^ 59
def prefixEnd_1741503 : Nat := 4983230072969 + 3 ^ 40 * 1741503 * 2
def baseEnd_1741503 : Nat := 596152066831336730135653

theorem tailTrace_1741503 : CollatzResearch.WordTrace tailWord_1741503 prefixEnd_1741503 596152066831336730135653 := by
  unfold tailWord_1741503
  simp only [CollatzResearch.WordTrace]
  refine ⟨63517832609839530878293163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42345221739893020585528775 63517832609839530878293163)
  ·
    refine ⟨95276748914759296317439745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63517832609839530878293163 95276748914759296317439745)
    ·
      refine ⟨71457561686069472238079809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95276748914759296317439745 71457561686069472238079809)
      ·
        refine ⟨53593171264552104178559857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71457561686069472238079809 53593171264552104178559857)
        ·
          refine ⟨40194878448414078133919893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53593171264552104178559857 40194878448414078133919893)
          ·
            refine ⟨1884134927269409912527495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40194878448414078133919893 1884134927269409912527495)
            ·
              refine ⟨2826202390904114868791243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884134927269409912527495 2826202390904114868791243)
              ·
                refine ⟨4239303586356172303186865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826202390904114868791243 4239303586356172303186865)
                ·
                  refine ⟨3179477689767129227390149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239303586356172303186865 3179477689767129227390149)
                  ·
                    refine ⟨596152066831336730135653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179477689767129227390149 596152066831336730135653)
                    ·
                      rfl

theorem cell22_1741503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_1741503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741503 prefixEnd_1741503 := by exact prefixLift 1741503
  have htrace : WordTrace (prefixWord ++ tailWord_1741503) baseStart_1741503 baseEnd_1741503 := by
    simpa [prefixWord, tailWord_1741503, baseEnd_1741503] using wordTrace_append hprefix tailTrace_1741503
  have hstable : (prefixWord ++ tailWord_1741503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741503).length < 2 ^ (prefixWord ++ tailWord_1741503).sum := by decide
  have hdescent : baseEnd_1741503 < baseStart_1741503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741522 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1741522 : Nat := 118140960795 + 1741522 * 2 ^ 59
def prefixEnd_1741522 : Nat := 4983230072969 + 3 ^ 40 * 1741522 * 2
def baseEnd_1741522 : Nat := 596158570919627013910595

theorem tailTrace_1741522 : CollatzResearch.WordTrace tailWord_1741522 prefixEnd_1741522 596158570919627013910595 := by
  unfold tailWord_1741522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879631399192674280808705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42345683731180464748823213 15879631399192674280808705)
  ·
    refine ⟨11909723549394505710606529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15879631399192674280808705 11909723549394505710606529)
    ·
      refine ⟨8932292662045879282954897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11909723549394505710606529 8932292662045879282954897)
      ·
        refine ⟨6699219496534409462216173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8932292662045879282954897 6699219496534409462216173)
        ·
          refine ⟨2512207311200403548331065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6699219496534409462216173 2512207311200403548331065)
          ·
            refine ⟨1884155483400302661248299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512207311200403548331065 1884155483400302661248299)
            ·
              refine ⟨2826233225100453991872449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884155483400302661248299 2826233225100453991872449)
              ·
                refine ⟨2119674918825340493904337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826233225100453991872449 2119674918825340493904337)
                ·
                  refine ⟨1589756189119005370428253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119674918825340493904337 1589756189119005370428253)
                  ·
                    refine ⟨596158570919627013910595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589756189119005370428253 596158570919627013910595)
                    ·
                      rfl

theorem cell22_1741522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1741522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741522 prefixEnd_1741522 := by exact prefixLift 1741522
  have htrace : WordTrace (prefixWord ++ tailWord_1741522) baseStart_1741522 baseEnd_1741522 := by
    simpa [prefixWord, tailWord_1741522, baseEnd_1741522] using wordTrace_append hprefix tailTrace_1741522
  have hstable : (prefixWord ++ tailWord_1741522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741522).length < 2 ^ (prefixWord ++ tailWord_1741522).sum := by decide
  have hdescent : baseEnd_1741522 < baseStart_1741522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741640 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1741640 : Nat := 118140960795 + 1741640 * 2 ^ 59
def prefixEnd_1741640 : Nat := 4983230072969 + 3 ^ 40 * 1741640 * 2
def baseEnd_1741640 : Nat := 596198964731114039460233

theorem tailTrace_1741640 : CollatzResearch.WordTrace tailWord_1741640 prefixEnd_1741640 596198964731114039460233 := by
  unfold tailWord_1741640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31761414705171601638015187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42348552940228802184020249 31761414705171601638015187)
  ·
    refine ⟨47642122057757402457022781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31761414705171601638015187 47642122057757402457022781)
    ·
      refine ⟨17865795771659025921383543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47642122057757402457022781 17865795771659025921383543)
      ·
        refine ⟨26798693657488538882075315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17865795771659025921383543 26798693657488538882075315)
        ·
          refine ⟨40198040486232808323112973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26798693657488538882075315 40198040486232808323112973)
          ·
            refine ⟨15074265182337303121167365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40198040486232808323112973 15074265182337303121167365)
            ·
              refine ⟨2826424721688244335218881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15074265182337303121167365 2826424721688244335218881)
              ·
                refine ⟨2119818541266183251414161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826424721688244335218881 2119818541266183251414161)
                ·
                  refine ⟨1589863905949637438560621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2119818541266183251414161 1589863905949637438560621)
                  ·
                    refine ⟨596198964731114039460233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1589863905949637438560621 596198964731114039460233)
                    ·
                      rfl

theorem cell22_1741640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1741640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741640 prefixEnd_1741640 := by exact prefixLift 1741640
  have htrace : WordTrace (prefixWord ++ tailWord_1741640) baseStart_1741640 baseEnd_1741640 := by
    simpa [prefixWord, tailWord_1741640, baseEnd_1741640] using wordTrace_append hprefix tailTrace_1741640
  have hstable : (prefixWord ++ tailWord_1741640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741640).length < 2 ^ (prefixWord ++ tailWord_1741640).sum := by decide
  have hdescent : baseEnd_1741640 < baseStart_1741640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741728 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_1741728 : Nat := 118140960795 + 1741728 * 2 ^ 59
def prefixEnd_1741728 : Nat := 4983230072969 + 3 ^ 40 * 1741728 * 2
def baseEnd_1741728 : Nat := 596229088929511143259963

theorem tailTrace_1741728 : CollatzResearch.WordTrace tailWord_1741728 prefixEnd_1741728 596229088929511143259963 := by
  unfold tailWord_1741728
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763019517012197152616919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42350692689349596203489225 31763019517012197152616919)
  ·
    refine ⟨47644529275518295728925379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31763019517012197152616919 47644529275518295728925379)
    ·
      refine ⟨71466793913277443593388069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47644529275518295728925379 71466793913277443593388069)
      ·
        refine ⟨13400023858739520673760263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71466793913277443593388069 13400023858739520673760263)
        ·
          refine ⟨20100035788109281010640395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13400023858739520673760263 20100035788109281010640395)
          ·
            refine ⟨30150053682163921515960593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20100035788109281010640395 30150053682163921515960593)
            ·
              refine ⟨22612540261622941136970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30150053682163921515960593 22612540261622941136970445)
              ·
                refine ⟨8479702598108602926363917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22612540261622941136970445 8479702598108602926363917)
                ·
                  refine ⟨3179888474290726097386469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8479702598108602926363917 3179888474290726097386469)
                  ·
                    refine ⟨596229088929511143259963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3179888474290726097386469 596229088929511143259963)
                    ·
                      rfl

theorem cell22_1741728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_1741728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741728 prefixEnd_1741728 := by exact prefixLift 1741728
  have htrace : WordTrace (prefixWord ++ tailWord_1741728) baseStart_1741728 baseEnd_1741728 := by
    simpa [prefixWord, tailWord_1741728, baseEnd_1741728] using wordTrace_append hprefix tailTrace_1741728
  have hstable : (prefixWord ++ tailWord_1741728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741728).length < 2 ^ (prefixWord ++ tailWord_1741728).sum := by decide
  have hdescent : baseEnd_1741728 < baseStart_1741728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741760 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_1741760 : Nat := 118140960795 + 1741760 * 2 ^ 59
def prefixEnd_1741760 : Nat := 4983230072969 + 3 ^ 40 * 1741760 * 2
def baseEnd_1741760 : Nat := 198746681061157908819955

theorem tailTrace_1741760 : CollatzResearch.WordTrace tailWord_1741760 prefixEnd_1741760 198746681061157908819955 := by
  unfold tailWord_1741760
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763603084954231885199367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42351470779938975846932489 31763603084954231885199367)
  ·
    refine ⟨47645404627431347827799051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31763603084954231885199367 47645404627431347827799051)
    ·
      refine ⟨71468106941147021741698577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47645404627431347827799051 71468106941147021741698577)
      ·
        refine ⟨53601080205860266306273933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71468106941147021741698577 53601080205860266306273933)
        ·
          refine ⟨20100405077197599864852725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53601080205860266306273933 20100405077197599864852725)
          ·
            refine ⟨1884412975987274987329943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20100405077197599864852725 1884412975987274987329943)
            ·
              refine ⟨2826619463980912480994915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884412975987274987329943 2826619463980912480994915)
              ·
                refine ⟨4239929195971368721492373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826619463980912480994915 4239929195971368721492373)
                ·
                  refine ⟨198746681061157908819955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4239929195971368721492373 198746681061157908819955)
                  ·
                    rfl

theorem cell22_1741760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_1741760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741760 prefixEnd_1741760 := by exact prefixLift 1741760
  have htrace : WordTrace (prefixWord ++ tailWord_1741760) baseStart_1741760 baseEnd_1741760 := by
    simpa [prefixWord, tailWord_1741760, baseEnd_1741760] using wordTrace_append hprefix tailTrace_1741760
  have hstable : (prefixWord ++ tailWord_1741760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741760).length < 2 ^ (prefixWord ++ tailWord_1741760).sum := by decide
  have hdescent : baseEnd_1741760 < baseStart_1741760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741895 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 6]
def baseStart_1741895 : Nat := 118140960795 + 1741895 * 2 ^ 59
def prefixEnd_1741895 : Nat := 4983230072969 + 3 ^ 40 * 1741895 * 2
def baseEnd_1741895 : Nat := 198762085480792791444817

theorem tailTrace_1741895 : CollatzResearch.WordTrace tailWord_1741895 prefixEnd_1741895 198762085480792791444817 := by
  unfold tailWord_1741895
  simp only [CollatzResearch.WordTrace]
  refine ⟨63532130024419381826563139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42354753349612921217708759 63532130024419381826563139)
  ·
    refine ⟨95298195036629072739844709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63532130024419381826563139 95298195036629072739844709)
    ·
      refine ⟨17868411569367951138720883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95298195036629072739844709 17868411569367951138720883)
      ·
        refine ⟨26802617354051926708081325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868411569367951138720883 26802617354051926708081325)
        ·
          refine ⟨10050981507769472515530497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26802617354051926708081325 10050981507769472515530497)
          ·
            refine ⟨7538236130827104386647873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10050981507769472515530497 7538236130827104386647873)
            ·
              refine ⟨5653677098120328289985905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538236130827104386647873 5653677098120328289985905)
              ·
                refine ⟨4240257823590246217489429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5653677098120328289985905 4240257823590246217489429)
                ·
                  refine ⟨198762085480792791444817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4240257823590246217489429 198762085480792791444817)
                  ·
                    rfl

theorem cell22_1741895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_1741895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741895 prefixEnd_1741895 := by exact prefixLift 1741895
  have htrace : WordTrace (prefixWord ++ tailWord_1741895) baseStart_1741895 baseEnd_1741895 := by
    simpa [prefixWord, tailWord_1741895, baseEnd_1741895] using wordTrace_append hprefix tailTrace_1741895
  have hstable : (prefixWord ++ tailWord_1741895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741895).length < 2 ^ (prefixWord ++ tailWord_1741895).sum := by decide
  have hdescent : baseEnd_1741895 < baseStart_1741895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741927 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1741927 : Nat := 118140960795 + 1741927 * 2 ^ 59
def prefixEnd_1741927 : Nat := 4983230072969 + 3 ^ 40 * 1741927 * 2
def baseEnd_1741927 : Nat := 596297210696340957534353

theorem tailTrace_1741927 : CollatzResearch.WordTrace tailWord_1741927 prefixEnd_1741927 596297210696340957534353 := by
  unfold tailWord_1741927
  simp only [CollatzResearch.WordTrace]
  refine ⟨63533297160303451291728035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42355531440202300861152023 63533297160303451291728035)
  ·
    refine ⟨95299945740455176937592053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63533297160303451291728035 95299945740455176937592053)
    ·
      refine ⟨8934369913167672837899255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95299945740455176937592053 8934369913167672837899255)
      ·
        refine ⟨13401554869751509256848883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8934369913167672837899255 13401554869751509256848883)
        ·
          refine ⟨20102332304627263885273325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13401554869751509256848883 20102332304627263885273325)
          ·
            refine ⟨7538374614235223956977497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20102332304627263885273325 7538374614235223956977497)
            ·
              refine ⟨5653780960676417967733123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538374614235223956977497 5653780960676417967733123)
              ·
                refine ⟨8480671441014626951599685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653780960676417967733123 8480671441014626951599685)
                ·
                  refine ⟨1590125895190242553424941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8480671441014626951599685 1590125895190242553424941)
                  ·
                    refine ⟨596297210696340957534353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590125895190242553424941 596297210696340957534353)
                    ·
                      rfl

theorem cell22_1741927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1741927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741927 prefixEnd_1741927 := by exact prefixLift 1741927
  have htrace : WordTrace (prefixWord ++ tailWord_1741927) baseStart_1741927 baseEnd_1741927 := by
    simpa [prefixWord, tailWord_1741927, baseEnd_1741927] using wordTrace_append hprefix tailTrace_1741927
  have hstable : (prefixWord ++ tailWord_1741927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741927).length < 2 ^ (prefixWord ++ tailWord_1741927).sum := by decide
  have hdescent : baseEnd_1741927 < baseStart_1741927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741929 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 4]
def baseStart_1741929 : Nat := 118140960795 + 1741929 * 2 ^ 59
def prefixEnd_1741929 : Nat := 4983230072969 + 3 ^ 40 * 1741929 * 2
def baseEnd_1741929 : Nat := 198765965112404539661449

theorem tailTrace_1741929 : CollatzResearch.WordTrace tailWord_1741929 prefixEnd_1741929 198765965112404539661449 := by
  unfold tailWord_1741929
  simp only [CollatzResearch.WordTrace]
  refine ⟨63533370106296205633300841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42355580070864137088867227 63533370106296205633300841)
  ·
    refine ⟨47650027579722154224975631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63533370106296205633300841 47650027579722154224975631)
    ·
      refine ⟨71475041369583231337463447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47650027579722154224975631 71475041369583231337463447)
      ·
        refine ⟨107212562054374847006195171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71475041369583231337463447 107212562054374847006195171)
        ·
          refine ⟨160818843081562270509292757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107212562054374847006195171 160818843081562270509292757)
          ·
            refine ⟨3769191634724115715061549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 160818843081562270509292757 3769191634724115715061549)
            ·
              refine ⟨1413446863021543393148081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3769191634724115715061549 1413446863021543393148081)
              ·
                refine ⟨1060085147266157544861061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413446863021543393148081 1060085147266157544861061)
                ·
                  refine ⟨198765965112404539661449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060085147266157544861061 198765965112404539661449)
                  ·
                    rfl

theorem cell22_1741929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_1741929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741929 prefixEnd_1741929 := by exact prefixLift 1741929
  have htrace : WordTrace (prefixWord ++ tailWord_1741929) baseStart_1741929 baseEnd_1741929 := by
    simpa [prefixWord, tailWord_1741929, baseEnd_1741929] using wordTrace_append hprefix tailTrace_1741929
  have hstable : (prefixWord ++ tailWord_1741929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741929).length < 2 ^ (prefixWord ++ tailWord_1741929).sum := by decide
  have hdescent : baseEnd_1741929 < baseStart_1741929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741942 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1741942 : Nat := 118140960795 + 1741942 * 2 ^ 59
def prefixEnd_1741942 : Nat := 4983230072969 + 3 ^ 40 * 1741942 * 2
def baseEnd_1741942 : Nat := 596302345502885918409307

theorem tailTrace_1741942 : CollatzResearch.WordTrace tailWord_1741942 prefixEnd_1741942 596302345502885918409307 := by
  unfold tailWord_1741942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970865265953069303345255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42355896170166072569016053 3970865265953069303345255)
  ·
    refine ⟨5956297898929603955017883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970865265953069303345255 5956297898929603955017883)
    ·
      refine ⟨8934446848394405932526825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956297898929603955017883 8934446848394405932526825)
      ·
        refine ⟨6700835136295804449395119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8934446848394405932526825 6700835136295804449395119)
        ·
          refine ⟨10051252704443706674092679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700835136295804449395119 10051252704443706674092679)
          ·
            refine ⟨15076879056665560011139019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10051252704443706674092679 15076879056665560011139019)
            ·
              refine ⟨22615318584998340016708529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15076879056665560011139019 22615318584998340016708529)
              ·
                refine ⟨16961488938748755012531397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22615318584998340016708529 16961488938748755012531397)
                ·
                  refine ⟨3180279176015391564849637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16961488938748755012531397 3180279176015391564849637)
                  ·
                    refine ⟨596302345502885918409307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180279176015391564849637 596302345502885918409307)
                    ·
                      rfl

theorem cell22_1741942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1741942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741942 prefixEnd_1741942 := by exact prefixLift 1741942
  have htrace : WordTrace (prefixWord ++ tailWord_1741942) baseStart_1741942 baseEnd_1741942 := by
    simpa [prefixWord, tailWord_1741942, baseEnd_1741942] using wordTrace_append hprefix tailTrace_1741942
  have hstable : (prefixWord ++ tailWord_1741942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741942).length < 2 ^ (prefixWord ++ tailWord_1741942).sum := by decide
  have hdescent : baseEnd_1741942 < baseStart_1741942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741944 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_1741944 : Nat := 118140960795 + 1741944 * 2 ^ 59
def prefixEnd_1741944 : Nat := 4983230072969 + 3 ^ 40 * 1741944 * 2
def baseEnd_1741944 : Nat := 596303030143758579859301

theorem tailTrace_1741944 : CollatzResearch.WordTrace tailWord_1741944 prefixEnd_1741944 596303030143758579859301 := by
  unfold tailWord_1741944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31766958600620931597548443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42355944800827908796731257 31766958600620931597548443)
  ·
    refine ⟨47650437900931397396322665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31766958600620931597548443 47650437900931397396322665)
    ·
      refine ⟨35737828425698548047241999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47650437900931397396322665 35737828425698548047241999)
      ·
        refine ⟨53606742638547822070862999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35737828425698548047241999 53606742638547822070862999)
        ·
          refine ⟨80410113957821733106294499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53606742638547822070862999 80410113957821733106294499)
          ·
            refine ⟨120615170936732599659441749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80410113957821733106294499 120615170936732599659441749)
            ·
              refine ⟨1413459034414835152259083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 120615170936732599659441749 1413459034414835152259083)
              ·
                refine ⟨2120188551622252728388625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413459034414835152259083 2120188551622252728388625)
                ·
                  refine ⟨1590141413716689546291469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120188551622252728388625 1590141413716689546291469)
                  ·
                    refine ⟨596303030143758579859301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590141413716689546291469 596303030143758579859301)
                    ·
                      rfl

theorem cell22_1741944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_1741944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741944 prefixEnd_1741944 := by exact prefixLift 1741944
  have htrace : WordTrace (prefixWord ++ tailWord_1741944) baseStart_1741944 baseEnd_1741944 := by
    simpa [prefixWord, tailWord_1741944, baseEnd_1741944] using wordTrace_append hprefix tailTrace_1741944
  have hstable : (prefixWord ++ tailWord_1741944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741944).length < 2 ^ (prefixWord ++ tailWord_1741944).sum := by decide
  have hdescent : baseEnd_1741944 < baseStart_1741944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741974 : List Nat := [5, 3, 2, 12]
def baseStart_1741974 : Nat := 118140960795 + 1741974 * 2 ^ 59
def prefixEnd_1741974 : Nat := 4983230072969 + 3 ^ 40 * 1741974 * 2
def baseEnd_1741974 : Nat := 817988065510080249121

theorem tailTrace_1741974 : CollatzResearch.WordTrace tailWord_1741974 prefixEnd_1741974 817988065510080249121 := by
  unfold tailWord_1741974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970938211945823644918061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42356674260755452212459317 3970938211945823644918061)
  ·
    refine ⟨1489101829479683866844273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3970938211945823644918061 1489101829479683866844273)
    ·
      refine ⟨1116826372109762900133205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489101829479683866844273 1116826372109762900133205)
      ·
        refine ⟨817988065510080249121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1116826372109762900133205 817988065510080249121)
        ·
          rfl

theorem cell22_1741974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 12].length) (baseStart_1741974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1741974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1741974 prefixEnd_1741974 := by exact prefixLift 1741974
  have htrace : WordTrace (prefixWord ++ tailWord_1741974) baseStart_1741974 baseEnd_1741974 := by
    simpa [prefixWord, tailWord_1741974, baseEnd_1741974] using wordTrace_append hprefix tailTrace_1741974
  have hstable : (prefixWord ++ tailWord_1741974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741974).length < 2 ^ (prefixWord ++ tailWord_1741974).sum := by decide
  have hdescent : baseEnd_1741974 < baseStart_1741974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742000 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1742000 : Nat := 118140960795 + 1742000 * 2 ^ 59
def prefixEnd_1742000 : Nat := 4983230072969 + 3 ^ 40 * 1742000 * 2
def baseEnd_1742000 : Nat := 596322200088193100459129

theorem tailTrace_1742000 : CollatzResearch.WordTrace tailWord_1742000 prefixEnd_1742000 596322200088193100459129 := by
  unfold tailWord_1742000
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767979844519492379567727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42357306459359323172756969 31767979844519492379567727)
  ·
    refine ⟨47651969766779238569351591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31767979844519492379567727 47651969766779238569351591)
    ·
      refine ⟨71477954650168857854027387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47651969766779238569351591 71477954650168857854027387)
      ·
        refine ⟨107216931975253286781041081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71477954650168857854027387 107216931975253286781041081)
        ·
          refine ⟨80412698981439965085780811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107216931975253286781041081 80412698981439965085780811)
          ·
            refine ⟨120619048472159947628671217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80412698981439965085780811 120619048472159947628671217)
            ·
              refine ⟨90464286354119960721503413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120619048472159947628671217 90464286354119960721503413)
              ·
                refine ⟨8481026845698746317640945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90464286354119960721503413 8481026845698746317640945)
                ·
                  refine ⟨6360770134274059738230709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481026845698746317640945 6360770134274059738230709)
                  ·
                    refine ⟨596322200088193100459129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6360770134274059738230709 596322200088193100459129)
                    ·
                      rfl

theorem cell22_1742000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1742000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742000 prefixEnd_1742000 := by exact prefixLift 1742000
  have htrace : WordTrace (prefixWord ++ tailWord_1742000) baseStart_1742000 baseEnd_1742000 := by
    simpa [prefixWord, tailWord_1742000, baseEnd_1742000] using wordTrace_append hprefix tailTrace_1742000
  have hstable : (prefixWord ++ tailWord_1742000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742000).length < 2 ^ (prefixWord ++ tailWord_1742000).sum := by decide
  have hdescent : baseEnd_1742000 < baseStart_1742000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742002 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1742002 : Nat := 118140960795 + 1742002 * 2 ^ 59
def prefixEnd_1742002 : Nat := 4983230072969 + 3 ^ 40 * 1742002 * 2
def baseEnd_1742002 : Nat := 198774294909688587303041

theorem tailTrace_1742002 : CollatzResearch.WordTrace tailWord_1742002 prefixEnd_1742002 198774294909688587303041 := by
  unfold tailWord_1742002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884008158757934775177065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42357355090021159400472173 15884008158757934775177065)
  ·
    refine ⟨11913006119068451081382799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15884008158757934775177065 11913006119068451081382799)
    ·
      refine ⟨17869509178602676622074199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913006119068451081382799 17869509178602676622074199)
      ·
        refine ⟨26804263767904014933111299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17869509178602676622074199 26804263767904014933111299)
        ·
          refine ⟨40206395651856022399666949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26804263767904014933111299 40206395651856022399666949)
          ·
            refine ⟨7538699184723004199937553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40206395651856022399666949 7538699184723004199937553)
            ·
              refine ⟨5654024388542253149953165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538699184723004199937553 5654024388542253149953165)
              ·
                refine ⟨2120259145703344931232437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5654024388542253149953165 2120259145703344931232437)
                ·
                  refine ⟨198774294909688587303041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2120259145703344931232437 198774294909688587303041)
                  ·
                    rfl

theorem cell22_1742002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1742002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742002 prefixEnd_1742002 := by exact prefixLift 1742002
  have htrace : WordTrace (prefixWord ++ tailWord_1742002) baseStart_1742002 baseEnd_1742002 := by
    simpa [prefixWord, tailWord_1742002, baseEnd_1742002] using wordTrace_append hprefix tailTrace_1742002
  have hstable : (prefixWord ++ tailWord_1742002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742002).length < 2 ^ (prefixWord ++ tailWord_1742002).sum := by decide
  have hdescent : baseEnd_1742002 < baseStart_1742002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742066 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1742066 : Nat := 118140960795 + 1742066 * 2 ^ 59
def prefixEnd_1742066 : Nat := 4983230072969 + 3 ^ 40 * 1742066 * 2
def baseEnd_1742066 : Nat := 596344793236990928308927

theorem tailTrace_1742066 : CollatzResearch.WordTrace tailWord_1742066 prefixEnd_1742066 596344793236990928308927 := by
  unfold tailWord_1742066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884591726699969507759513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42358911271199918687358701 15884591726699969507759513)
  ·
    refine ⟨11913443795024977130819635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15884591726699969507759513 11913443795024977130819635)
    ·
      refine ⟨17870165692537465696229453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913443795024977130819635 17870165692537465696229453)
      ·
        refine ⟨6701312134701549636086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17870165692537465696229453 6701312134701549636086045)
        ·
          refine ⟨2512992050513081113532267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6701312134701549636086045 2512992050513081113532267)
          ·
            refine ⟨3769488075769621670298401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512992050513081113532267 3769488075769621670298401)
            ·
              refine ⟨2827116056827216252723801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769488075769621670298401 2827116056827216252723801)
              ·
                refine ⟨2120337042620412189542851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827116056827216252723801 2120337042620412189542851)
                ·
                  refine ⟨3180505563930618284314277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120337042620412189542851 3180505563930618284314277)
                  ·
                    refine ⟨596344793236990928308927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180505563930618284314277 596344793236990928308927)
                    ·
                      rfl

theorem cell22_1742066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1742066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742066 prefixEnd_1742066 := by exact prefixLift 1742066
  have htrace : WordTrace (prefixWord ++ tailWord_1742066) baseStart_1742066 baseEnd_1742066 := by
    simpa [prefixWord, tailWord_1742066, baseEnd_1742066] using wordTrace_append hprefix tailTrace_1742066
  have hstable : (prefixWord ++ tailWord_1742066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742066).length < 2 ^ (prefixWord ++ tailWord_1742066).sum := by decide
  have hdescent : baseEnd_1742066 < baseStart_1742066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742081 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 4]
def baseStart_1742081 : Nat := 118140960795 + 1742081 * 2 ^ 59
def prefixEnd_1742081 : Nat := 4983230072969 + 3 ^ 40 * 1742081 * 2
def baseEnd_1742081 : Nat := 198783309347845296394627

theorem tailTrace_1742081 : CollatzResearch.WordTrace tailWord_1742081 prefixEnd_1742081 198783309347845296394627 := by
  unfold tailWord_1742081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63538914001745535592834097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42359276001163690395222731 63538914001745535592834097)
  ·
    refine ⟨47654185501309151694625573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63538914001745535592834097 47654185501309151694625573)
    ·
      refine ⟨8935159781495465942742295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47654185501309151694625573 8935159781495465942742295)
      ·
        refine ⟨13402739672243198914113443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935159781495465942742295 13402739672243198914113443)
        ·
          refine ⟨20104109508364798371170165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402739672243198914113443 20104109508364798371170165)
          ·
            refine ⟨1884760266409199847297203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20104109508364798371170165 1884760266409199847297203)
            ·
              refine ⟨2827140399613799770945805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884760266409199847297203 2827140399613799770945805)
              ·
                refine ⟨1060177649855174914104677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2827140399613799770945805 1060177649855174914104677)
                ·
                  refine ⟨198783309347845296394627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060177649855174914104677 198783309347845296394627)
                  ·
                    rfl

theorem cell22_1742081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_1742081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742081 prefixEnd_1742081 := by exact prefixLift 1742081
  have htrace : WordTrace (prefixWord ++ tailWord_1742081) baseStart_1742081 baseEnd_1742081 := by
    simpa [prefixWord, tailWord_1742081, baseEnd_1742081] using wordTrace_append hprefix tailTrace_1742081
  have hstable : (prefixWord ++ tailWord_1742081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742081).length < 2 ^ (prefixWord ++ tailWord_1742081).sum := by decide
  have hdescent : baseEnd_1742081 < baseStart_1742081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742092 : List Nat := [2, 2, 1, 2, 2, 5, 8]
def baseStart_1742092 : Nat := 118140960795 + 1742092 * 2 ^ 59
def prefixEnd_1742092 : Nat := 4983230072969 + 3 ^ 40 * 1742092 * 2
def baseEnd_1742092 : Nat := 22087173835864278783661

theorem tailTrace_1742092 : CollatzResearch.WordTrace tailWord_1742092 prefixEnd_1742092 22087173835864278783661 := by
  unfold tailWord_1742092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31769657602352842235742265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42359543469803789647656353 31769657602352842235742265)
  ·
    refine ⟨23827243201764631676806699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31769657602352842235742265 23827243201764631676806699)
    ·
      refine ⟨35740864802646947515210049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23827243201764631676806699 35740864802646947515210049)
      ·
        refine ⟨26805648601985210636407537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35740864802646947515210049 26805648601985210636407537)
        ·
          refine ⟨20104236451488907977305653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26805648601985210636407537 20104236451488907977305653)
          ·
            refine ⟨1884772167327085122872405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20104236451488907977305653 1884772167327085122872405)
            ·
              refine ⟨22087173835864278783661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1884772167327085122872405 22087173835864278783661)
              ·
                rfl

theorem cell22_1742092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 8].length) (baseStart_1742092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742092 prefixEnd_1742092 := by exact prefixLift 1742092
  have htrace : WordTrace (prefixWord ++ tailWord_1742092) baseStart_1742092 baseEnd_1742092 := by
    simpa [prefixWord, tailWord_1742092, baseEnd_1742092] using wordTrace_append hprefix tailTrace_1742092
  have hstable : (prefixWord ++ tailWord_1742092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742092).length < 2 ^ (prefixWord ++ tailWord_1742092).sum := by decide
  have hdescent : baseEnd_1742092 < baseStart_1742092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742094 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1742094 : Nat := 118140960795 + 1742094 * 2 ^ 59
def prefixEnd_1742094 : Nat := 4983230072969 + 3 ^ 40 * 1742094 * 2
def baseEnd_1742094 : Nat := 596354378209208188608841

theorem tailTrace_1742094 : CollatzResearch.WordTrace tailWord_1742094 prefixEnd_1742094 596354378209208188608841 := by
  unfold tailWord_1742094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942423518837304851632167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42359592100465625875371557 7942423518837304851632167)
  ·
    refine ⟨11913635278255957277448251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942423518837304851632167 11913635278255957277448251)
    ·
      refine ⟨17870452917383935916172377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913635278255957277448251 17870452917383935916172377)
      ·
        refine ⟨13402839688037951937129283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17870452917383935916172377 13402839688037951937129283)
        ·
          refine ⟨20104259532056927905693925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402839688037951937129283 20104259532056927905693925)
          ·
            refine ⟨3769548662260673982317611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20104259532056927905693925 3769548662260673982317611)
            ·
              refine ⟨5654322993391010973476417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769548662260673982317611 5654322993391010973476417)
              ·
                refine ⟨4240742245043258230107313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5654322993391010973476417 4240742245043258230107313)
                ·
                  refine ⟨3180556683782443672580485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240742245043258230107313 3180556683782443672580485)
                  ·
                    refine ⟨596354378209208188608841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180556683782443672580485 596354378209208188608841)
                    ·
                      rfl

theorem cell22_1742094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1742094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742094 prefixEnd_1742094 := by exact prefixLift 1742094
  have htrace : WordTrace (prefixWord ++ tailWord_1742094) baseStart_1742094 baseEnd_1742094 := by
    simpa [prefixWord, tailWord_1742094, baseEnd_1742094] using wordTrace_append hprefix tailTrace_1742094
  have hstable : (prefixWord ++ tailWord_1742094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742094).length < 2 ^ (prefixWord ++ tailWord_1742094).sum := by decide
  have hdescent : baseEnd_1742094 < baseStart_1742094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742098 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1742098 : Nat := 118140960795 + 1742098 * 2 ^ 59
def prefixEnd_1742098 : Nat := 4983230072969 + 3 ^ 40 * 1742098 * 2
def baseEnd_1742098 : Nat := 198785249163651170502943

theorem tailTrace_1742098 : CollatzResearch.WordTrace tailWord_1742098 prefixEnd_1742098 198785249163651170502943 := by
  unfold tailWord_1742098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884883510670986874050737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42359689361789298330801965 15884883510670986874050737)
  ·
    refine ⟨11913662633003240155538053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15884883510670986874050737 11913662633003240155538053)
    ·
      refine ⟨2233811743688107529163385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11913662633003240155538053 2233811743688107529163385)
      ·
        refine ⟨1675358807766080646872539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233811743688107529163385 1675358807766080646872539)
        ·
          refine ⟨2513038211649120970308809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675358807766080646872539 2513038211649120970308809)
          ·
            refine ⟨1884778658736840727731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513038211649120970308809 1884778658736840727731607)
            ·
              refine ⟨2827167988105261091597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884778658736840727731607 2827167988105261091597411)
              ·
                refine ⟨4240751982157891637396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827167988105261091597411 4240751982157891637396117)
                ·
                  refine ⟨198785249163651170502943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4240751982157891637396117 198785249163651170502943)
                  ·
                    rfl

theorem cell22_1742098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1742098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742098 prefixEnd_1742098 := by exact prefixLift 1742098
  have htrace : WordTrace (prefixWord ++ tailWord_1742098) baseStart_1742098 baseEnd_1742098 := by
    simpa [prefixWord, tailWord_1742098, baseEnd_1742098] using wordTrace_append hprefix tailTrace_1742098
  have hstable : (prefixWord ++ tailWord_1742098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742098).length < 2 ^ (prefixWord ++ tailWord_1742098).sum := by decide
  have hdescent : baseEnd_1742098 < baseStart_1742098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742109 : List Nat := [1, 4, 2, 3, 1, 2, 2, 7]
def baseStart_1742109 : Nat := 118140960795 + 1742109 * 2 ^ 59
def prefixEnd_1742109 : Nat := 4983230072969 + 3 ^ 40 * 1742109 * 2
def baseEnd_1742109 : Nat := 66262168112861461053755

theorem tailTrace_1742109 : CollatzResearch.WordTrace tailWord_1742109 prefixEnd_1742109 66262168112861461053755 := by
  unfold tailWord_1742109
  simp only [CollatzResearch.WordTrace]
  refine ⟨63539935245644096374853381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42359956830429397583235587 63539935245644096374853381)
  ·
    refine ⟨11913737858558268070285009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63539935245644096374853381 11913737858558268070285009)
    ·
      refine ⟨8935303393918701052713757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11913737858558268070285009 8935303393918701052713757)
      ·
        refine ⟨3350738772719512894767659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8935303393918701052713757 3350738772719512894767659)
        ·
          refine ⟨5026108159079269342151489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350738772719512894767659 5026108159079269342151489)
          ·
            refine ⟨3769581119309452006613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026108159079269342151489 3769581119309452006613617)
            ·
              refine ⟨2827185839482089004960213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769581119309452006613617 2827185839482089004960213)
              ·
                refine ⟨66262168112861461053755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2827185839482089004960213 66262168112861461053755)
                ·
                  rfl

theorem cell22_1742109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 7].length) (baseStart_1742109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742109 prefixEnd_1742109 := by exact prefixLift 1742109
  have htrace : WordTrace (prefixWord ++ tailWord_1742109) baseStart_1742109 baseEnd_1742109 := by
    simpa [prefixWord, tailWord_1742109, baseEnd_1742109] using wordTrace_append hprefix tailTrace_1742109
  have hstable : (prefixWord ++ tailWord_1742109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742109).length < 2 ^ (prefixWord ++ tailWord_1742109).sum := by decide
  have hdescent : baseEnd_1742109 < baseStart_1742109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742152 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1742152 : Nat := 118140960795 + 1742152 * 2 ^ 59
def prefixEnd_1742152 : Nat := 4983230072969 + 3 ^ 40 * 1742152 * 2
def baseEnd_1742152 : Nat := 596374232794515370658663

theorem tailTrace_1742152 : CollatzResearch.WordTrace tailWord_1742152 prefixEnd_1742152 596374232794515370658663 := by
  unfold tailWord_1742152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770751792244157359334355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42361002389658876479112473 31770751792244157359334355)
  ·
    refine ⟨47656127688366236039001533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31770751792244157359334355 47656127688366236039001533)
    ·
      refine ⟨17871047883137338514625575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47656127688366236039001533 17871047883137338514625575)
      ·
        refine ⟨26806571824706007771938363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871047883137338514625575 26806571824706007771938363)
        ·
          refine ⟨40209857737059011657907545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26806571824706007771938363 40209857737059011657907545)
          ·
            refine ⟨30157393302794258743430659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40209857737059011657907545 30157393302794258743430659)
            ·
              refine ⟨45236089954191388115145989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30157393302794258743430659 45236089954191388115145989)
              ·
                refine ⟨8481766866410885271589873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45236089954191388115145989 8481766866410885271589873)
                ·
                  refine ⟨6361325149808163953692405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481766866410885271589873 6361325149808163953692405)
                  ·
                    refine ⟨596374232794515370658663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6361325149808163953692405 596374232794515370658663)
                    ·
                      rfl

theorem cell22_1742152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1742152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742152 prefixEnd_1742152 := by exact prefixLift 1742152
  have htrace : WordTrace (prefixWord ++ tailWord_1742152) baseStart_1742152 baseEnd_1742152 := by
    simpa [prefixWord, tailWord_1742152, baseEnd_1742152] using wordTrace_append hprefix tailTrace_1742152
  have hstable : (prefixWord ++ tailWord_1742152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742152).length < 2 ^ (prefixWord ++ tailWord_1742152).sum := by decide
  have hdescent : baseEnd_1742152 < baseStart_1742152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742201 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_1742201 : Nat := 118140960795 + 1742201 * 2 ^ 59
def prefixEnd_1742201 : Nat := 4983230072969 + 3 ^ 40 * 1742201 * 2
def baseEnd_1742201 : Nat := 596391006495895576183513

theorem tailTrace_1742201 : CollatzResearch.WordTrace tailWord_1742201 prefixEnd_1742201 596391006495895576183513 := by
  unfold tailWord_1742201
  simp only [CollatzResearch.WordTrace]
  refine ⟨63543290761310796087202457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42362193840873864058134971 63543290761310796087202457)
  ·
    refine ⟨47657468070983097065401843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63543290761310796087202457 47657468070983097065401843)
    ·
      refine ⟨71486202106474645598102765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47657468070983097065401843 71486202106474645598102765)
      ·
        refine ⟨26807325789927992099288537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71486202106474645598102765 26807325789927992099288537)
        ·
          refine ⟨20105494342445994074466403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26807325789927992099288537 20105494342445994074466403)
          ·
            refine ⟨30158241513668991111699605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20105494342445994074466403 30158241513668991111699605)
            ·
              refine ⟨1413667570953233958360919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30158241513668991111699605 1413667570953233958360919)
              ·
                refine ⟨2120501356429850937541379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413667570953233958360919 2120501356429850937541379)
                ·
                  refine ⟨3180752034644776406312069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120501356429850937541379 3180752034644776406312069)
                  ·
                    refine ⟨596391006495895576183513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3180752034644776406312069 596391006495895576183513)
                    ·
                      rfl

theorem cell22_1742201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_1742201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742201 prefixEnd_1742201 := by exact prefixLift 1742201
  have htrace : WordTrace (prefixWord ++ tailWord_1742201) baseStart_1742201 baseEnd_1742201 := by
    simpa [prefixWord, tailWord_1742201, baseEnd_1742201] using wordTrace_append hprefix tailTrace_1742201
  have hstable : (prefixWord ++ tailWord_1742201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742201).length < 2 ^ (prefixWord ++ tailWord_1742201).sum := by decide
  have hdescent : baseEnd_1742201 < baseStart_1742201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742216 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_1742216 : Nat := 118140960795 + 1742216 * 2 ^ 59
def prefixEnd_1742216 : Nat := 4983230072969 + 3 ^ 40 * 1742216 * 2
def baseEnd_1742216 : Nat := 198798713767480179019489

theorem tailTrace_1742216 : CollatzResearch.WordTrace tailWord_1742216 prefixEnd_1742216 198798713767480179019489 := by
  unfold tailWord_1742216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771918928128226824499251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42362558570837635765999001 31771918928128226824499251)
  ·
    refine ⟨47657878392192340236748877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31771918928128226824499251 47657878392192340236748877)
    ·
      refine ⟨17871704397072127588780829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47657878392192340236748877 17871704397072127588780829)
      ·
        refine ⟨6701889148902047845792811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17871704397072127588780829 6701889148902047845792811)
        ·
          refine ⟨10052833723353071768689217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701889148902047845792811 10052833723353071768689217)
          ·
            refine ⟨7539625292514803826516913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10052833723353071768689217 7539625292514803826516913)
            ·
              refine ⟨5654718969386102869887685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7539625292514803826516913 5654718969386102869887685)
              ·
                refine ⟨1060259806759894288103941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5654718969386102869887685 1060259806759894288103941)
                ·
                  refine ⟨198798713767480179019489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060259806759894288103941 198798713767480179019489)
                  ·
                    rfl

theorem cell22_1742216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_1742216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742216 prefixEnd_1742216 := by exact prefixLift 1742216
  have htrace : WordTrace (prefixWord ++ tailWord_1742216) baseStart_1742216 baseEnd_1742216 := by
    simpa [prefixWord, tailWord_1742216, baseEnd_1742216] using wordTrace_append hprefix tailTrace_1742216
  have hstable : (prefixWord ++ tailWord_1742216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742216).length < 2 ^ (prefixWord ++ tailWord_1742216).sum := by decide
  have hdescent : baseEnd_1742216 < baseStart_1742216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742259 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 5, 3]
def baseStart_1742259 : Nat := 118140960795 + 1742259 * 2 ^ 59
def prefixEnd_1742259 : Nat := 4983230072969 + 3 ^ 40 * 1742259 * 2
def baseEnd_1742259 : Nat := 596410861081202758233335

theorem tailTrace_1742259 : CollatzResearch.WordTrace tailWord_1742259 prefixEnd_1742259 596410861081202758233335 := by
  unfold tailWord_1742259
  simp only [CollatzResearch.WordTrace]
  refine ⟨63545406195100671992813831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42363604130067114661875887 63545406195100671992813831)
  ·
    refine ⟨95318109292651007989220747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63545406195100671992813831 95318109292651007989220747)
    ·
      refine ⟨142977163938976511983831121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95318109292651007989220747 142977163938976511983831121)
      ·
        refine ⟨107232872954232383987873341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142977163938976511983831121 107232872954232383987873341)
        ·
          refine ⟨40212327357837143995452503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107232872954232383987873341 40212327357837143995452503)
          ·
            refine ⟨60318491036755715993178755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40212327357837143995452503 60318491036755715993178755)
            ·
              refine ⟨90477736555133573989768133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60318491036755715993178755 90477736555133573989768133)
              ·
                refine ⟨16964575604087545123081525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90477736555133573989768133 16964575604087545123081525)
                ·
                  refine ⟨1590428962883207355288893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16964575604087545123081525 1590428962883207355288893)
                  ·
                    refine ⟨596410861081202758233335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590428962883207355288893 596410861081202758233335)
                    ·
                      rfl

theorem cell22_1742259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].length) (baseStart_1742259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742259 prefixEnd_1742259 := by exact prefixLift 1742259
  have htrace : WordTrace (prefixWord ++ tailWord_1742259) baseStart_1742259 baseEnd_1742259 := by
    simpa [prefixWord, tailWord_1742259, baseEnd_1742259] using wordTrace_append hprefix tailTrace_1742259
  have hstable : (prefixWord ++ tailWord_1742259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742259).length < 2 ^ (prefixWord ++ tailWord_1742259).sum := by decide
  have hdescent : baseEnd_1742259 < baseStart_1742259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742338 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1742338 : Nat := 118140960795 + 1742338 * 2 ^ 59
def prefixEnd_1742338 : Nat := 4983230072969 + 3 ^ 40 * 1742338 * 2
def baseEnd_1742338 : Nat := 596437904395672885508093

theorem tailTrace_1742338 : CollatzResearch.WordTrace tailWord_1742338 prefixEnd_1742338 596437904395672885508093 := by
  unfold tailWord_1742338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15887071890453617121234917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42365525041209645656626445 15887071890453617121234917)
  ·
    refine ⟨2978825979460053210231547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15887071890453617121234917 2978825979460053210231547)
    ·
      refine ⟨4468238969190079815347321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978825979460053210231547 4468238969190079815347321)
      ·
        refine ⟨3351179226892559861510491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4468238969190079815347321 3351179226892559861510491)
        ·
          refine ⟨5026768840338839792265737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351179226892559861510491 5026768840338839792265737)
          ·
            refine ⟨3770076630254129844199303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026768840338839792265737 3770076630254129844199303)
            ·
              refine ⟨5655114945381194766298955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770076630254129844199303 5655114945381194766298955)
              ·
                refine ⟨8482672418071792149448433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655114945381194766298955 8482672418071792149448433)
                ·
                  refine ⟨6362004313553844112086325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8482672418071792149448433 6362004313553844112086325)
                  ·
                    refine ⟨596437904395672885508093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6362004313553844112086325 596437904395672885508093)
                    ·
                      rfl

theorem cell22_1742338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1742338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742338 prefixEnd_1742338 := by exact prefixLift 1742338
  have htrace : WordTrace (prefixWord ++ tailWord_1742338) baseStart_1742338 baseEnd_1742338 := by
    simpa [prefixWord, tailWord_1742338, baseEnd_1742338] using wordTrace_append hprefix tailTrace_1742338
  have hstable : (prefixWord ++ tailWord_1742338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742338).length < 2 ^ (prefixWord ++ tailWord_1742338).sum := by decide
  have hdescent : baseEnd_1742338 < baseStart_1742338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742368 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_1742368 : Nat := 118140960795 + 1742368 * 2 ^ 59
def prefixEnd_1742368 : Nat := 4983230072969 + 3 ^ 40 * 1742368 * 2
def baseEnd_1742368 : Nat := 198816058002920935752667

theorem tailTrace_1742368 : CollatzResearch.WordTrace tailWord_1742368 prefixEnd_1742368 198816058002920935752667 := by
  unfold tailWord_1742368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774690875852891804265879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42366254501137189072354505 31774690875852891804265879)
  ·
    refine ⟨47662036313779337706398819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31774690875852891804265879 47662036313779337706398819)
    ·
      refine ⟨71493054470669006559598229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47662036313779337706398819 71493054470669006559598229)
      ·
        refine ⟨3351236928312609682481167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71493054470669006559598229 3351236928312609682481167)
        ·
          refine ⟨5026855392468914523721751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351236928312609682481167 5026855392468914523721751)
          ·
            refine ⟨7540283088703371785582627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026855392468914523721751 7540283088703371785582627)
            ·
              refine ⟨11310424633055057678373941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540283088703371785582627 11310424633055057678373941)
              ·
                refine ⟨1060352309348911657347557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11310424633055057678373941 1060352309348911657347557)
                ·
                  refine ⟨198816058002920935752667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060352309348911657347557 198816058002920935752667)
                  ·
                    rfl

theorem cell22_1742368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_1742368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742368 prefixEnd_1742368 := by exact prefixLift 1742368
  have htrace : WordTrace (prefixWord ++ tailWord_1742368) baseStart_1742368 baseEnd_1742368 := by
    simpa [prefixWord, tailWord_1742368, baseEnd_1742368] using wordTrace_append hprefix tailTrace_1742368
  have hstable : (prefixWord ++ tailWord_1742368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742368).length < 2 ^ (prefixWord ++ tailWord_1742368).sum := by decide
  have hdescent : baseEnd_1742368 < baseStart_1742368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742409 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1742409 : Nat := 118140960795 + 1742409 * 2 ^ 59
def prefixEnd_1742409 : Nat := 4983230072969 + 3 ^ 40 * 1742409 * 2
def baseEnd_1742409 : Nat := 596462209146652366982875

theorem tailTrace_1742409 : CollatzResearch.WordTrace tailWord_1742409 prefixEnd_1742409 596462209146652366982875 := by
  unfold tailWord_1742409
  simp only [CollatzResearch.WordTrace]
  refine ⟨63550877144557247610774281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42367251429704831740516187 63550877144557247610774281)
  ·
    refine ⟨47663157858417935708080711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63550877144557247610774281 47663157858417935708080711)
    ·
      refine ⟨71494736787626903562121067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47663157858417935708080711 71494736787626903562121067)
      ·
        refine ⟨107242105181440355343181601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71494736787626903562121067 107242105181440355343181601)
        ·
          refine ⟨80431578886080266507386201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107242105181440355343181601 80431578886080266507386201)
          ·
            refine ⟨60323684164560199880539651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80431578886080266507386201 60323684164560199880539651)
            ·
              refine ⟨90485526246840299820809477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60323684164560199880539651 90485526246840299820809477)
              ·
                refine ⟨16966036171282556216401777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90485526246840299820809477 16966036171282556216401777)
                ·
                  refine ⟨12724527128461917162301333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16966036171282556216401777 12724527128461917162301333)
                  ·
                    refine ⟨596462209146652366982875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12724527128461917162301333 596462209146652366982875)
                    ·
                      rfl

theorem cell22_1742409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1742409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742409 prefixEnd_1742409 := by exact prefixLift 1742409
  have htrace : WordTrace (prefixWord ++ tailWord_1742409) baseStart_1742409 baseEnd_1742409 := by
    simpa [prefixWord, tailWord_1742409, baseEnd_1742409] using wordTrace_append hprefix tailTrace_1742409
  have hstable : (prefixWord ++ tailWord_1742409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742409).length < 2 ^ (prefixWord ++ tailWord_1742409).sum := by decide
  have hdescent : baseEnd_1742409 < baseStart_1742409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742413 : List Nat := [1, 6, 1, 1, 3, 1, 1, 8]
def baseStart_1742413 : Nat := 118140960795 + 1742413 * 2 ^ 59
def prefixEnd_1742413 : Nat := 4983230072969 + 3 ^ 40 * 1742413 * 2
def baseEnd_1742413 : Nat := 66273730936488632209207

theorem tailTrace_1742413 : CollatzResearch.WordTrace tailWord_1742413 prefixEnd_1742413 66273730936488632209207 := by
  unfold tailWord_1742413
  simp only [CollatzResearch.WordTrace]
  refine ⟨63551023036542756293919893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42367348691028504195946595 63551023036542756293919893)
  ·
    refine ⟨2978954204837941701277495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63551023036542756293919893 2978954204837941701277495)
    ·
      refine ⟨4468431307256912551916243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978954204837941701277495 4468431307256912551916243)
      ·
        refine ⟨6702646960885368827874365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468431307256912551916243 6702646960885368827874365)
        ·
          refine ⟨2513492610332013310452887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6702646960885368827874365 2513492610332013310452887)
          ·
            refine ⟨3770238915498019965679331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513492610332013310452887 3770238915498019965679331)
            ·
              refine ⟨5655358373247029948518997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770238915498019965679331 5655358373247029948518997)
              ·
                refine ⟨66273730936488632209207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5655358373247029948518997 66273730936488632209207)
                ·
                  rfl

theorem cell22_1742413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 8].length) (baseStart_1742413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742413 prefixEnd_1742413 := by exact prefixLift 1742413
  have htrace : WordTrace (prefixWord ++ tailWord_1742413) baseStart_1742413 baseEnd_1742413 := by
    simpa [prefixWord, tailWord_1742413, baseEnd_1742413] using wordTrace_append hprefix tailTrace_1742413
  have hstable : (prefixWord ++ tailWord_1742413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742413).length < 2 ^ (prefixWord ++ tailWord_1742413).sum := by decide
  have hdescent : baseEnd_1742413 < baseStart_1742413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742548 : List Nat := [2, 4, 1, 3, 1, 2, 9]
def baseStart_1742548 : Nat := 118140960795 + 1742548 * 2 ^ 59
def prefixEnd_1742548 : Nat := 4983230072969 + 3 ^ 40 * 1742548 * 2
def baseEnd_1742548 : Nat := 22092955247677864361387

theorem tailTrace_1742548 : CollatzResearch.WordTrace tailWord_1742548 prefixEnd_1742548 22092955247677864361387 := by
  unfold tailWord_1742548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777973445526837175042149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42370631260702449566722865 31777973445526837175042149)
  ·
    refine ⟨5958370021036281970320403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31777973445526837175042149 5958370021036281970320403)
    ·
      refine ⟨8937555031554422955480605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958370021036281970320403 8937555031554422955480605)
      ·
        refine ⟨3351583136832908608305227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8937555031554422955480605 3351583136832908608305227)
        ·
          refine ⟨5027374705249362912457841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351583136832908608305227 5027374705249362912457841)
          ·
            refine ⟨3770531028937022184343381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5027374705249362912457841 3770531028937022184343381)
            ·
              refine ⟨22092955247677864361387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3770531028937022184343381 22092955247677864361387)
              ·
                rfl

theorem cell22_1742548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 9].length) (baseStart_1742548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742548 prefixEnd_1742548 := by exact prefixLift 1742548
  have htrace : WordTrace (prefixWord ++ tailWord_1742548) baseStart_1742548 baseEnd_1742548 := by
    simpa [prefixWord, tailWord_1742548, baseEnd_1742548] using wordTrace_append hprefix tailTrace_1742548
  have hstable : (prefixWord ++ tailWord_1742548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742548).length < 2 ^ (prefixWord ++ tailWord_1742548).sum := by decide
  have hdescent : baseEnd_1742548 < baseStart_1742548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742591 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1742591 : Nat := 118140960795 + 1742591 * 2 ^ 59
def prefixEnd_1742591 : Nat := 4983230072969 + 3 ^ 40 * 1742591 * 2
def baseEnd_1742591 : Nat := 596524511466064558932317

theorem tailTrace_1742591 : CollatzResearch.WordTrace tailWord_1742591 prefixEnd_1742591 596524511466064558932317 := by
  unfold tailWord_1742591
  simp only [CollatzResearch.WordTrace]
  refine ⟨63557515229897892693899627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42371676819931928462599751 63557515229897892693899627)
  ·
    refine ⟨95336272844846839040849441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63557515229897892693899627 95336272844846839040849441)
    ·
      refine ⟨71502204633635129280637081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95336272844846839040849441 71502204633635129280637081)
      ·
        refine ⟨53626653475226346960477811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71502204633635129280637081 53626653475226346960477811)
        ·
          refine ⟨80439980212839520440716717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53626653475226346960477811 80439980212839520440716717)
          ·
            refine ⟨30164992579814820165268769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80439980212839520440716717 30164992579814820165268769)
            ·
              refine ⟨22623744434861115123951577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30164992579814820165268769 22623744434861115123951577)
              ·
                refine ⟨16967808326145836342963683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22623744434861115123951577 16967808326145836342963683)
                ·
                  refine ⟨25451712489218754514445525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16967808326145836342963683 25451712489218754514445525)
                  ·
                    refine ⟨596524511466064558932317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25451712489218754514445525 596524511466064558932317)
                    ·
                      rfl

theorem cell22_1742591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1742591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742591 prefixEnd_1742591 := by exact prefixLift 1742591
  have htrace : WordTrace (prefixWord ++ tailWord_1742591) baseStart_1742591 baseEnd_1742591 := by
    simpa [prefixWord, tailWord_1742591, baseEnd_1742591] using wordTrace_append hprefix tailTrace_1742591
  have hstable : (prefixWord ++ tailWord_1742591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742591).length < 2 ^ (prefixWord ++ tailWord_1742591).sum := by decide
  have hdescent : baseEnd_1742591 < baseStart_1742591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742610 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1742610 : Nat := 118140960795 + 1742610 * 2 ^ 59
def prefixEnd_1742610 : Nat := 4983230072969 + 3 ^ 40 * 1742610 * 2
def baseEnd_1742610 : Nat := 198843671851451614235753

theorem tailTrace_1742610 : CollatzResearch.WordTrace tailWord_1742610 prefixEnd_1742610 198843671851451614235753 := by
  unfold tailWord_1742610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15889552054207264734710321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42372138811219372625894189 15889552054207264734710321)
  ·
    refine ⟨11917164040655448551032741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15889552054207264734710321 11917164040655448551032741)
    ·
      refine ⟨2234468257622896603318639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11917164040655448551032741 2234468257622896603318639)
      ·
        refine ⟨3351702386434344904977959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234468257622896603318639 3351702386434344904977959)
        ·
          refine ⟨5027553579651517357466939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351702386434344904977959 5027553579651517357466939)
          ·
            refine ⟨7541330369477276036200409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027553579651517357466939 7541330369477276036200409)
            ·
              refine ⟨5655997777107957027150307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7541330369477276036200409 5655997777107957027150307)
              ·
                refine ⟨8483996665661935540725461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655997777107957027150307 8483996665661935540725461)
                ·
                  refine ⟨198843671851451614235753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8483996665661935540725461 198843671851451614235753)
                  ·
                    rfl

theorem cell22_1742610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1742610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742610 prefixEnd_1742610 := by exact prefixLift 1742610
  have htrace : WordTrace (prefixWord ++ tailWord_1742610) baseStart_1742610 baseEnd_1742610 := by
    simpa [prefixWord, tailWord_1742610, baseEnd_1742610] using wordTrace_append hprefix tailTrace_1742610
  have hstable : (prefixWord ++ tailWord_1742610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742610).length < 2 ^ (prefixWord ++ tailWord_1742610).sum := by decide
  have hdescent : baseEnd_1742610 < baseStart_1742610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742623 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1742623 : Nat := 118140960795 + 1742623 * 2 ^ 59
def prefixEnd_1742623 : Nat := 4983230072969 + 3 ^ 40 * 1742623 * 2
def baseEnd_1742623 : Nat := 596535465720027142132219

theorem tailTrace_1742623 : CollatzResearch.WordTrace tailWord_1742623 prefixEnd_1742623 596535465720027142132219 := by
  unfold tailWord_1742623
  simp only [CollatzResearch.WordTrace]
  refine ⟨63558682365781962159064523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42372454910521308106043015 63558682365781962159064523)
  ·
    refine ⟨95338023548672943238596785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63558682365781962159064523 95338023548672943238596785)
    ·
      refine ⟨71503517661504707428947589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95338023548672943238596785 71503517661504707428947589)
      ·
        refine ⟨13406909561532132642927673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71503517661504707428947589 13406909561532132642927673)
        ·
          refine ⟨10055182171149099482195755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13406909561532132642927673 10055182171149099482195755)
          ·
            refine ⟨15082773256723649223293633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055182171149099482195755 15082773256723649223293633)
            ·
              refine ⟨11312079942542736917470225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15082773256723649223293633 11312079942542736917470225)
              ·
                refine ⟨8484059956907052688102669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312079942542736917470225 8484059956907052688102669)
                ·
                  refine ⟨3181522483840144758038501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8484059956907052688102669 3181522483840144758038501)
                  ·
                    refine ⟨596535465720027142132219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181522483840144758038501 596535465720027142132219)
                    ·
                      rfl

theorem cell22_1742623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1742623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742623 prefixEnd_1742623 := by exact prefixLift 1742623
  have htrace : WordTrace (prefixWord ++ tailWord_1742623) baseStart_1742623 baseEnd_1742623 := by
    simpa [prefixWord, tailWord_1742623, baseEnd_1742623] using wordTrace_append hprefix tailTrace_1742623
  have hstable : (prefixWord ++ tailWord_1742623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742623).length < 2 ^ (prefixWord ++ tailWord_1742623).sum := by decide
  have hdescent : baseEnd_1742623 < baseStart_1742623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742700 : List Nat := [2, 2, 1, 1, 4, 3, 3, 6]
def baseStart_1742700 : Nat := 118140960795 + 1742700 * 2 ^ 59
def prefixEnd_1742700 : Nat := 4983230072969 + 3 ^ 40 * 1742700 * 2
def baseEnd_1742700 : Nat := 66284647154847178661887

theorem tailTrace_1742700 : CollatzResearch.WordTrace tailWord_1742700 prefixEnd_1742700 66284647154847178661887 := by
  unfold tailWord_1742700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780745393251502154808777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42374327191002002873078369 31780745393251502154808777)
  ·
    refine ⟨23835559044938626616106583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31780745393251502154808777 23835559044938626616106583)
    ·
      refine ⟨35753338567407939924159875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23835559044938626616106583 35753338567407939924159875)
      ·
        refine ⟨53630007851111909886239813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35753338567407939924159875 53630007851111909886239813)
        ·
          refine ⟨10055626472083483103669965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53630007851111909886239813 10055626472083483103669965)
          ·
            refine ⟨3770859927031306163876237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10055626472083483103669965 3770859927031306163876237)
            ·
              refine ⟨1414072472636739811453589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3770859927031306163876237 1414072472636739811453589)
              ·
                refine ⟨66284647154847178661887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1414072472636739811453589 66284647154847178661887)
                ·
                  rfl

theorem cell22_1742700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_1742700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742700 prefixEnd_1742700 := by exact prefixLift 1742700
  have htrace : WordTrace (prefixWord ++ tailWord_1742700) baseStart_1742700 baseEnd_1742700 := by
    simpa [prefixWord, tailWord_1742700, baseEnd_1742700] using wordTrace_append hprefix tailTrace_1742700
  have hstable : (prefixWord ++ tailWord_1742700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742700).length < 2 ^ (prefixWord ++ tailWord_1742700).sum := by decide
  have hdescent : baseEnd_1742700 < baseStart_1742700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742702 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1742702 : Nat := 118140960795 + 1742702 * 2 ^ 59
def prefixEnd_1742702 : Nat := 4983230072969 + 3 ^ 40 * 1742702 * 2
def baseEnd_1742702 : Nat := 596562509034497269406977

theorem tailTrace_1742702 : CollatzResearch.WordTrace tailWord_1742702 prefixEnd_1742702 596562509034497269406977 := by
  unfold tailWord_1742702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945195466561969831398795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42374375821663839100793573 7945195466561969831398795)
  ·
    refine ⟨11917793199842954747098193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7945195466561969831398795 11917793199842954747098193)
    ·
      refine ⟨8938344899882216060323645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11917793199842954747098193 8938344899882216060323645)
      ·
        refine ⟨3351879337455831022621367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8938344899882216060323645 3351879337455831022621367)
        ·
          refine ⟨5027819006183746533932051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3351879337455831022621367 5027819006183746533932051)
          ·
            refine ⟨7541728509275619800898077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5027819006183746533932051 7541728509275619800898077)
            ·
              refine ⟨2828148190978357425336779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7541728509275619800898077 2828148190978357425336779)
              ·
                refine ⟨4242222286467536138005169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828148190978357425336779 4242222286467536138005169)
                ·
                  refine ⟨3181666714850652103503877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242222286467536138005169 3181666714850652103503877)
                  ·
                    refine ⟨596562509034497269406977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181666714850652103503877 596562509034497269406977)
                    ·
                      rfl

theorem cell22_1742702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1742702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742702 prefixEnd_1742702 := by exact prefixLift 1742702
  have htrace : WordTrace (prefixWord ++ tailWord_1742702) baseStart_1742702 baseEnd_1742702 := by
    simpa [prefixWord, tailWord_1742702, baseEnd_1742702] using wordTrace_append hprefix tailTrace_1742702
  have hstable : (prefixWord ++ tailWord_1742702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742702).length < 2 ^ (prefixWord ++ tailWord_1742702).sum := by decide
  have hdescent : baseEnd_1742702 < baseStart_1742702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742721 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1742721 : Nat := 118140960795 + 1742721 * 2 ^ 59
def prefixEnd_1742721 : Nat := 4983230072969 + 3 ^ 40 * 1742721 * 2
def baseEnd_1742721 : Nat := 596569013122787553181919

theorem tailTrace_1742721 : CollatzResearch.WordTrace tailWord_1742721 prefixEnd_1742721 596569013122787553181919 := by
  unfold tailWord_1742721
  simp only [CollatzResearch.WordTrace]
  refine ⟨63562256719426924896132017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42374837812951283264088011 63562256719426924896132017)
  ·
    refine ⟨47671692539570193672099013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63562256719426924896132017 47671692539570193672099013)
    ·
      refine ⟨8938442351169411313518565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47671692539570193672099013 8938442351169411313518565)
      ·
        refine ⟨1675957940844264621284731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8938442351169411313518565 1675957940844264621284731)
        ·
          refine ⟨2513936911266396931927097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675957940844264621284731 2513936911266396931927097)
          ·
            refine ⟨1885452683449797698945323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513936911266396931927097 1885452683449797698945323)
            ·
              refine ⟨2828179025174696548417985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885452683449797698945323 2828179025174696548417985)
              ·
                refine ⟨2121134268881022411313489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828179025174696548417985 2121134268881022411313489)
                ·
                  refine ⟨1590850701660766808485117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2121134268881022411313489 1590850701660766808485117)
                  ·
                    refine ⟨596569013122787553181919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1590850701660766808485117 596569013122787553181919)
                    ·
                      rfl

theorem cell22_1742721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1742721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742721 prefixEnd_1742721 := by exact prefixLift 1742721
  have htrace : WordTrace (prefixWord ++ tailWord_1742721) baseStart_1742721 baseEnd_1742721 := by
    simpa [prefixWord, tailWord_1742721, baseEnd_1742721] using wordTrace_append hprefix tailTrace_1742721
  have hstable : (prefixWord ++ tailWord_1742721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742721).length < 2 ^ (prefixWord ++ tailWord_1742721).sum := by decide
  have hdescent : baseEnd_1742721 < baseStart_1742721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742809 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_1742809 : Nat := 118140960795 + 1742809 * 2 ^ 59
def prefixEnd_1742809 : Nat := 4983230072969 + 3 ^ 40 * 1742809 * 2
def baseEnd_1742809 : Nat := 596599137321184656981649

theorem tailTrace_1742809 : CollatzResearch.WordTrace tailWord_1742809 prefixEnd_1742809 596599137321184656981649 := by
  unfold tailWord_1742809
  simp only [CollatzResearch.WordTrace]
  refine ⟨63565466343108115925335481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42376977562072077283556987 63565466343108115925335481)
  ·
    refine ⟨47674099757331086944001611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63565466343108115925335481 47674099757331086944001611)
    ·
      refine ⟨71511149635996630416002417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47674099757331086944001611 71511149635996630416002417)
      ·
        refine ⟨53633362226997472812001813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71511149635996630416002417 53633362226997472812001813)
        ·
          refine ⟨2514063854390506538062585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53633362226997472812001813 2514063854390506538062585)
          ·
            refine ⟨1885547890792879903546939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514063854390506538062585 1885547890792879903546939)
            ·
              refine ⟨2828321836189319855320409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885547890792879903546939 2828321836189319855320409)
              ·
                refine ⟨2121241377141989891490307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828321836189319855320409 2121241377141989891490307)
                ·
                  refine ⟨3181862065712984837235461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121241377141989891490307 3181862065712984837235461)
                  ·
                    refine ⟨596599137321184656981649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181862065712984837235461 596599137321184656981649)
                    ·
                      rfl

theorem cell22_1742809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_1742809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742809 prefixEnd_1742809 := by exact prefixLift 1742809
  have htrace : WordTrace (prefixWord ++ tailWord_1742809) baseStart_1742809 baseEnd_1742809 := by
    simpa [prefixWord, tailWord_1742809, baseEnd_1742809] using wordTrace_append hprefix tailTrace_1742809
  have hstable : (prefixWord ++ tailWord_1742809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742809).length < 2 ^ (prefixWord ++ tailWord_1742809).sum := by decide
  have hdescent : baseEnd_1742809 < baseStart_1742809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742871 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 2, 4]
def baseStart_1742871 : Nat := 118140960795 + 1742871 * 2 ^ 59
def prefixEnd_1742871 : Nat := 4983230072969 + 3 ^ 40 * 1742871 * 2
def baseEnd_1742871 : Nat := 596620361188237161931459

theorem tailTrace_1742871 : CollatzResearch.WordTrace tailWord_1742871 prefixEnd_1742871 596620361188237161931459 := by
  unfold tailWord_1742871
  simp only [CollatzResearch.WordTrace]
  refine ⟨63567727668883500514092467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42378485112589000342728311 63567727668883500514092467)
  ·
    refine ⟨95351591503325250771138701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63567727668883500514092467 95351591503325250771138701)
    ·
      refine ⟨35756846813746969039177013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95351591503325250771138701 35756846813746969039177013)
      ·
        refine ⟨3352204388788778347422845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35756846813746969039177013 3352204388788778347422845)
        ·
          refine ⟨1257076645795791880283567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3352204388788778347422845 1257076645795791880283567)
          ·
            refine ⟨1885614968693687820425351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257076645795791880283567 1885614968693687820425351)
            ·
              refine ⟨2828422453040531730638027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885614968693687820425351 2828422453040531730638027)
              ·
                refine ⟨4242633679560797595957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828422453040531730638027 4242633679560797595957041)
                ·
                  refine ⟨3181975259670598196967781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242633679560797595957041 3181975259670598196967781)
                  ·
                    refine ⟨596620361188237161931459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3181975259670598196967781 596620361188237161931459)
                    ·
                      rfl

theorem cell22_1742871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_1742871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742871 prefixEnd_1742871 := by exact prefixLift 1742871
  have htrace : WordTrace (prefixWord ++ tailWord_1742871) baseStart_1742871 baseEnd_1742871 := by
    simpa [prefixWord, tailWord_1742871, baseEnd_1742871] using wordTrace_append hprefix tailTrace_1742871
  have hstable : (prefixWord ++ tailWord_1742871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742871).length < 2 ^ (prefixWord ++ tailWord_1742871).sum := by decide
  have hdescent : baseEnd_1742871 < baseStart_1742871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742897 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 5]
def baseStart_1742897 : Nat := 118140960795 + 1742897 * 2 ^ 59
def prefixEnd_1742897 : Nat := 4983230072969 + 3 ^ 40 * 1742897 * 2
def baseEnd_1742897 : Nat := 198876420506527253593793

theorem tailTrace_1742897 : CollatzResearch.WordTrace tailWord_1742897 prefixEnd_1742897 198876420506527253593793 := by
  unfold tailWord_1742897
  simp only [CollatzResearch.WordTrace]
  refine ⟨63568675966789306954538945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42379117311192871303025963 63568675966789306954538945)
  ·
    refine ⟨47676506975091980215904209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63568675966789306954538945 47676506975091980215904209)
    ·
      refine ⟨35757380231318985161928157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47676506975091980215904209 35757380231318985161928157)
      ·
        refine ⟨13409017586744619435723059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35757380231318985161928157 13409017586744619435723059)
        ·
          refine ⟨20113526380116929153584589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409017586744619435723059 20113526380116929153584589)
          ·
            refine ⟨7542572392543848432594221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20113526380116929153584589 7542572392543848432594221)
            ·
              refine ⟨2828464647203943162222833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7542572392543848432594221 2828464647203943162222833)
              ·
                refine ⟨2121348485402957371667125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828464647203943162222833 2121348485402957371667125)
                ·
                  refine ⟨198876420506527253593793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2121348485402957371667125 198876420506527253593793)
                  ·
                    rfl

theorem cell22_1742897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_1742897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1742897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1742897 prefixEnd_1742897 := by exact prefixLift 1742897
  have htrace : WordTrace (prefixWord ++ tailWord_1742897) baseStart_1742897 baseEnd_1742897 := by
    simpa [prefixWord, tailWord_1742897, baseEnd_1742897] using wordTrace_append hprefix tailTrace_1742897
  have hstable : (prefixWord ++ tailWord_1742897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742897).length < 2 ^ (prefixWord ++ tailWord_1742897).sum := by decide
  have hdescent : baseEnd_1742897 < baseStart_1742897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743032 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_1743032 : Nat := 118140960795 + 1743032 * 2 ^ 59
def prefixEnd_1743032 : Nat := 4983230072969 + 3 ^ 40 * 1743032 * 2
def baseEnd_1743032 : Nat := 198891824926162136218655

theorem tailTrace_1743032 : CollatzResearch.WordTrace tailWord_1743032 prefixEnd_1743032 198891824926162136218655 := by
  unfold tailWord_1743032
  simp only [CollatzResearch.WordTrace]
  refine ⟨31786799910650112505351675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42382399880866816673802233 31786799910650112505351675)
  ·
    refine ⟨47680199865975168758027513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31786799910650112505351675 47680199865975168758027513)
    ·
      refine ⟨35760149899481376568520635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47680199865975168758027513 35760149899481376568520635)
      ·
        refine ⟨53640224849222064852780953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35760149899481376568520635 53640224849222064852780953)
        ·
          refine ⟨40230168636916548639585715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53640224849222064852780953 40230168636916548639585715)
          ·
            refine ⟨60345252955374822959378573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40230168636916548639585715 60345252955374822959378573)
            ·
              refine ⟨22629469858265558609766965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60345252955374822959378573 22629469858265558609766965)
              ·
                refine ⟨2121512799212396119665653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22629469858265558609766965 2121512799212396119665653)
                ·
                  refine ⟨198891824926162136218655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2121512799212396119665653 198891824926162136218655)
                  ·
                    rfl

theorem cell22_1743032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_1743032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743032 prefixEnd_1743032 := by exact prefixLift 1743032
  have htrace : WordTrace (prefixWord ++ tailWord_1743032) baseStart_1743032 baseEnd_1743032 := by
    simpa [prefixWord, tailWord_1743032, baseEnd_1743032] using wordTrace_append hprefix tailTrace_1743032
  have hstable : (prefixWord ++ tailWord_1743032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743032).length < 2 ^ (prefixWord ++ tailWord_1743032).sum := by decide
  have hdescent : baseEnd_1743032 < baseStart_1743032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743036 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1743036 : Nat := 118140960795 + 1743036 * 2 ^ 59
def prefixEnd_1743036 : Nat := 4983230072969 + 3 ^ 40 * 1743036 * 2
def baseEnd_1743036 : Nat := 596676844060231731555953

theorem tailTrace_1743036 : CollatzResearch.WordTrace tailWord_1743036 prefixEnd_1743036 596676844060231731555953 := by
  unfold tailWord_1743036
  simp only [CollatzResearch.WordTrace]
  refine ⟨31786872856642866846924481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42382497142190489129232641 31786872856642866846924481)
  ·
    refine ⟨23840154642482150135193361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31786872856642866846924481 23840154642482150135193361)
    ·
      refine ⟨17880115981861612601395021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23840154642482150135193361 17880115981861612601395021)
      ·
        refine ⟨6705043493198104725523133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17880115981861612601395021 6705043493198104725523133)
        ·
          refine ⟨2514391309949289272071175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6705043493198104725523133 2514391309949289272071175)
          ·
            refine ⟨3771586964923933908106763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514391309949289272071175 3771586964923933908106763)
            ·
              refine ⟨5657380447385900862160145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771586964923933908106763 5657380447385900862160145)
              ·
                refine ⟨4243035335539425646620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657380447385900862160145 4243035335539425646620109)
                ·
                  refine ⟨1591138250827284617482541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4243035335539425646620109 1591138250827284617482541)
                  ·
                    refine ⟨596676844060231731555953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591138250827284617482541 596676844060231731555953)
                    ·
                      rfl

theorem cell22_1743036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1743036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743036 prefixEnd_1743036 := by exact prefixLift 1743036
  have htrace : WordTrace (prefixWord ++ tailWord_1743036) baseStart_1743036 baseEnd_1743036 := by
    simpa [prefixWord, tailWord_1743036, baseEnd_1743036] using wordTrace_append hprefix tailTrace_1743036
  have hstable : (prefixWord ++ tailWord_1743036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743036).length < 2 ^ (prefixWord ++ tailWord_1743036).sum := by decide
  have hdescent : baseEnd_1743036 < baseStart_1743036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743094 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1743094 : Nat := 118140960795 + 1743094 * 2 ^ 59
def prefixEnd_1743094 : Nat := 4983230072969 + 3 ^ 40 * 1743094 * 2
def baseEnd_1743094 : Nat := 198898899548512971201925

theorem tailTrace_1743094 : CollatzResearch.WordTrace tailWord_1743094 prefixEnd_1743094 198898899548512971201925 := by
  unfold tailWord_1743094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973491321692225599966271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42383907431383739732973557 3973491321692225599966271)
  ·
    refine ⟨5960236982538338399949407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973491321692225599966271 5960236982538338399949407)
    ·
      refine ⟨8940355473807507599924111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5960236982538338399949407 8940355473807507599924111)
      ·
        refine ⟨13410533210711261399886167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8940355473807507599924111 13410533210711261399886167)
        ·
          refine ⟨20115799816066892099829251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13410533210711261399886167 20115799816066892099829251)
          ·
            refine ⟨30173699724100338149743877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20115799816066892099829251 30173699724100338149743877)
            ·
              refine ⟨5657568698268813403076977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30173699724100338149743877 5657568698268813403076977)
              ·
                refine ⟨4243176523701610052307733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657568698268813403076977 4243176523701610052307733)
                ·
                  refine ⟨198898899548512971201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243176523701610052307733 198898899548512971201925)
                  ·
                    rfl

theorem cell22_1743094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1743094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743094 prefixEnd_1743094 := by exact prefixLift 1743094
  have htrace : WordTrace (prefixWord ++ tailWord_1743094) baseStart_1743094 baseEnd_1743094 := by
    simpa [prefixWord, tailWord_1743094, baseEnd_1743094] using wordTrace_append hprefix tailTrace_1743094
  have hstable : (prefixWord ++ tailWord_1743094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743094).length < 2 ^ (prefixWord ++ tailWord_1743094).sum := by decide
  have hdescent : baseEnd_1743094 < baseStart_1743094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743107 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_1743107 : Nat := 118140960795 + 1743107 * 2 ^ 59
def prefixEnd_1743107 : Nat := 4983230072969 + 3 ^ 40 * 1743107 * 2
def baseEnd_1743107 : Nat := 596701148811211213030735

theorem tailTrace_1743107 : CollatzResearch.WordTrace tailWord_1743107 prefixEnd_1743107 596701148811211213030735 := by
  unfold tailWord_1743107
  simp only [CollatzResearch.WordTrace]
  refine ⟨63576335296028512819683575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42384223530685675213122383 63576335296028512819683575)
  ·
    refine ⟨95364502944042769229525363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63576335296028512819683575 95364502944042769229525363)
    ·
      refine ⟨143046754416064153844288045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95364502944042769229525363 143046754416064153844288045)
      ·
        refine ⟨53642532906024057691608017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143046754416064153844288045 53642532906024057691608017)
        ·
          refine ⟨40231899679518043268706013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53642532906024057691608017 40231899679518043268706013)
          ·
            refine ⟨15086962379819266225764755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40231899679518043268706013 15086962379819266225764755)
            ·
              refine ⟨22630443569728899338647133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15086962379819266225764755 22630443569728899338647133)
              ·
                refine ⟨8486416338648337251992675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22630443569728899338647133 8486416338648337251992675)
                ·
                  refine ⟨12729624507972505877989013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8486416338648337251992675 12729624507972505877989013)
                  ·
                    refine ⟨596701148811211213030735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12729624507972505877989013 596701148811211213030735)
                    ·
                      rfl

theorem cell22_1743107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_1743107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743107 prefixEnd_1743107 := by exact prefixLift 1743107
  have htrace : WordTrace (prefixWord ++ tailWord_1743107) baseStart_1743107 baseEnd_1743107 := by
    simpa [prefixWord, tailWord_1743107, baseEnd_1743107] using wordTrace_append hprefix tailTrace_1743107
  have hstable : (prefixWord ++ tailWord_1743107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743107).length < 2 ^ (prefixWord ++ tailWord_1743107).sum := by decide
  have hdescent : baseEnd_1743107 < baseStart_1743107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743152 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1743152 : Nat := 118140960795 + 1743152 * 2 ^ 59
def prefixEnd_1743152 : Nat := 4983230072969 + 3 ^ 40 * 1743152 * 2
def baseEnd_1743152 : Nat := 596716553230846095655597

theorem tailTrace_1743152 : CollatzResearch.WordTrace tailWord_1743152 prefixEnd_1743152 596716553230846095655597 := by
  unfold tailWord_1743152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788988290432742752535855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42385317720576990336714473 31788988290432742752535855)
  ·
    refine ⟨47683482435649114128803783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31788988290432742752535855 47683482435649114128803783)
    ·
      refine ⟨71525223653473671193205675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47683482435649114128803783 71525223653473671193205675)
      ·
        refine ⟨107287835480210506789808513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71525223653473671193205675 107287835480210506789808513)
        ·
          refine ⟨80465876610157880092356385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107287835480210506789808513 80465876610157880092356385)
          ·
            refine ⟨60349407457618410069267289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80465876610157880092356385 60349407457618410069267289)
            ·
              refine ⟨45262055593213807551950467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60349407457618410069267289 45262055593213807551950467)
              ·
                refine ⟨67893083389820711327925701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45262055593213807551950467 67893083389820711327925701)
                ·
                  refine ⟨12729953135591383373986069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67893083389820711327925701 12729953135591383373986069)
                  ·
                    refine ⟨596716553230846095655597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12729953135591383373986069 596716553230846095655597)
                    ·
                      rfl

theorem cell22_1743152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1743152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743152 prefixEnd_1743152 := by exact prefixLift 1743152
  have htrace : WordTrace (prefixWord ++ tailWord_1743152) baseStart_1743152 baseEnd_1743152 := by
    simpa [prefixWord, tailWord_1743152, baseEnd_1743152] using wordTrace_append hprefix tailTrace_1743152
  have hstable : (prefixWord ++ tailWord_1743152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743152).length < 2 ^ (prefixWord ++ tailWord_1743152).sum := by decide
  have hdescent : baseEnd_1743152 < baseStart_1743152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743184 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_1743184 : Nat := 118140960795 + 1743184 * 2 ^ 59
def prefixEnd_1743184 : Nat := 4983230072969 + 3 ^ 40 * 1743184 * 2
def baseEnd_1743184 : Nat := 198909169161602892951833

theorem tailTrace_1743184 : CollatzResearch.WordTrace tailWord_1743184 prefixEnd_1743184 198909169161602892951833 := by
  unfold tailWord_1743184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789571858374777485118303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42386095811166369980157737 31789571858374777485118303)
  ·
    refine ⟨47684357787562166227677455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31789571858374777485118303 47684357787562166227677455)
    ·
      refine ⟨71526536681343249341516183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47684357787562166227677455 71526536681343249341516183)
      ·
        refine ⟨107289805022014874012274275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71526536681343249341516183 107289805022014874012274275)
        ·
          refine ⟨160934707533022311018411413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107289805022014874012274275 160934707533022311018411413)
          ·
            refine ⟨7543814415610420828988035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 160934707533022311018411413 7543814415610420828988035)
            ·
              refine ⟨11315721623415631243482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543814415610420828988035 11315721623415631243482053)
              ·
                refine ⟨2121697804390430858152885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11315721623415631243482053 2121697804390430858152885)
                ·
                  refine ⟨198909169161602892951833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2121697804390430858152885 198909169161602892951833)
                  ·
                    rfl

theorem cell22_1743184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_1743184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743184 prefixEnd_1743184 := by exact prefixLift 1743184
  have htrace : WordTrace (prefixWord ++ tailWord_1743184) baseStart_1743184 baseEnd_1743184 := by
    simpa [prefixWord, tailWord_1743184, baseEnd_1743184] using wordTrace_append hprefix tailTrace_1743184
  have hstable : (prefixWord ++ tailWord_1743184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743184).length < 2 ^ (prefixWord ++ tailWord_1743184).sum := by decide
  have hdescent : baseEnd_1743184 < baseStart_1743184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743246 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1743246 : Nat := 118140960795 + 1743246 * 2 ^ 59
def prefixEnd_1743246 : Nat := 4983230072969 + 3 ^ 40 * 1743246 * 2
def baseEnd_1743246 : Nat := 198916243783953727935103

theorem tailTrace_1743246 : CollatzResearch.WordTrace tailWord_1743246 prefixEnd_1743246 198916243783953727935103 := by
  unfold tailWord_1743246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947675630315617444874199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42387603361683293039329061 7947675630315617444874199)
  ·
    refine ⟨11921513445473426167311299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947675630315617444874199 11921513445473426167311299)
    ·
      refine ⟨17882270168210139250966949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11921513445473426167311299 17882270168210139250966949)
      ·
        refine ⟨3352925656539401109556303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17882270168210139250966949 3352925656539401109556303)
        ·
          refine ⟨5029388484809101664334455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352925656539401109556303 5029388484809101664334455)
          ·
            refine ⟨7544082727213652496501683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029388484809101664334455 7544082727213652496501683)
            ·
              refine ⟨11316124090820478744752525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544082727213652496501683 11316124090820478744752525)
              ·
                refine ⟨4243546534057679529282197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11316124090820478744752525 4243546534057679529282197)
                ·
                  refine ⟨198916243783953727935103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243546534057679529282197 198916243783953727935103)
                  ·
                    rfl

theorem cell22_1743246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1743246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743246 prefixEnd_1743246 := by exact prefixLift 1743246
  have htrace : WordTrace (prefixWord ++ tailWord_1743246) baseStart_1743246 baseEnd_1743246 := by
    simpa [prefixWord, tailWord_1743246, baseEnd_1743246] using wordTrace_append hprefix tailTrace_1743246
  have hstable : (prefixWord ++ tailWord_1743246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743246).length < 2 ^ (prefixWord ++ tailWord_1743246).sum := by decide
  have hdescent : baseEnd_1743246 < baseStart_1743246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743265 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1743265 : Nat := 118140960795 + 1743265 * 2 ^ 59
def prefixEnd_1743265 : Nat := 4983230072969 + 3 ^ 40 * 1743265 * 2
def baseEnd_1743265 : Nat := 596755235440151467580251

theorem tailTrace_1743265 : CollatzResearch.WordTrace tailWord_1743265 prefixEnd_1743265 596755235440151467580251 := by
  unfold tailWord_1743265
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582098029456105803935249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42388065352970737202623499 63582098029456105803935249)
  ·
    refine ⟨47686573522092079352951437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582098029456105803935249 47686573522092079352951437)
    ·
      refine ⟨17882465070784529757356789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47686573522092079352951437 17882465070784529757356789)
      ·
        refine ⟨1676481100386049664752199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17882465070784529757356789 1676481100386049664752199)
        ·
          refine ⟨2514721650579074497128299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676481100386049664752199 2514721650579074497128299)
          ·
            refine ⟨3772082475868611745692449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514721650579074497128299 3772082475868611745692449)
            ·
              refine ⟨2829061856901458809269337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772082475868611745692449 2829061856901458809269337)
              ·
                refine ⟨2121796392676094106952003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829061856901458809269337 2121796392676094106952003)
                ·
                  refine ⟨3182694589014141160428005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121796392676094106952003 3182694589014141160428005)
                  ·
                    refine ⟨596755235440151467580251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182694589014141160428005 596755235440151467580251)
                    ·
                      rfl

theorem cell22_1743265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1743265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743265 prefixEnd_1743265 := by exact prefixLift 1743265
  have htrace : WordTrace (prefixWord ++ tailWord_1743265) baseStart_1743265 baseEnd_1743265 := by
    simpa [prefixWord, tailWord_1743265, baseEnd_1743265] using wordTrace_append hprefix tailTrace_1743265
  have hstable : (prefixWord ++ tailWord_1743265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743265).length < 2 ^ (prefixWord ++ tailWord_1743265).sum := by decide
  have hdescent : baseEnd_1743265 < baseStart_1743265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743297 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 6]
def baseStart_1743297 : Nat := 118140960795 + 1743297 * 2 ^ 59
def prefixEnd_1743297 : Nat := 4983230072969 + 3 ^ 40 * 1743297 * 2
def baseEnd_1743297 : Nat := 198922063231371350260051

theorem tailTrace_1743297 : CollatzResearch.WordTrace tailWord_1743297 prefixEnd_1743297 198922063231371350260051 := by
  unfold tailWord_1743297
  simp only [CollatzResearch.WordTrace]
  refine ⟨63583265165340175269100145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42388843443560116846066763 63583265165340175269100145)
  ·
    refine ⟨47687448874005131451825109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63583265165340175269100145 47687448874005131451825109)
    ·
      refine ⟨1117674582984495268402151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 47687448874005131451825109 1117674582984495268402151)
      ·
        refine ⟨1676511874476742902603227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117674582984495268402151 1676511874476742902603227)
        ·
          refine ⟨2514767811715114353904841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676511874476742902603227 2514767811715114353904841)
          ·
            refine ⟨1886075858786335765428631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514767811715114353904841 1886075858786335765428631)
            ·
              refine ⟨2829113788179503648142947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886075858786335765428631 2829113788179503648142947)
              ·
                refine ⟨4243670682269255472214421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829113788179503648142947 4243670682269255472214421)
                ·
                  refine ⟨198922063231371350260051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243670682269255472214421 198922063231371350260051)
                  ·
                    rfl

theorem cell22_1743297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_1743297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743297 prefixEnd_1743297 := by exact prefixLift 1743297
  have htrace : WordTrace (prefixWord ++ tailWord_1743297) baseStart_1743297 baseEnd_1743297 := by
    simpa [prefixWord, tailWord_1743297, baseEnd_1743297] using wordTrace_append hprefix tailTrace_1743297
  have hstable : (prefixWord ++ tailWord_1743297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743297).length < 2 ^ (prefixWord ++ tailWord_1743297).sum := by decide
  have hdescent : baseEnd_1743297 < baseStart_1743297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743381 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 6]
def baseStart_1743381 : Nat := 118140960795 + 1743381 * 2 ^ 59
def prefixEnd_1743381 : Nat := 4983230072969 + 3 ^ 40 * 1743381 * 2
def baseEnd_1743381 : Nat := 198931648203588610559965

theorem tailTrace_1743381 : CollatzResearch.WordTrace tailWord_1743381 prefixEnd_1743381 198931648203588610559965 := by
  unfold tailWord_1743381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63586328897035857615157997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42390885931357238410105331 63586328897035857615157997)
  ·
    refine ⟨23844873336388446605684249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63586328897035857615157997 23844873336388446605684249)
    ·
      refine ⟨17883655002291334954263187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23844873336388446605684249 17883655002291334954263187)
      ·
        refine ⟨26825482503437002431394781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17883655002291334954263187 26825482503437002431394781)
        ·
          refine ⟨10059555938788875911773043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26825482503437002431394781 10059555938788875911773043)
          ·
            refine ⟨15089333908183313867659565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059555938788875911773043 15089333908183313867659565)
            ·
              refine ⟨5658500215568742700372337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15089333908183313867659565 5658500215568742700372337)
              ·
                refine ⟨4243875161676557025279253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658500215568742700372337 4243875161676557025279253)
                ·
                  refine ⟨198931648203588610559965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243875161676557025279253 198931648203588610559965)
                  ·
                    rfl

theorem cell22_1743381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_1743381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743381 prefixEnd_1743381 := by exact prefixLift 1743381
  have htrace : WordTrace (prefixWord ++ tailWord_1743381) baseStart_1743381 baseEnd_1743381 := by
    simpa [prefixWord, tailWord_1743381, baseEnd_1743381] using wordTrace_append hprefix tailTrace_1743381
  have hstable : (prefixWord ++ tailWord_1743381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743381).length < 2 ^ (prefixWord ++ tailWord_1743381).sum := by decide
  have hdescent : baseEnd_1743381 < baseStart_1743381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743400 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1743400 : Nat := 118140960795 + 1743400 * 2 ^ 59
def prefixEnd_1743400 : Nat := 4983230072969 + 3 ^ 40 * 1743400 * 2
def baseEnd_1743400 : Nat := 596801448699056115454837

theorem tailTrace_1743400 : CollatzResearch.WordTrace tailWord_1743400 prefixEnd_1743400 596801448699056115454837 := by
  unfold tailWord_1743400
  simp only [CollatzResearch.WordTrace]
  refine ⟨31793510941983511930049827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42391347922644682573399769 31793510941983511930049827)
  ·
    refine ⟨47690266412975267895074741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31793510941983511930049827 47690266412975267895074741)
    ·
      refine ⟨4470962476216431365163257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47690266412975267895074741 4470962476216431365163257)
      ·
        refine ⟨3353221857162323523872443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4470962476216431365163257 3353221857162323523872443)
        ·
          refine ⟨5029832785743485285808665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353221857162323523872443 5029832785743485285808665)
          ·
            refine ⟨3772374589307613964356499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029832785743485285808665 3772374589307613964356499)
            ·
              refine ⟨5658561883961420946534749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772374589307613964356499 5658561883961420946534749)
              ·
                refine ⟨2121960706485532854950531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5658561883961420946534749 2121960706485532854950531)
                ·
                  refine ⟨3182941059728299282425797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121960706485532854950531 3182941059728299282425797)
                  ·
                    refine ⟨596801448699056115454837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182941059728299282425797 596801448699056115454837)
                    ·
                      rfl

theorem cell22_1743400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1743400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743400 prefixEnd_1743400 := by exact prefixLift 1743400
  have htrace : WordTrace (prefixWord ++ tailWord_1743400) baseStart_1743400 baseEnd_1743400 := by
    simpa [prefixWord, tailWord_1743400, baseEnd_1743400] using wordTrace_append hprefix tailTrace_1743400
  have hstable : (prefixWord ++ tailWord_1743400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743400).length < 2 ^ (prefixWord ++ tailWord_1743400).sum := by decide
  have hdescent : baseEnd_1743400 < baseStart_1743400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743411 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_1743411 : Nat := 118140960795 + 1743411 * 2 ^ 59
def prefixEnd_1743411 : Nat := 4983230072969 + 3 ^ 40 * 1743411 * 2
def baseEnd_1743411 : Nat := 596805214223855753429803

theorem tailTrace_1743411 : CollatzResearch.WordTrace tailWord_1743411 prefixEnd_1743411 596805214223855753429803 := by
  unfold tailWord_1743411
  simp only [CollatzResearch.WordTrace]
  refine ⟨63587423086927172738750087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42391615391284781825833391 63587423086927172738750087)
  ·
    refine ⟨95381134630390759108125131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63587423086927172738750087 95381134630390759108125131)
    ·
      refine ⟨143071701945586138662187697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95381134630390759108125131 143071701945586138662187697)
      ·
        refine ⟨107303776459189603996640773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143071701945586138662187697 107303776459189603996640773)
        ·
          refine ⟨20119458086098050749370145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107303776459189603996640773 20119458086098050749370145)
          ·
            refine ⟨15089593564573538062027609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20119458086098050749370145 15089593564573538062027609)
            ·
              refine ⟨11317195173430153546520707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15089593564573538062027609 11317195173430153546520707)
              ·
                refine ⟨16975792760145230319781061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11317195173430153546520707 16975792760145230319781061)
                ·
                  refine ⟨3182961142527230684958949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16975792760145230319781061 3182961142527230684958949)
                  ·
                    refine ⟨596805214223855753429803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3182961142527230684958949 596805214223855753429803)
                    ·
                      rfl

theorem cell22_1743411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_1743411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743411 prefixEnd_1743411 := by exact prefixLift 1743411
  have htrace : WordTrace (prefixWord ++ tailWord_1743411) baseStart_1743411 baseEnd_1743411 := by
    simpa [prefixWord, tailWord_1743411, baseEnd_1743411] using wordTrace_append hprefix tailTrace_1743411
  have hstable : (prefixWord ++ tailWord_1743411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743411).length < 2 ^ (prefixWord ++ tailWord_1743411).sum := by decide
  have hdescent : baseEnd_1743411 < baseStart_1743411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743413 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1743413 : Nat := 118140960795 + 1743413 * 2 ^ 59
def prefixEnd_1743413 : Nat := 4983230072969 + 3 ^ 40 * 1743413 * 2
def baseEnd_1743413 : Nat := 596805898864728414879797

theorem tailTrace_1743413 : CollatzResearch.WordTrace tailWord_1743413 prefixEnd_1743413 596805898864728414879797 := by
  unfold tailWord_1743413
  simp only [CollatzResearch.WordTrace]
  refine ⟨63587496032919927080322893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42391664021946618053548595 63587496032919927080322893)
  ·
    refine ⟨23845311012344972655121085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63587496032919927080322893 23845311012344972655121085)
    ·
      refine ⟨8941991629629364745670407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23845311012344972655121085 8941991629629364745670407)
      ·
        refine ⟨13412987444444047118505611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8941991629629364745670407 13412987444444047118505611)
        ·
          refine ⟨20119481166666070677758417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412987444444047118505611 20119481166666070677758417)
          ·
            refine ⟨15089610874999553008318813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20119481166666070677758417 15089610874999553008318813)
            ·
              refine ⟨5658604078124832378119555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15089610874999553008318813 5658604078124832378119555)
              ·
                refine ⟨8487906117187248567179333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658604078124832378119555 8487906117187248567179333)
                ·
                  refine ⟨1591482396972609106346125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8487906117187248567179333 1591482396972609106346125)
                  ·
                    refine ⟨596805898864728414879797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591482396972609106346125 596805898864728414879797)
                    ·
                      rfl

theorem cell22_1743413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1743413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743413 prefixEnd_1743413 := by exact prefixLift 1743413
  have htrace : WordTrace (prefixWord ++ tailWord_1743413) baseStart_1743413 baseEnd_1743413 := by
    simpa [prefixWord, tailWord_1743413, baseEnd_1743413] using wordTrace_append hprefix tailTrace_1743413
  have hstable : (prefixWord ++ tailWord_1743413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743413).length < 2 ^ (prefixWord ++ tailWord_1743413).sum := by decide
  have hdescent : baseEnd_1743413 < baseStart_1743413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743471 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 7]
def baseStart_1743471 : Nat := 118140960795 + 1743471 * 2 ^ 59
def prefixEnd_1743471 : Nat := 4983230072969 + 3 ^ 40 * 1743471 * 2
def baseEnd_1743471 : Nat := 198941917816678532309873

theorem tailTrace_1743471 : CollatzResearch.WordTrace tailWord_1743471 prefixEnd_1743471 198941917816678532309873 := by
  unfold tailWord_1743471
  simp only [CollatzResearch.WordTrace]
  refine ⟨63589611466709802985934267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42393074311139868657289511 63589611466709802985934267)
  ·
    refine ⟨95384417200064704478901401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63589611466709802985934267 95384417200064704478901401)
    ·
      refine ⟨71538312900048528359176051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95384417200064704478901401 71538312900048528359176051)
      ·
        refine ⟨107307469350072792538764077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71538312900048528359176051 107307469350072792538764077)
        ·
          refine ⟨40240301006277297202036529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107307469350072792538764077 40240301006277297202036529)
          ·
            refine ⟨30180225754707972901527397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40240301006277297202036529 30180225754707972901527397)
            ·
              refine ⟨5658792329007744919036387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30180225754707972901527397 5658792329007744919036387)
              ·
                refine ⟨8488188493511617378554581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658792329007744919036387 8488188493511617378554581)
                ·
                  refine ⟨198941917816678532309873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8488188493511617378554581 198941917816678532309873)
                  ·
                    rfl

theorem cell22_1743471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_1743471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743471 prefixEnd_1743471 := by exact prefixLift 1743471
  have htrace : WordTrace (prefixWord ++ tailWord_1743471) baseStart_1743471 baseEnd_1743471 := by
    simpa [prefixWord, tailWord_1743471, baseEnd_1743471] using wordTrace_append hprefix tailTrace_1743471
  have hstable : (prefixWord ++ tailWord_1743471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743471).length < 2 ^ (prefixWord ++ tailWord_1743471).sum := by decide
  have hdescent : baseEnd_1743471 < baseStart_1743471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743488 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_1743488 : Nat := 118140960795 + 1743488 * 2 ^ 59
def prefixEnd_1743488 : Nat := 4983230072969 + 3 ^ 40 * 1743488 * 2
def baseEnd_1743488 : Nat := 198943857632484406418189

theorem tailTrace_1743488 : CollatzResearch.WordTrace tailWord_1743488 prefixEnd_1743488 198943857632484406418189 := by
  unfold tailWord_1743488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795115753824107444651559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42393487671765476592868745 31795115753824107444651559)
  ·
    refine ⟨47692673630736161166977339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31795115753824107444651559 47692673630736161166977339)
    ·
      refine ⟨71539010446104241750466009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47692673630736161166977339 71539010446104241750466009)
      ·
        refine ⟨53654257834578181312849507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71539010446104241750466009 53654257834578181312849507)
        ·
          refine ⟨80481386751867271969274261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53654257834578181312849507 80481386751867271969274261)
          ·
            refine ⟨3772565003993778373559731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80481386751867271969274261 3772565003993778373559731)
            ·
              refine ⟨5658847505990667560339597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772565003993778373559731 5658847505990667560339597)
              ·
                refine ⟨2122067814746500335127349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5658847505990667560339597 2122067814746500335127349)
                ·
                  refine ⟨198943857632484406418189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122067814746500335127349 198943857632484406418189)
                  ·
                    rfl

theorem cell22_1743488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_1743488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743488 prefixEnd_1743488 := by exact prefixLift 1743488
  have htrace : WordTrace (prefixWord ++ tailWord_1743488) baseStart_1743488 baseEnd_1743488 := by
    simpa [prefixWord, tailWord_1743488, baseEnd_1743488] using wordTrace_append hprefix tailTrace_1743488
  have hstable : (prefixWord ++ tailWord_1743488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743488).length < 2 ^ (prefixWord ++ tailWord_1743488).sum := by decide
  have hdescent : baseEnd_1743488 < baseStart_1743488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743610 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1743610 : Nat := 118140960795 + 1743610 * 2 ^ 59
def prefixEnd_1743610 : Nat := 4983230072969 + 3 ^ 40 * 1743610 * 2
def baseEnd_1743610 : Nat := 596873335990685567704193

theorem tailTrace_1743610 : CollatzResearch.WordTrace tailWord_1743610 prefixEnd_1743610 596873335990685567704193 := by
  unfold tailWord_1743610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898670303301557431311071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42396454142137486483496189 15898670303301557431311071)
  ·
    refine ⟨23848005454952336146966607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15898670303301557431311071 23848005454952336146966607)
    ·
      refine ⟨35772008182428504220449911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23848005454952336146966607 35772008182428504220449911)
      ·
        refine ⟨53658012273642756330674867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35772008182428504220449911 53658012273642756330674867)
        ·
          refine ⟨80487018410464134496012301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53658012273642756330674867 80487018410464134496012301)
          ·
            refine ⟨30182631903924050436004613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80487018410464134496012301 30182631903924050436004613)
            ·
              refine ⟨5659243481985759456750865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30182631903924050436004613 5659243481985759456750865)
              ·
                refine ⟨4244432611489319592563149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5659243481985759456750865 4244432611489319592563149)
                ·
                  refine ⟨1591662229308494847211181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4244432611489319592563149 1591662229308494847211181)
                  ·
                    refine ⟨596873335990685567704193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591662229308494847211181 596873335990685567704193)
                    ·
                      rfl

theorem cell22_1743610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1743610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743610 prefixEnd_1743610 := by exact prefixLift 1743610
  have htrace : WordTrace (prefixWord ++ tailWord_1743610) baseStart_1743610 baseEnd_1743610 := by
    simpa [prefixWord, tailWord_1743610, baseEnd_1743610] using wordTrace_append hprefix tailTrace_1743610
  have hstable : (prefixWord ++ tailWord_1743610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743610).length < 2 ^ (prefixWord ++ tailWord_1743610).sum := by decide
  have hdescent : baseEnd_1743610 < baseStart_1743610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743713 : List Nat := [1, 2, 3, 1, 1, 1, 2, 11]
def baseStart_1743713 : Nat := 118140960795 + 1743713 * 2 ^ 59
def prefixEnd_1743713 : Nat := 4983230072969 + 3 ^ 40 * 1743713 * 2
def baseEnd_1743713 : Nat := 66323177221736403597653

theorem tailTrace_1743713 : CollatzResearch.WordTrace tailWord_1743713 prefixEnd_1743713 66323177221736403597653 := by
  unfold tailWord_1743713
  simp only [CollatzResearch.WordTrace]
  refine ⟨63598437931833078316243793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42398958621222052210829195 63598437931833078316243793)
  ·
    refine ⟨47698828448874808737182845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63598437931833078316243793 47698828448874808737182845)
    ·
      refine ⟨17887060668328053276443567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47698828448874808737182845 17887060668328053276443567)
      ·
        refine ⟨26830591002492079914665351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887060668328053276443567 26830591002492079914665351)
        ·
          refine ⟨40245886503738119871998027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26830591002492079914665351 40245886503738119871998027)
          ·
            refine ⟨60368829755607179807997041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40245886503738119871998027 60368829755607179807997041)
            ·
              refine ⟨45276622316705384855997781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60368829755607179807997041 45276622316705384855997781)
              ·
                refine ⟨66323177221736403597653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 45276622316705384855997781 66323177221736403597653)
                ·
                  rfl

theorem cell22_1743713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 11].length) (baseStart_1743713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743713 prefixEnd_1743713 := by exact prefixLift 1743713
  have htrace : WordTrace (prefixWord ++ tailWord_1743713) baseStart_1743713 baseEnd_1743713 := by
    simpa [prefixWord, tailWord_1743713, baseEnd_1743713] using wordTrace_append hprefix tailTrace_1743713
  have hstable : (prefixWord ++ tailWord_1743713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743713).length < 2 ^ (prefixWord ++ tailWord_1743713).sum := by decide
  have hdescent : baseEnd_1743713 < baseStart_1743713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743717 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_1743717 : Nat := 118140960795 + 1743717 * 2 ^ 59
def prefixEnd_1743717 : Nat := 4983230072969 + 3 ^ 40 * 1743717 * 2
def baseEnd_1743717 : Nat := 596909964277372955278865

theorem tailTrace_1743717 : CollatzResearch.WordTrace tailWord_1743717 prefixEnd_1743717 596909964277372955278865 := by
  unfold tailWord_1743717
  simp only [CollatzResearch.WordTrace]
  refine ⟨63598583823818586999389405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42399055882545724666259603 63598583823818586999389405)
  ·
    refine ⟨23849468933931970124771027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63598583823818586999389405 23849468933931970124771027)
    ·
      refine ⟨35774203400897955187156541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23849468933931970124771027 35774203400897955187156541)
      ·
        refine ⟨13415326275336733195183703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35774203400897955187156541 13415326275336733195183703)
        ·
          refine ⟨20122989413005099792775555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13415326275336733195183703 20122989413005099792775555)
          ·
            refine ⟨30184484119507649689163333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20122989413005099792775555 30184484119507649689163333)
            ·
              refine ⟨5659590772407684316718125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30184484119507649689163333 5659590772407684316718125)
              ·
                refine ⟨2122346539652881618769297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5659590772407684316718125 2122346539652881618769297)
                ·
                  refine ⟨1591759904739661214076973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2122346539652881618769297 1591759904739661214076973)
                  ·
                    refine ⟨596909964277372955278865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591759904739661214076973 596909964277372955278865)
                    ·
                      rfl

theorem cell22_1743717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_1743717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743717 prefixEnd_1743717 := by exact prefixLift 1743717
  have htrace : WordTrace (prefixWord ++ tailWord_1743717) baseStart_1743717 baseEnd_1743717 := by
    simpa [prefixWord, tailWord_1743717, baseEnd_1743717] using wordTrace_append hprefix tailTrace_1743717
  have hstable : (prefixWord ++ tailWord_1743717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743717).length < 2 ^ (prefixWord ++ tailWord_1743717).sum := by decide
  have hdescent : baseEnd_1743717 < baseStart_1743717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743798 : List Nat := [5, 1, 4, 1, 2, 1, 8]
def baseStart_1743798 : Nat := 118140960795 + 1743798 * 2 ^ 59
def prefixEnd_1743798 : Nat := 4983230072969 + 3 ^ 40 * 1743798 * 2
def baseEnd_1743798 : Nat := 22108803416026509037171

theorem tailTrace_1743798 : CollatzResearch.WordTrace tailWord_1743798 prefixEnd_1743798 22108803416026509037171 := by
  unfold tailWord_1743798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975096133532821114568003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42401025424350091888725365 3975096133532821114568003)
  ·
    refine ⟨5962644200299231671852005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3975096133532821114568003 5962644200299231671852005)
    ·
      refine ⟨1117995787556105938472251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5962644200299231671852005 1117995787556105938472251)
      ·
        refine ⟨1676993681334158907708377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117995787556105938472251 1676993681334158907708377)
        ·
          refine ⟨1257745261000619180781283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676993681334158907708377 1257745261000619180781283)
          ·
            refine ⟨1886617891500928771171925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257745261000619180781283 1886617891500928771171925)
            ·
              refine ⟨22108803416026509037171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1886617891500928771171925 22108803416026509037171)
              ·
                rfl

theorem cell22_1743798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 8].length) (baseStart_1743798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743798 prefixEnd_1743798 := by exact prefixLift 1743798
  have htrace : WordTrace (prefixWord ++ tailWord_1743798) baseStart_1743798 baseEnd_1743798 := by
    simpa [prefixWord, tailWord_1743798, baseEnd_1743798] using wordTrace_append hprefix tailTrace_1743798
  have hstable : (prefixWord ++ tailWord_1743798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743798).length < 2 ^ (prefixWord ++ tailWord_1743798).sum := by decide
  have hdescent : baseEnd_1743798 < baseStart_1743798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743826 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1743826 : Nat := 118140960795 + 1743826 * 2 ^ 59
def prefixEnd_1743826 : Nat := 4983230072969 + 3 ^ 40 * 1743826 * 2
def baseEnd_1743826 : Nat := 198982425734977668101177

theorem tailTrace_1743826 : CollatzResearch.WordTrace tailWord_1743826 prefixEnd_1743826 198982425734977668101177 := by
  unfold tailWord_1743826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15900639845105924653776833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42401706253615799076738221 15900639845105924653776833)
  ·
    refine ⟨11925479883829443490332625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15900639845105924653776833 11925479883829443490332625)
    ·
      refine ⟨8944109912872082617749469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11925479883829443490332625 8944109912872082617749469)
      ·
        refine ⟨3354041217327030981656051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8944109912872082617749469 3354041217327030981656051)
        ·
          refine ⟨5031061825990546472484077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354041217327030981656051 5031061825990546472484077)
          ·
            refine ⟨1886648184746454927181529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5031061825990546472484077 1886648184746454927181529)
            ·
              refine ⟨1414986138559841195386147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886648184746454927181529 1414986138559841195386147)
              ·
                refine ⟨2122479207839761793079221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414986138559841195386147 2122479207839761793079221)
                ·
                  refine ⟨198982425734977668101177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122479207839761793079221 198982425734977668101177)
                  ·
                    rfl

theorem cell22_1743826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1743826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743826 prefixEnd_1743826 := by exact prefixLift 1743826
  have htrace : WordTrace (prefixWord ++ tailWord_1743826) baseStart_1743826 baseEnd_1743826 := by
    simpa [prefixWord, tailWord_1743826, baseEnd_1743826] using wordTrace_append hprefix tailTrace_1743826
  have hstable : (prefixWord ++ tailWord_1743826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743826).length < 2 ^ (prefixWord ++ tailWord_1743826).sum := by decide
  have hdescent : baseEnd_1743826 < baseStart_1743826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743860 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1743860 : Nat := 118140960795 + 1743860 * 2 ^ 59
def prefixEnd_1743860 : Nat := 4983230072969 + 3 ^ 40 * 1743860 * 2
def baseEnd_1743860 : Nat := 198986305366589416317809

theorem tailTrace_1743860 : CollatzResearch.WordTrace tailWord_1743860 prefixEnd_1743860 198986305366589416317809 := by
  unfold tailWord_1743860
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801899731150261210922517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42402532974867014947896689 31801899731150261210922517)
  ·
    refine ⟨1490714049897668494261993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31801899731150261210922517 1490714049897668494261993)
    ·
      refine ⟨1118035537423251370696495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490714049897668494261993 1118035537423251370696495)
      ·
        refine ⟨1677053306134877056044743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118035537423251370696495 1677053306134877056044743)
        ·
          refine ⟨2515579959202315584067115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677053306134877056044743 2515579959202315584067115)
          ·
            refine ⟨3773369938803473376100673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515579959202315584067115 3773369938803473376100673)
            ·
              refine ⟨2830027454102605032075505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773369938803473376100673 2830027454102605032075505)
              ·
                refine ⟨2122520590576953774056629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830027454102605032075505 2122520590576953774056629)
                ·
                  refine ⟨198986305366589416317809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122520590576953774056629 198986305366589416317809)
                  ·
                    rfl

theorem cell22_1743860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1743860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743860 prefixEnd_1743860 := by exact prefixLift 1743860
  have htrace : WordTrace (prefixWord ++ tailWord_1743860) baseStart_1743860 baseEnd_1743860 := by
    simpa [prefixWord, tailWord_1743860, baseEnd_1743860] using wordTrace_append hprefix tailTrace_1743860
  have hstable : (prefixWord ++ tailWord_1743860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743860).length < 2 ^ (prefixWord ++ tailWord_1743860).sum := by decide
  have hdescent : baseEnd_1743860 < baseStart_1743860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743882 : List Nat := [3, 1, 2, 2, 3, 1, 3, 7]
def baseStart_1743882 : Nat := 118140960795 + 1743882 * 2 ^ 59
def prefixEnd_1743882 : Nat := 4983230072969 + 3 ^ 40 * 1743882 * 2
def baseEnd_1743882 : Nat := 66329605238818613878151

theorem tailTrace_1743882 : CollatzResearch.WordTrace tailWord_1743882 prefixEnd_1743882 66329605238818613878151 := by
  unfold tailWord_1743882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901150467055205044786475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42403067912147213452763933 15901150467055205044786475)
  ·
    refine ⟨23851725700582807567179713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15901150467055205044786475 23851725700582807567179713)
    ·
      refine ⟨17888794275437105675384785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23851725700582807567179713 17888794275437105675384785)
      ·
        refine ⟨13416595706577829256538589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17888794275437105675384785 13416595706577829256538589)
        ·
          refine ⟨5031223389966685971201971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13416595706577829256538589 5031223389966685971201971)
          ·
            refine ⟨7546835084950028956802957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031223389966685971201971 7546835084950028956802957)
            ·
              refine ⟨2830063156856260858801109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7546835084950028956802957 2830063156856260858801109)
              ·
                refine ⟨66329605238818613878151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2830063156856260858801109 66329605238818613878151)
                ·
                  rfl

theorem cell22_1743882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_1743882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743882 prefixEnd_1743882 := by exact prefixLift 1743882
  have htrace : WordTrace (prefixWord ++ tailWord_1743882) baseStart_1743882 baseEnd_1743882 := by
    simpa [prefixWord, tailWord_1743882, baseEnd_1743882] using wordTrace_append hprefix tailTrace_1743882
  have hstable : (prefixWord ++ tailWord_1743882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743882).length < 2 ^ (prefixWord ++ tailWord_1743882).sum := by decide
  have hdescent : baseEnd_1743882 < baseStart_1743882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743897 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_1743897 : Nat := 118140960795 + 1743897 * 2 ^ 59
def prefixEnd_1743897 : Nat := 4983230072969 + 3 ^ 40 * 1743897 * 2
def baseEnd_1743897 : Nat := 596971581955912485778313

theorem tailTrace_1743897 : CollatzResearch.WordTrace tailWord_1743897 prefixEnd_1743897 596971581955912485778313 := by
  unfold tailWord_1743897
  simp only [CollatzResearch.WordTrace]
  refine ⟨63605148963166477740941945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42403432642110985160627963 63605148963166477740941945)
  ·
    refine ⟨47703861722374858305706459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63605148963166477740941945 47703861722374858305706459)
    ·
      refine ⟨71555792583562287458559689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47703861722374858305706459 71555792583562287458559689)
      ·
        refine ⟨53666844437671715593919767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71555792583562287458559689 53666844437671715593919767)
        ·
          refine ⟨80500266656507573390879651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53666844437671715593919767 80500266656507573390879651)
          ·
            refine ⟨120750399984761360086319477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80500266656507573390879651 120750399984761360086319477)
            ·
              refine ⟨11320349998571377508092451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120750399984761360086319477 11320349998571377508092451)
              ·
                refine ⟨16980524997857066262138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320349998571377508092451 16980524997857066262138677)
                ·
                  refine ⟨1591924218549099962075501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16980524997857066262138677 1591924218549099962075501)
                  ·
                    refine ⟨596971581955912485778313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1591924218549099962075501 596971581955912485778313)
                    ·
                      rfl

theorem cell22_1743897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_1743897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743897 prefixEnd_1743897 := by exact prefixLift 1743897
  have htrace : WordTrace (prefixWord ++ tailWord_1743897) baseStart_1743897 baseEnd_1743897 := by
    simpa [prefixWord, tailWord_1743897, baseEnd_1743897] using wordTrace_append hprefix tailTrace_1743897
  have hstable : (prefixWord ++ tailWord_1743897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743897).length < 2 ^ (prefixWord ++ tailWord_1743897).sum := by decide
  have hdescent : baseEnd_1743897 < baseStart_1743897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743901 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1743901 : Nat := 118140960795 + 1743901 * 2 ^ 59
def prefixEnd_1743901 : Nat := 4983230072969 + 3 ^ 40 * 1743901 * 2
def baseEnd_1743901 : Nat := 596972951237657808678301

theorem tailTrace_1743901 : CollatzResearch.WordTrace tailWord_1743901 prefixEnd_1743901 596972951237657808678301 := by
  unfold tailWord_1743901
  simp only [CollatzResearch.WordTrace]
  refine ⟨63605294855151986424087557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42403529903434657616058371 63605294855151986424087557)
  ·
    refine ⟨11925992785340997454516417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63605294855151986424087557 11925992785340997454516417)
    ·
      refine ⟨8944494589005748090887313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11925992785340997454516417 8944494589005748090887313)
      ·
        refine ⟨6708370941754311068165485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8944494589005748090887313 6708370941754311068165485)
        ·
          refine ⟨2515639103157866650562057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6708370941754311068165485 2515639103157866650562057)
          ·
            refine ⟨1886729327368399987921543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515639103157866650562057 1886729327368399987921543)
            ·
              refine ⟨2830093991052599981882315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886729327368399987921543 2830093991052599981882315)
              ·
                refine ⟨4245140986578899972823473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830093991052599981882315 4245140986578899972823473)
                ·
                  refine ⟨3183855739934174979617605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4245140986578899972823473 3183855739934174979617605)
                  ·
                    refine ⟨596972951237657808678301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3183855739934174979617605 596972951237657808678301)
                    ·
                      rfl

theorem cell22_1743901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1743901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743901 prefixEnd_1743901 := by exact prefixLift 1743901
  have htrace : WordTrace (prefixWord ++ tailWord_1743901) baseStart_1743901 baseEnd_1743901 := by
    simpa [prefixWord, tailWord_1743901, baseEnd_1743901] using wordTrace_append hprefix tailTrace_1743901
  have hstable : (prefixWord ++ tailWord_1743901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743901).length < 2 ^ (prefixWord ++ tailWord_1743901).sum := by decide
  have hdescent : baseEnd_1743901 < baseStart_1743901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743944 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_1743944 : Nat := 118140960795 + 1743944 * 2 ^ 59
def prefixEnd_1743944 : Nat := 4983230072969 + 3 ^ 40 * 1743944 * 2
def baseEnd_1743944 : Nat := 198995890338806676617723

theorem tailTrace_1743944 : CollatzResearch.WordTrace tailWord_1743944 prefixEnd_1743944 198995890338806676617723 := by
  unfold tailWord_1743944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31803431596998102383951443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42404575462664136511935257 31803431596998102383951443)
  ·
    refine ⟨47705147395497153575927165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31803431596998102383951443 47705147395497153575927165)
    ·
      refine ⟨17889430273311432590972687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47705147395497153575927165 17889430273311432590972687)
      ·
        refine ⟨26834145409967148886459031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17889430273311432590972687 26834145409967148886459031)
        ·
          refine ⟨40251218114950723329688547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26834145409967148886459031 40251218114950723329688547)
          ·
            refine ⟨60376827172426084994532821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40251218114950723329688547 60376827172426084994532821)
            ·
              refine ⟨1415081886853736367059363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60376827172426084994532821 1415081886853736367059363)
              ·
                refine ⟨2122622830280604550589045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415081886853736367059363 2122622830280604550589045)
                ·
                  refine ⟨198995890338806676617723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122622830280604550589045 198995890338806676617723)
                  ·
                    rfl

theorem cell22_1743944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_1743944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1743944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1743944 prefixEnd_1743944 := by exact prefixLift 1743944
  have htrace : WordTrace (prefixWord ++ tailWord_1743944) baseStart_1743944 baseEnd_1743944 := by
    simpa [prefixWord, tailWord_1743944, baseEnd_1743944] using wordTrace_append hprefix tailTrace_1743944
  have hstable : (prefixWord ++ tailWord_1743944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743944).length < 2 ^ (prefixWord ++ tailWord_1743944).sum := by decide
  have hdescent : baseEnd_1743944 < baseStart_1743944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744008 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_1744008 : Nat := 118140960795 + 1744008 * 2 ^ 59
def prefixEnd_1744008 : Nat := 4983230072969 + 3 ^ 40 * 1744008 * 2
def baseEnd_1744008 : Nat := 597009579524345196252973

theorem tailTrace_1744008 : CollatzResearch.WordTrace tailWord_1744008 prefixEnd_1744008 597009579524345196252973 := by
  unfold tailWord_1744008
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804598732882171849116339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42406131643842895798821785 31804598732882171849116339)
  ·
    refine ⟨47706898099323257773674509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31804598732882171849116339 47706898099323257773674509)
    ·
      refine ⟨17890086787246221665127941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47706898099323257773674509 17890086787246221665127941)
      ·
        refine ⟨3354391272608666562211489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17890086787246221665127941 3354391272608666562211489)
        ·
          refine ⟨2515793454456499921658617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354391272608666562211489 2515793454456499921658617)
          ·
            refine ⟨1886845090842374941243963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515793454456499921658617 1886845090842374941243963)
            ·
              refine ⟨2830267636263562411865945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886845090842374941243963 2830267636263562411865945)
              ·
                refine ⟨2122700727197671808899459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830267636263562411865945 2122700727197671808899459)
                ·
                  refine ⟨3184051090796507713349189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122700727197671808899459 3184051090796507713349189)
                  ·
                    refine ⟨597009579524345196252973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184051090796507713349189 597009579524345196252973)
                    ·
                      rfl

theorem cell22_1744008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_1744008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744008 prefixEnd_1744008 := by exact prefixLift 1744008
  have htrace : WordTrace (prefixWord ++ tailWord_1744008) baseStart_1744008 baseEnd_1744008 := by
    simpa [prefixWord, tailWord_1744008, baseEnd_1744008] using wordTrace_append hprefix tailTrace_1744008
  have hstable : (prefixWord ++ tailWord_1744008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744008).length < 2 ^ (prefixWord ++ tailWord_1744008).sum := by decide
  have hdescent : baseEnd_1744008 < baseStart_1744008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744034 : List Nat := [3, 3, 1, 3, 2, 10]
def baseStart_1744034 : Nat := 118140960795 + 1744034 * 2 ^ 59
def prefixEnd_1744034 : Nat := 4983230072969 + 3 ^ 40 * 1744034 * 2
def baseEnd_1744034 : Nat := 7370598516736911050653

theorem tailTrace_1744034 : CollatzResearch.WordTrace tailWord_1744034 prefixEnd_1744034 7370598516736911050653 := by
  unfold tailWord_1744034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902536440917537534669789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42406763842446766759119437 15902536440917537534669789)
  ·
    refine ⟨5963451165344076575501171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15902536440917537534669789 5963451165344076575501171)
    ·
      refine ⟨8945176748016114863251757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5963451165344076575501171 8945176748016114863251757)
      ·
        refine ⟨3354441280506043073719409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8945176748016114863251757 3354441280506043073719409)
        ·
          refine ⟨2515830960379532305289557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354441280506043073719409 2515830960379532305289557)
          ·
            refine ⟨7370598516736911050653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2515830960379532305289557 7370598516736911050653)
            ·
              rfl

theorem cell22_1744034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 10].length) (baseStart_1744034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744034 prefixEnd_1744034 := by exact prefixLift 1744034
  have htrace : WordTrace (prefixWord ++ tailWord_1744034) baseStart_1744034 baseEnd_1744034 := by
    simpa [prefixWord, tailWord_1744034, baseEnd_1744034] using wordTrace_append hprefix tailTrace_1744034
  have hstable : (prefixWord ++ tailWord_1744034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744034).length < 2 ^ (prefixWord ++ tailWord_1744034).sum := by decide
  have hdescent : baseEnd_1744034 < baseStart_1744034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744047 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1744047 : Nat := 118140960795 + 1744047 * 2 ^ 59
def prefixEnd_1744047 : Nat := 4983230072969 + 3 ^ 40 * 1744047 * 2
def baseEnd_1744047 : Nat := 597022930021362094527853

theorem tailTrace_1744047 : CollatzResearch.WordTrace tailWord_1744047 prefixEnd_1744047 597022930021362094527853 := by
  unfold tailWord_1744047
  simp only [CollatzResearch.WordTrace]
  refine ⟨63610619912623053358902395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42407079941748702239268263 63610619912623053358902395)
  ·
    refine ⟨95415929868934580038353593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63610619912623053358902395 95415929868934580038353593)
    ·
      refine ⟨71561947401700935028765195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95415929868934580038353593 71561947401700935028765195)
      ·
        refine ⟨107342921102551402543147793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71561947401700935028765195 107342921102551402543147793)
        ·
          refine ⟨80507190826913551907360845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107342921102551402543147793 80507190826913551907360845)
          ·
            refine ⟨30190196560092581965260317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80507190826913551907360845 30190196560092581965260317)
            ·
              refine ⟨11321323710034718236972619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30190196560092581965260317 11321323710034718236972619)
              ·
                refine ⟨16981985565052077355458929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321323710034718236972619 16981985565052077355458929)
                ·
                  refine ⟨12736489173789058016594197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16981985565052077355458929 12736489173789058016594197)
                  ·
                    refine ⟨597022930021362094527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12736489173789058016594197 597022930021362094527853)
                    ·
                      rfl

theorem cell22_1744047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1744047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744047 prefixEnd_1744047 := by exact prefixLift 1744047
  have htrace : WordTrace (prefixWord ++ tailWord_1744047) baseStart_1744047 baseEnd_1744047 := by
    simpa [prefixWord, tailWord_1744047, baseEnd_1744047] using wordTrace_append hprefix tailTrace_1744047
  have hstable : (prefixWord ++ tailWord_1744047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744047).length < 2 ^ (prefixWord ++ tailWord_1744047).sum := by decide
  have hdescent : baseEnd_1744047 < baseStart_1744047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744070 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1744070 : Nat := 118140960795 + 1744070 * 2 ^ 59
def prefixEnd_1744070 : Nat := 4983230072969 + 3 ^ 40 * 1744070 * 2
def baseEnd_1744070 : Nat := 597030803391397701202783

theorem tailTrace_1744070 : CollatzResearch.WordTrace tailWord_1744070 prefixEnd_1744070 597030803391397701202783 := by
  unfold tailWord_1744070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987858087235616508968427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42407639194359818857993109 1987858087235616508968427)
  ·
    refine ⟨2981787130853424763452641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987858087235616508968427 2981787130853424763452641)
    ·
      refine ⟨2236340348140068572589481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981787130853424763452641 2236340348140068572589481)
      ·
        refine ⟨1677255261105051429442111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2236340348140068572589481 1677255261105051429442111)
        ·
          refine ⟨2515882891657577144163167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677255261105051429442111 2515882891657577144163167)
          ·
            refine ⟨3773824337486365716244751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515882891657577144163167 3773824337486365716244751)
            ·
              refine ⟨5660736506229548574367127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773824337486365716244751 5660736506229548574367127)
              ·
                refine ⟨8491104759344322861550691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660736506229548574367127 8491104759344322861550691)
                ·
                  refine ⟨12736657139016484292326037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491104759344322861550691 12736657139016484292326037)
                  ·
                    refine ⟨597030803391397701202783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12736657139016484292326037 597030803391397701202783)
                    ·
                      rfl

theorem cell22_1744070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1744070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744070 prefixEnd_1744070 := by exact prefixLift 1744070
  have htrace : WordTrace (prefixWord ++ tailWord_1744070) baseStart_1744070 baseEnd_1744070 := by
    simpa [prefixWord, tailWord_1744070, baseEnd_1744070] using wordTrace_append hprefix tailTrace_1744070
  have hstable : (prefixWord ++ tailWord_1744070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744070).length < 2 ^ (prefixWord ++ tailWord_1744070).sum := by decide
  have hdescent : baseEnd_1744070 < baseStart_1744070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744096 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_1744096 : Nat := 118140960795 + 1744096 * 2 ^ 59
def prefixEnd_1744096 : Nat := 4983230072969 + 3 ^ 40 * 1744096 * 2
def baseEnd_1744096 : Nat := 199013234574247433350901

theorem tailTrace_1744096 : CollatzResearch.WordTrace tailWord_1744096 prefixEnd_1744096 199013234574247433350901 := by
  unfold tailWord_1744096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31806203544722767363718071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42408271392963689818290761 31806203544722767363718071)
  ·
    refine ⟨47709305317084151045577107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31806203544722767363718071 47709305317084151045577107)
    ·
      refine ⟨71563957975626226568365661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47709305317084151045577107 71563957975626226568365661)
      ·
        refine ⟨26836484240859834963137123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71563957975626226568365661 26836484240859834963137123)
        ·
          refine ⟨40254726361289752444705685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26836484240859834963137123 40254726361289752444705685)
          ·
            refine ⟨1886940298185457145845579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40254726361289752444705685 1886940298185457145845579)
            ·
              refine ⟨2830410447278185718768369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886940298185457145845579 2830410447278185718768369)
              ·
                refine ⟨2122807835458639289076277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830410447278185718768369 2122807835458639289076277)
                ·
                  refine ⟨199013234574247433350901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122807835458639289076277 199013234574247433350901)
                  ·
                    rfl

theorem cell22_1744096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_1744096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744096 prefixEnd_1744096 := by exact prefixLift 1744096
  have htrace : WordTrace (prefixWord ++ tailWord_1744096) baseStart_1744096 baseEnd_1744096 := by
    simpa [prefixWord, tailWord_1744096, baseEnd_1744096] using wordTrace_append hprefix tailTrace_1744096
  have hstable : (prefixWord ++ tailWord_1744096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744096).length < 2 ^ (prefixWord ++ tailWord_1744096).sum := by decide
  have hdescent : baseEnd_1744096 < baseStart_1744096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744156 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1744156 : Nat := 118140960795 + 1744156 * 2 ^ 59
def prefixEnd_1744156 : Nat := 4983230072969 + 3 ^ 40 * 1744156 * 2
def baseEnd_1744156 : Nat := 597060242948922143552519

theorem tailTrace_1744156 : CollatzResearch.WordTrace tailWord_1744156 prefixEnd_1744156 597060242948922143552519 := by
  unfold tailWord_1744156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31807297734614082487310161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42409730312818776649746881 31807297734614082487310161)
  ·
    refine ⟨23855473300960561865482621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31807297734614082487310161 23855473300960561865482621)
    ·
      refine ⟨8945802487860210699555983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23855473300960561865482621 8945802487860210699555983)
      ·
        refine ⟨13418703731790316049333975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945802487860210699555983 13418703731790316049333975)
        ·
          refine ⟨20128055597685474074000963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418703731790316049333975 20128055597685474074000963)
          ·
            refine ⟨30192083396528211111001445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20128055597685474074000963 30192083396528211111001445)
            ·
              refine ⟨5661015636849039583312771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30192083396528211111001445 5661015636849039583312771)
              ·
                refine ⟨8491523455273559374969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661015636849039583312771 8491523455273559374969157)
                ·
                  refine ⟨1592160647863792382806717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8491523455273559374969157 1592160647863792382806717)
                  ·
                    refine ⟨597060242948922143552519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1592160647863792382806717 597060242948922143552519)
                    ·
                      rfl

theorem cell22_1744156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1744156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744156 prefixEnd_1744156 := by exact prefixLift 1744156
  have htrace : WordTrace (prefixWord ++ tailWord_1744156) baseStart_1744156 baseEnd_1744156 := by
    simpa [prefixWord, tailWord_1744156, baseEnd_1744156] using wordTrace_append hprefix tailTrace_1744156
  have hstable : (prefixWord ++ tailWord_1744156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744156).length < 2 ^ (prefixWord ++ tailWord_1744156).sum := by decide
  have hdescent : baseEnd_1744156 < baseStart_1744156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744265 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 5]
def baseStart_1744265 : Nat := 118140960795 + 1744265 * 2 ^ 59
def prefixEnd_1744265 : Nat := 4983230072969 + 3 ^ 40 * 1744265 * 2
def baseEnd_1744265 : Nat := 199032518625494064192395

theorem tailTrace_1744265 : CollatzResearch.WordTrace tailWord_1744265 prefixEnd_1744265 199032518625494064192395 := by
  unfold tailWord_1744265
  simp only [CollatzResearch.WordTrace]
  refine ⟨63618571025833276590338249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42412380683888851060225499 63618571025833276590338249)
  ·
    refine ⟨47713928269374957442753687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63618571025833276590338249 47713928269374957442753687)
    ·
      refine ⟨71570892404062436164130531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47713928269374957442753687 71570892404062436164130531)
      ·
        refine ⟨107356338606093654246195797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71570892404062436164130531 107356338606093654246195797)
        ·
          refine ⟨1258082093040160010697607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 107356338606093654246195797 1258082093040160010697607)
          ·
            refine ⟨1887123139560240016046411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258082093040160010697607 1887123139560240016046411)
            ·
              refine ⟨2830684709340360024069617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887123139560240016046411 2830684709340360024069617)
              ·
                refine ⟨2123013532005270018052213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830684709340360024069617 2123013532005270018052213)
                ·
                  refine ⟨199032518625494064192395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123013532005270018052213 199032518625494064192395)
                  ·
                    rfl

theorem cell22_1744265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_1744265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744265 prefixEnd_1744265 := by exact prefixLift 1744265
  have htrace : WordTrace (prefixWord ++ tailWord_1744265) baseStart_1744265 baseEnd_1744265 := by
    simpa [prefixWord, tailWord_1744265, baseEnd_1744265] using wordTrace_append hprefix tailTrace_1744265
  have hstable : (prefixWord ++ tailWord_1744265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744265).length < 2 ^ (prefixWord ++ tailWord_1744265).sum := by decide
  have hdescent : baseEnd_1744265 < baseStart_1744265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744342 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1744342 : Nat := 118140960795 + 1744342 * 2 ^ 59
def prefixEnd_1744342 : Nat := 4983230072969 + 3 ^ 40 * 1744342 * 2
def baseEnd_1744342 : Nat := 597123914550079658401949

theorem tailTrace_1744342 : CollatzResearch.WordTrace tailWord_1744342 prefixEnd_1744342 597123914550079658401949 := by
  unfold tailWord_1744342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976336215409644921305705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42414252964369545827260853 3976336215409644921305705)
  ·
    refine ⟨2982252161557233690979279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3976336215409644921305705 2982252161557233690979279)
    ·
      refine ⟨4473378242335850536468919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2982252161557233690979279 4473378242335850536468919)
      ·
        refine ⟨6710067363503775804703379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473378242335850536468919 6710067363503775804703379)
        ·
          refine ⟨10065101045255663707055069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710067363503775804703379 10065101045255663707055069)
          ·
            refine ⟨3774412891970873890145651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10065101045255663707055069 3774412891970873890145651)
            ·
              refine ⟨5661619337956310835218477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774412891970873890145651 5661619337956310835218477)
              ·
                refine ⟨2123107251733616563206929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5661619337956310835218477 2123107251733616563206929)
                ·
                  refine ⟨1592330438800212422405197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123107251733616563206929 1592330438800212422405197)
                  ·
                    refine ⟨597123914550079658401949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1592330438800212422405197 597123914550079658401949)
                    ·
                      rfl

theorem cell22_1744342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1744342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744342 prefixEnd_1744342 := by exact prefixLift 1744342
  have htrace : WordTrace (prefixWord ++ tailWord_1744342) baseStart_1744342 baseEnd_1744342 := by
    simpa [prefixWord, tailWord_1744342, baseEnd_1744342] using wordTrace_append hprefix tailTrace_1744342
  have hstable : (prefixWord ++ tailWord_1744342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744342).length < 2 ^ (prefixWord ++ tailWord_1744342).sum := by decide
  have hdescent : baseEnd_1744342 < baseStart_1744342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744413 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1744413 : Nat := 118140960795 + 1744413 * 2 ^ 59
def prefixEnd_1744413 : Nat := 4983230072969 + 3 ^ 40 * 1744413 * 2
def baseEnd_1744413 : Nat := 597148219301059139876731

theorem tailTrace_1744413 : CollatzResearch.WordTrace tailWord_1744413 prefixEnd_1744413 597148219301059139876731 := by
  unfold tailWord_1744413
  simp only [CollatzResearch.WordTrace]
  refine ⟨63623969029297097866725893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42415979352864731911150595 63623969029297097866725893)
  ·
    refine ⟨11929494192993205850011105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63623969029297097866725893 11929494192993205850011105)
    ·
      refine ⟨8947120644744904387508329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11929494192993205850011105 8947120644744904387508329)
      ·
        refine ⟨6710340483558678290631247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8947120644744904387508329 6710340483558678290631247)
        ·
          refine ⟨10065510725338017435946871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710340483558678290631247 10065510725338017435946871)
          ·
            refine ⟨15098266088007026153920307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065510725338017435946871 15098266088007026153920307)
            ·
              refine ⟨22647399132010539230880461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15098266088007026153920307 22647399132010539230880461)
              ·
                refine ⟨8492774674503952211580173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22647399132010539230880461 8492774674503952211580173)
                ·
                  refine ⟨3184790502938982079342565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8492774674503952211580173 3184790502938982079342565)
                  ·
                    refine ⟨597148219301059139876731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3184790502938982079342565 597148219301059139876731)
                    ·
                      rfl

theorem cell22_1744413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1744413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744413 prefixEnd_1744413 := by exact prefixLift 1744413
  have htrace : WordTrace (prefixWord ++ tailWord_1744413) baseStart_1744413 baseEnd_1744413 := by
    simpa [prefixWord, tailWord_1744413, baseEnd_1744413] using wordTrace_append hprefix tailTrace_1744413
  have hstable : (prefixWord ++ tailWord_1744413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744413).length < 2 ^ (prefixWord ++ tailWord_1744413).sum := by decide
  have hdescent : baseEnd_1744413 < baseStart_1744413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744445 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 6]
def baseStart_1744445 : Nat := 118140960795 + 1744445 * 2 ^ 59
def prefixEnd_1744445 : Nat := 4983230072969 + 3 ^ 40 * 1744445 * 2
def baseEnd_1744445 : Nat := 199053057851673907692211

theorem tailTrace_1744445 : CollatzResearch.WordTrace tailWord_1744445 prefixEnd_1744445 199053057851673907692211 := by
  unfold tailWord_1744445
  simp only [CollatzResearch.WordTrace]
  refine ⟨63625136165181167331890789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42416757443454111554593859 63625136165181167331890789)
  ·
    refine ⟨11929713030971468874729523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63625136165181167331890789 11929713030971468874729523)
    ·
      refine ⟨17894569546457203312094285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929713030971468874729523 17894569546457203312094285)
      ·
        refine ⟨6710463579921451242035357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17894569546457203312094285 6710463579921451242035357)
        ·
          refine ⟨2516423842470544215763259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6710463579921451242035357 2516423842470544215763259)
          ·
            refine ⟨3774635763705816323644889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516423842470544215763259 3774635763705816323644889)
            ·
              refine ⟨2830976822779362242733667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3774635763705816323644889 2830976822779362242733667)
              ·
                refine ⟨4246465234169043364100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830976822779362242733667 4246465234169043364100501)
                ·
                  refine ⟨199053057851673907692211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4246465234169043364100501 199053057851673907692211)
                  ·
                    rfl

theorem cell22_1744445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_1744445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744445 prefixEnd_1744445 := by exact prefixLift 1744445
  have htrace : WordTrace (prefixWord ++ tailWord_1744445) baseStart_1744445 baseEnd_1744445 := by
    simpa [prefixWord, tailWord_1744445, baseEnd_1744445] using wordTrace_append hprefix tailTrace_1744445
  have hstable : (prefixWord ++ tailWord_1744445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744445).length < 2 ^ (prefixWord ++ tailWord_1744445).sum := by decide
  have hdescent : baseEnd_1744445 < baseStart_1744445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744460 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_1744460 : Nat := 118140960795 + 1744460 * 2 ^ 59
def prefixEnd_1744460 : Nat := 4983230072969 + 3 ^ 40 * 1744460 * 2
def baseEnd_1744460 : Nat := 597164308361566683951587

theorem tailTrace_1744460 : CollatzResearch.WordTrace tailWord_1744460 prefixEnd_1744460 597164308361566683951587 := by
  unfold tailWord_1744460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812841630063412446843417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42417122173417883262457889 31812841630063412446843417)
  ·
    refine ⟨23859631222547559335132563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31812841630063412446843417 23859631222547559335132563)
    ·
      refine ⟨35789446833821339002698845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23859631222547559335132563 35789446833821339002698845)
      ·
        refine ⟨13421042562683002126012067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35789446833821339002698845 13421042562683002126012067)
        ·
          refine ⟨20131563844024503189018101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421042562683002126012067 20131563844024503189018101)
          ·
            refine ⟨1887334110377297173970447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20131563844024503189018101 1887334110377297173970447)
            ·
              refine ⟨2831001165565945760955671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887334110377297173970447 2831001165565945760955671)
              ·
                refine ⟨4246501748348918641433507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831001165565945760955671 4246501748348918641433507)
                ·
                  refine ⟨6369752622523377962150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246501748348918641433507 6369752622523377962150261)
                  ·
                    refine ⟨597164308361566683951587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6369752622523377962150261 597164308361566683951587)
                    ·
                      rfl

theorem cell22_1744460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_1744460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744460 prefixEnd_1744460 := by exact prefixLift 1744460
  have htrace : WordTrace (prefixWord ++ tailWord_1744460) baseStart_1744460 baseEnd_1744460 := by
    simpa [prefixWord, tailWord_1744460, baseEnd_1744460] using wordTrace_append hprefix tailTrace_1744460
  have hstable : (prefixWord ++ tailWord_1744460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744460).length < 2 ^ (prefixWord ++ tailWord_1744460).sum := by decide
  have hdescent : baseEnd_1744460 < baseStart_1744460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744563 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 6]
def baseStart_1744563 : Nat := 118140960795 + 1744563 * 2 ^ 59
def prefixEnd_1744563 : Nat := 4983230072969 + 3 ^ 40 * 1744563 * 2
def baseEnd_1744563 : Nat := 199066522455502916208757

theorem tailTrace_1744563 : CollatzResearch.WordTrace tailWord_1744563 prefixEnd_1744563 199066522455502916208757 := by
  unfold tailWord_1744563
  simp only [CollatzResearch.WordTrace]
  refine ⟨63629439978753673484686343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42419626652502448989790895 63629439978753673484686343)
  ·
    refine ⟨95444159968130510227029515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63629439978753673484686343 95444159968130510227029515)
    ·
      refine ⟨143166239952195765340544273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95444159968130510227029515 143166239952195765340544273)
      ·
        refine ⟨107374679964146824005408205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143166239952195765340544273 107374679964146824005408205)
        ·
          refine ⟨40265504986555059002028077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107374679964146824005408205 40265504986555059002028077)
          ·
            refine ⟨15099564369958147125760529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40265504986555059002028077 15099564369958147125760529)
            ·
              refine ⟨11324673277468610344320397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15099564369958147125760529 11324673277468610344320397)
              ·
                refine ⟨4246752479050728879120149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11324673277468610344320397 4246752479050728879120149)
                ·
                  refine ⟨199066522455502916208757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4246752479050728879120149 199066522455502916208757)
                  ·
                    rfl

theorem cell22_1744563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_1744563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744563 prefixEnd_1744563 := by exact prefixLift 1744563
  have htrace : WordTrace (prefixWord ++ tailWord_1744563) baseStart_1744563 baseEnd_1744563 := by
    simpa [prefixWord, tailWord_1744563, baseEnd_1744563] using wordTrace_append hprefix tailTrace_1744563
  have hstable : (prefixWord ++ tailWord_1744563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744563).length < 2 ^ (prefixWord ++ tailWord_1744563).sum := by decide
  have hdescent : baseEnd_1744563 < baseStart_1744563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744580 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1744580 : Nat := 118140960795 + 1744580 * 2 ^ 59
def prefixEnd_1744580 : Nat := 4983230072969 + 3 ^ 40 * 1744580 * 2
def baseEnd_1744580 : Nat := 199068462271308790317073

theorem tailTrace_1744580 : CollatzResearch.WordTrace tailWord_1744580 prefixEnd_1744580 199068462271308790317073 := by
  unfold tailWord_1744580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31815030009846042694027597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42420040013128056925370129 31815030009846042694027597)
  ·
    refine ⟨11930636253692266010260349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31815030009846042694027597 11930636253692266010260349)
    ·
      refine ⟨4473988595134599753847631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11930636253692266010260349 4473988595134599753847631)
      ·
        refine ⟨6710982892701899630771447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473988595134599753847631 6710982892701899630771447)
        ·
          refine ⟨10066474339052849446157171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710982892701899630771447 10066474339052849446157171)
          ·
            refine ⟨15099711508579274169235757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066474339052849446157171 15099711508579274169235757)
            ·
              refine ⟨5662391815717227813463409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15099711508579274169235757 5662391815717227813463409)
              ·
                refine ⟨4246793861787920860097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662391815717227813463409 4246793861787920860097557)
                ·
                  refine ⟨199068462271308790317073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4246793861787920860097557 199068462271308790317073)
                  ·
                    rfl

theorem cell22_1744580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1744580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744580 prefixEnd_1744580 := by exact prefixLift 1744580
  have htrace : WordTrace (prefixWord ++ tailWord_1744580) baseStart_1744580 baseEnd_1744580 := by
    simpa [prefixWord, tailWord_1744580, baseEnd_1744580] using wordTrace_append hprefix tailTrace_1744580
  have hstable : (prefixWord ++ tailWord_1744580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744580).length < 2 ^ (prefixWord ++ tailWord_1744580).sum := by decide
  have hdescent : baseEnd_1744580 < baseStart_1744580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744730 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1744730 : Nat := 118140960795 + 1744730 * 2 ^ 59
def prefixEnd_1744730 : Nat := 4983230072969 + 3 ^ 40 * 1744730 * 2
def baseEnd_1744730 : Nat := 597256734879375979700759

theorem tailTrace_1744730 : CollatzResearch.WordTrace tailWord_1744730 prefixEnd_1744730 597256734879375979700759 := by
  unfold tailWord_1744730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908882742287165251503911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42423687312765774004010429 15908882742287165251503911)
  ·
    refine ⟨23863324113430747877255867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15908882742287165251503911 23863324113430747877255867)
    ·
      refine ⟨35794986170146121815883801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863324113430747877255867 35794986170146121815883801)
      ·
        refine ⟨26846239627609591361912851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35794986170146121815883801 26846239627609591361912851)
        ·
          refine ⟨40269359441414387042869277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846239627609591361912851 40269359441414387042869277)
          ·
            refine ⟨15101009790530395141075979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40269359441414387042869277 15101009790530395141075979)
            ·
              refine ⟨22651514685795592711613969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101009790530395141075979 22651514685795592711613969)
              ·
                refine ⟨16988636014346694533710477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22651514685795592711613969 16988636014346694533710477)
                ·
                  refine ⟨6370738505380010450141429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16988636014346694533710477 6370738505380010450141429)
                  ·
                    refine ⟨597256734879375979700759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6370738505380010450141429 597256734879375979700759)
                    ·
                      rfl

theorem cell22_1744730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1744730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744730 prefixEnd_1744730 := by exact prefixLift 1744730
  have htrace : WordTrace (prefixWord ++ tailWord_1744730) baseStart_1744730 baseEnd_1744730 := by
    simpa [prefixWord, tailWord_1744730, baseEnd_1744730] using wordTrace_append hprefix tailTrace_1744730
  have hstable : (prefixWord ++ tailWord_1744730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744730).length < 2 ^ (prefixWord ++ tailWord_1744730).sum := by decide
  have hdescent : baseEnd_1744730 < baseStart_1744730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744745 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1744745 : Nat := 118140960795 + 1744745 * 2 ^ 59
def prefixEnd_1744745 : Nat := 4983230072969 + 3 ^ 40 * 1744745 * 2
def baseEnd_1744745 : Nat := 597261869685920940575713

theorem tailTrace_1744745 : CollatzResearch.WordTrace tailWord_1744745 prefixEnd_1744745 597261869685920940575713 := by
  unfold tailWord_1744745
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636078064094318567811689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42424052042729545711874459 63636078064094318567811689)
  ·
    refine ⟨47727058548070738925858767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63636078064094318567811689 47727058548070738925858767)
    ·
      refine ⟨71590587822106108388788151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47727058548070738925858767 71590587822106108388788151)
      ·
        refine ⟨107385881733159162583182227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71590587822106108388788151 107385881733159162583182227)
        ·
          refine ⟨161078822599738743874773341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107385881733159162583182227 161078822599738743874773341)
          ·
            refine ⟨60404558474902028953040003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161078822599738743874773341 60404558474902028953040003)
            ·
              refine ⟨90606837712353043429560005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60404558474902028953040003 90606837712353043429560005)
              ·
                refine ⟨16988782071066195643042501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90606837712353043429560005 16988782071066195643042501)
                ·
                  refine ⟨3185396638324911683070469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16988782071066195643042501 3185396638324911683070469)
                  ·
                    refine ⟨597261869685920940575713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185396638324911683070469 597261869685920940575713)
                    ·
                      rfl

theorem cell22_1744745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1744745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744745 prefixEnd_1744745 := by exact prefixLift 1744745
  have htrace : WordTrace (prefixWord ++ tailWord_1744745) baseStart_1744745 baseEnd_1744745 := by
    simpa [prefixWord, tailWord_1744745, baseEnd_1744745] using wordTrace_append hprefix tailTrace_1744745
  have hstable : (prefixWord ++ tailWord_1744745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744745).length < 2 ^ (prefixWord ++ tailWord_1744745).sum := by decide
  have hdescent : baseEnd_1744745 < baseStart_1744745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744762 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1744762 : Nat := 118140960795 + 1744762 * 2 ^ 59
def prefixEnd_1744762 : Nat := 4983230072969 + 3 ^ 40 * 1744762 * 2
def baseEnd_1744762 : Nat := 597267689133338562900661

theorem tailTrace_1744762 : CollatzResearch.WordTrace tailWord_1744762 prefixEnd_1744762 597267689133338562900661 := by
  unfold tailWord_1744762
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909174526258182617795135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42424465403355153647453693 15909174526258182617795135)
  ·
    refine ⟨23863761789387273926692703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909174526258182617795135 23863761789387273926692703)
    ·
      refine ⟨35795642684080910890039055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863761789387273926692703 35795642684080910890039055)
      ·
        refine ⟨53693464026121366335058583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35795642684080910890039055 53693464026121366335058583)
        ·
          refine ⟨80540196039182049502587875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53693464026121366335058583 80540196039182049502587875)
          ·
            refine ⟨120810294058773074253881813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80540196039182049502587875 120810294058773074253881813)
            ·
              refine ⟨2831491267002493927825355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120810294058773074253881813 2831491267002493927825355)
              ·
                refine ⟨4247236900503740891738033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831491267002493927825355 4247236900503740891738033)
                ·
                  refine ⟨3185427675377805668803525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4247236900503740891738033 3185427675377805668803525)
                  ·
                    refine ⟨597267689133338562900661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3185427675377805668803525 597267689133338562900661)
                    ·
                      rfl

theorem cell22_1744762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1744762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744762 prefixEnd_1744762 := by exact prefixLift 1744762
  have htrace : WordTrace (prefixWord ++ tailWord_1744762) baseStart_1744762 baseEnd_1744762 := by
    simpa [prefixWord, tailWord_1744762, baseEnd_1744762] using wordTrace_append hprefix tailTrace_1744762
  have hstable : (prefixWord ++ tailWord_1744762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744762).length < 2 ^ (prefixWord ++ tailWord_1744762).sum := by decide
  have hdescent : baseEnd_1744762 < baseStart_1744762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744766 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1744766 : Nat := 118140960795 + 1744766 * 2 ^ 59
def prefixEnd_1744766 : Nat := 4983230072969 + 3 ^ 40 * 1744766 * 2
def baseEnd_1744766 : Nat := 199089686138361295266883

theorem tailTrace_1744766 : CollatzResearch.WordTrace tailWord_1744766 prefixEnd_1744766 199089686138361295266883 := by
  unfold tailWord_1744766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954605499627279894290769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42424562664678826102884101 7954605499627279894290769)
  ·
    refine ⟨5965954124720459920718077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7954605499627279894290769 5965954124720459920718077)
    ·
      refine ⟨2237232796770172470269279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5965954124720459920718077 2237232796770172470269279)
      ·
        refine ⟨3355849195155258705403919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237232796770172470269279 3355849195155258705403919)
        ·
          refine ⟨5033773792732888058105879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3355849195155258705403919 5033773792732888058105879)
          ·
            refine ⟨7550660689099332087158819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033773792732888058105879 7550660689099332087158819)
            ·
              refine ⟨11325991033648998130738229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550660689099332087158819 11325991033648998130738229)
              ·
                refine ⟨1061811659404593574756709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11325991033648998130738229 1061811659404593574756709)
                ·
                  refine ⟨199089686138361295266883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061811659404593574756709 199089686138361295266883)
                  ·
                    rfl

theorem cell22_1744766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1744766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744766 prefixEnd_1744766 := by exact prefixLift 1744766
  have htrace : WordTrace (prefixWord ++ tailWord_1744766) baseStart_1744766 baseEnd_1744766 := by
    simpa [prefixWord, tailWord_1744766, baseEnd_1744766] using wordTrace_append hprefix tailTrace_1744766
  have hstable : (prefixWord ++ tailWord_1744766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744766).length < 2 ^ (prefixWord ++ tailWord_1744766).sum := by decide
  have hdescent : baseEnd_1744766 < baseStart_1744766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744798 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1744798 : Nat := 118140960795 + 1744798 * 2 ^ 59
def prefixEnd_1744798 : Nat := 4983230072969 + 3 ^ 40 * 1744798 * 2
def baseEnd_1744798 : Nat := 597280012669046469000551

theorem tailTrace_1744798 : CollatzResearch.WordTrace tailWord_1744798 prefixEnd_1744798 597280012669046469000551 := by
  unfold tailWord_1744798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954751391612788577436381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42425340755268205746327365 7954751391612788577436381)
  ·
    refine ⟨2983031771854795716538643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7954751391612788577436381 2983031771854795716538643)
    ·
      refine ⟨4474547657782193574807965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983031771854795716538643 4474547657782193574807965)
      ·
        refine ⟨1677955371668322590552987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4474547657782193574807965 1677955371668322590552987)
        ·
          refine ⟨2516933057502483885829481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677955371668322590552987 2516933057502483885829481)
          ·
            refine ⟨1887699793126862914372111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2516933057502483885829481 1887699793126862914372111)
            ·
              refine ⟨2831549689690294371558167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887699793126862914372111 2831549689690294371558167)
              ·
                refine ⟨4247324534535441557337251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831549689690294371558167 4247324534535441557337251)
                ·
                  refine ⟨6370986801803162336005877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247324534535441557337251 6370986801803162336005877)
                  ·
                    refine ⟨597280012669046469000551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6370986801803162336005877 597280012669046469000551)
                    ·
                      rfl

theorem cell22_1744798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1744798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744798 prefixEnd_1744798 := by exact prefixLift 1744798
  have htrace : WordTrace (prefixWord ++ tailWord_1744798) baseStart_1744798 baseEnd_1744798 := by
    simpa [prefixWord, tailWord_1744798, baseEnd_1744798] using wordTrace_append hprefix tailTrace_1744798
  have hstable : (prefixWord ++ tailWord_1744798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744798).length < 2 ^ (prefixWord ++ tailWord_1744798).sum := by decide
  have hdescent : baseEnd_1744798 < baseStart_1744798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744901 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 4]
def baseStart_1744901 : Nat := 118140960795 + 1744901 * 2 ^ 59
def prefixEnd_1744901 : Nat := 4983230072969 + 3 ^ 40 * 1744901 * 2
def baseEnd_1744901 : Nat := 199105090557996177891745

theorem tailTrace_1744901 : CollatzResearch.WordTrace tailWord_1744901 prefixEnd_1744901 199105090557996177891745 := by
  unfold tailWord_1744901
  simp only [CollatzResearch.WordTrace]
  refine ⟨63641767851529157210490557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42427845234352771473660371 63641767851529157210490557)
  ·
    refine ⟨23865662944323433953933959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63641767851529157210490557 23865662944323433953933959)
    ·
      refine ⟨35798494416485150930900939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23865662944323433953933959 35798494416485150930900939)
      ·
        refine ⟨53697741624727726396351409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35798494416485150930900939 53697741624727726396351409)
        ·
          refine ⟨40273306218545794797263557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53697741624727726396351409 40273306218545794797263557)
          ·
            refine ⟨7551244915977336524486917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40273306218545794797263557 7551244915977336524486917)
            ·
              refine ⟨1415858421745750598341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7551244915977336524486917 1415858421745750598341297)
              ·
                refine ⟨1061893816309312948755973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415858421745750598341297 1061893816309312948755973)
                ·
                  refine ⟨199105090557996177891745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061893816309312948755973 199105090557996177891745)
                  ·
                    rfl

theorem cell22_1744901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_1744901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744901 prefixEnd_1744901 := by exact prefixLift 1744901
  have htrace : WordTrace (prefixWord ++ tailWord_1744901) baseStart_1744901 baseEnd_1744901 := by
    simpa [prefixWord, tailWord_1744901, baseEnd_1744901] using wordTrace_append hprefix tailTrace_1744901
  have hstable : (prefixWord ++ tailWord_1744901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744901).length < 2 ^ (prefixWord ++ tailWord_1744901).sum := by decide
  have hdescent : baseEnd_1744901 < baseStart_1744901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744961 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1744961 : Nat := 118140960795 + 1744961 * 2 ^ 59
def prefixEnd_1744961 : Nat := 4983230072969 + 3 ^ 40 * 1744961 * 2
def baseEnd_1744961 : Nat := 597335810900168377175051

theorem tailTrace_1744961 : CollatzResearch.WordTrace tailWord_1744961 prefixEnd_1744961 597335810900168377175051 := by
  unfold tailWord_1744961
  simp only [CollatzResearch.WordTrace]
  refine ⟨63643956231311787457674737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42429304154207858305116491 63643956231311787457674737)
  ·
    refine ⟨47732967173483840593256053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63643956231311787457674737 47732967173483840593256053)
    ·
      refine ⟨4474965672514110055617755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47732967173483840593256053 4474965672514110055617755)
      ·
        refine ⟨6712448508771165083426633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474965672514110055617755 6712448508771165083426633)
        ·
          refine ⟨5034336381578373812569975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6712448508771165083426633 5034336381578373812569975)
          ·
            refine ⟨7551504572367560718854963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034336381578373812569975 7551504572367560718854963)
            ·
              refine ⟨11327256858551341078282445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551504572367560718854963 11327256858551341078282445)
              ·
                refine ⟨4247721321956752904355917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11327256858551341078282445 4247721321956752904355917)
                ·
                  refine ⟨1592895495733782339133469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4247721321956752904355917 1592895495733782339133469)
                  ·
                    refine ⟨597335810900168377175051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1592895495733782339133469 597335810900168377175051)
                    ·
                      rfl

theorem cell22_1744961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1744961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1744961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1744961 prefixEnd_1744961 := by exact prefixLift 1744961
  have htrace : WordTrace (prefixWord ++ tailWord_1744961) baseStart_1744961 baseEnd_1744961 := by
    simpa [prefixWord, tailWord_1744961, baseEnd_1744961] using wordTrace_append hprefix tailTrace_1744961
  have hstable : (prefixWord ++ tailWord_1744961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744961).length < 2 ^ (prefixWord ++ tailWord_1744961).sum := by decide
  have hdescent : baseEnd_1744961 < baseStart_1744961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745025 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 5]
def baseStart_1745025 : Nat := 118140960795 + 1745025 * 2 ^ 59
def prefixEnd_1745025 : Nat := 4983230072969 + 3 ^ 40 * 1745025 * 2
def baseEnd_1745025 : Nat := 199119239802697847858285

theorem tailTrace_1745025 : CollatzResearch.WordTrace tailWord_1745025 prefixEnd_1745025 199119239802697847858285 := by
  unfold tailWord_1745025
  simp only [CollatzResearch.WordTrace]
  refine ⟨63646290503079926388004529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42430860335386617592003019 63646290503079926388004529)
  ·
    refine ⟨47734717877309944791003397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63646290503079926388004529 47734717877309944791003397)
    ·
      refine ⟨8950259601995614648313137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47734717877309944791003397 8950259601995614648313137)
      ·
        refine ⟨6712694701496710986234853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8950259601995614648313137 6712694701496710986234853)
        ·
          refine ⟨1258630256530633309919035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6712694701496710986234853 1258630256530633309919035)
          ·
            refine ⟨1887945384795949964878553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258630256530633309919035 1887945384795949964878553)
            ·
              refine ⟨1415959038596962473658915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887945384795949964878553 1415959038596962473658915)
              ·
                refine ⟨2123938557895443710488373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415959038596962473658915 2123938557895443710488373)
                ·
                  refine ⟨199119239802697847858285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2123938557895443710488373 199119239802697847858285)
                  ·
                    rfl

theorem cell22_1745025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_1745025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745025 prefixEnd_1745025 := by exact prefixLift 1745025
  have htrace : WordTrace (prefixWord ++ tailWord_1745025) baseStart_1745025 baseEnd_1745025 := by
    simpa [prefixWord, tailWord_1745025, baseEnd_1745025] using wordTrace_append hprefix tailTrace_1745025
  have hstable : (prefixWord ++ tailWord_1745025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745025).length < 2 ^ (prefixWord ++ tailWord_1745025).sum := by decide
  have hdescent : baseEnd_1745025 < baseStart_1745025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745100 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1745100 : Nat := 118140960795 + 1745100 * 2 ^ 59
def prefixEnd_1745100 : Nat := 4983230072969 + 3 ^ 40 * 1745100 * 2
def baseEnd_1745100 : Nat := 597383393440818347949625

theorem tailTrace_1745100 : CollatzResearch.WordTrace tailWord_1745100 prefixEnd_1745100 597383393440818347949625 := by
  unfold tailWord_1745100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31824512988904107098492377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42432683985205476131323169 31824512988904107098492377)
  ·
    refine ⟨23868384741678080323869283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31824512988904107098492377 23868384741678080323869283)
    ·
      refine ⟨35802577112517120485803925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23868384741678080323869283 35802577112517120485803925)
      ·
        refine ⟨1678245802149240022772059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35802577112517120485803925 1678245802149240022772059)
        ·
          refine ⟨2517368703223860034158089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678245802149240022772059 2517368703223860034158089)
          ·
            refine ⟨1888026527417895025618567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517368703223860034158089 1888026527417895025618567)
            ·
              refine ⟨2832039791126842538427851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888026527417895025618567 2832039791126842538427851)
              ·
                refine ⟨4248059686690263807641777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832039791126842538427851 4248059686690263807641777)
                ·
                  refine ⟨3186044765017697855731333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248059686690263807641777 3186044765017697855731333)
                  ·
                    refine ⟨597383393440818347949625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186044765017697855731333 597383393440818347949625)
                    ·
                      rfl

theorem cell22_1745100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1745100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745100 prefixEnd_1745100 := by exact prefixLift 1745100
  have htrace : WordTrace (prefixWord ++ tailWord_1745100) baseStart_1745100 baseEnd_1745100 := by
    simpa [prefixWord, tailWord_1745100, baseEnd_1745100] using wordTrace_append hprefix tailTrace_1745100
  have hstable : (prefixWord ++ tailWord_1745100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745100).length < 2 ^ (prefixWord ++ tailWord_1745100).sum := by decide
  have hdescent : baseEnd_1745100 < baseStart_1745100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745113 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_1745113 : Nat := 118140960795 + 1745113 * 2 ^ 59
def prefixEnd_1745113 : Nat := 4983230072969 + 3 ^ 40 * 1745113 * 2
def baseEnd_1745113 : Nat := 597387843606490647374585

theorem tailTrace_1745113 : CollatzResearch.WordTrace tailWord_1745113 prefixEnd_1745113 597387843606490647374585 := by
  unfold tailWord_1745113
  simp only [CollatzResearch.WordTrace]
  refine ⟨63649500126761117417207993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42433000084507411611471995 63649500126761117417207993)
  ·
    refine ⟨47737125095070838062905995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63649500126761117417207993 47737125095070838062905995)
    ·
      refine ⟨71605687642606257094358993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47737125095070838062905995 71605687642606257094358993)
      ·
        refine ⟨53704265731954692820769245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71605687642606257094358993 53704265731954692820769245)
        ·
          refine ⟨20139099649483009807788467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53704265731954692820769245 20139099649483009807788467)
          ·
            refine ⟨30208649474224514711682701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139099649483009807788467 30208649474224514711682701)
            ·
              refine ⟨11328243552834193016881013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30208649474224514711682701 11328243552834193016881013)
              ·
                refine ⟨1062022833078205595332595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11328243552834193016881013 1062022833078205595332595)
                ·
                  refine ⟨1593034249617308392998893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062022833078205595332595 1593034249617308392998893)
                  ·
                    refine ⟨597387843606490647374585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593034249617308392998893 597387843606490647374585)
                    ·
                      rfl

theorem cell22_1745113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_1745113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745113 prefixEnd_1745113 := by exact prefixLift 1745113
  have htrace : WordTrace (prefixWord ++ tailWord_1745113) baseStart_1745113 baseEnd_1745113 := by
    simpa [prefixWord, tailWord_1745113, baseEnd_1745113] using wordTrace_append hprefix tailTrace_1745113
  have hstable : (prefixWord ++ tailWord_1745113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745113).length < 2 ^ (prefixWord ++ tailWord_1745113).sum := by decide
  have hdescent : baseEnd_1745113 < baseStart_1745113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745188 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1745188 : Nat := 118140960795 + 1745188 * 2 ^ 59
def prefixEnd_1745188 : Nat := 4983230072969 + 3 ^ 40 * 1745188 * 2
def baseEnd_1745188 : Nat := 199137839213071817249785

theorem tailTrace_1745188 : CollatzResearch.WordTrace tailWord_1745188 prefixEnd_1745188 199137839213071817249785 := by
  unfold tailWord_1745188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826117800744702613094109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42434823734326270150792145 31826117800744702613094109)
  ·
    refine ⟨11934794175279263479910291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31826117800744702613094109 11934794175279263479910291)
    ·
      refine ⟨17902191262918895219865437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934794175279263479910291 17902191262918895219865437)
      ·
        refine ⟨6713321723594585707449539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17902191262918895219865437 6713321723594585707449539)
        ·
          refine ⟨10069982585391878561174309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713321723594585707449539 10069982585391878561174309)
          ·
            refine ⟨1888121734760977230220183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10069982585391878561174309 1888121734760977230220183)
            ·
              refine ⟨2832182602141465845330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888121734760977230220183 2832182602141465845330275)
              ·
                refine ⟨4248273903212198767995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832182602141465845330275 4248273903212198767995413)
                ·
                  refine ⟨199137839213071817249785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4248273903212198767995413 199137839213071817249785)
                  ·
                    rfl

theorem cell22_1745188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1745188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745188 prefixEnd_1745188 := by exact prefixLift 1745188
  have htrace : WordTrace (prefixWord ++ tailWord_1745188) baseStart_1745188 baseEnd_1745188 := by
    simpa [prefixWord, tailWord_1745188, baseEnd_1745188] using wordTrace_append hprefix tailTrace_1745188
  have hstable : (prefixWord ++ tailWord_1745188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745188).length < 2 ^ (prefixWord ++ tailWord_1745188).sum := by decide
  have hdescent : baseEnd_1745188 < baseStart_1745188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745199 : List Nat := [1, 1, 2, 1, 2, 1, 5, 9]
def baseStart_1745199 : Nat := 118140960795 + 1745199 * 2 ^ 59
def prefixEnd_1745199 : Nat := 4983230072969 + 3 ^ 40 * 1745199 * 2
def baseEnd_1745199 : Nat := 66379698129335009969369

theorem tailTrace_1745199 : CollatzResearch.WordTrace tailWord_1745199 prefixEnd_1745199 66379698129335009969369 := by
  unfold tailWord_1745199
  simp only [CollatzResearch.WordTrace]
  refine ⟨63652636804449554104838651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42435091202966369403225767 63652636804449554104838651)
  ·
    refine ⟨95478955206674331157257977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63652636804449554104838651 95478955206674331157257977)
    ·
      refine ⟨71609216405005748367943483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95478955206674331157257977 71609216405005748367943483)
      ·
        refine ⟨107413824607508622551915225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71609216405005748367943483 107413824607508622551915225)
        ·
          refine ⟨80560368455631466913936419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107413824607508622551915225 80560368455631466913936419)
          ·
            refine ⟨120840552683447200370904629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80560368455631466913936419 120840552683447200370904629)
            ·
              refine ⟨11328801814073175034772309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120840552683447200370904629 11328801814073175034772309)
              ·
                refine ⟨66379698129335009969369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11328801814073175034772309 66379698129335009969369)
                ·
                  rfl

theorem cell22_1745199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 9].length) (baseStart_1745199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745199 prefixEnd_1745199 := by exact prefixLift 1745199
  have htrace : WordTrace (prefixWord ++ tailWord_1745199) baseStart_1745199 baseEnd_1745199 := by
    simpa [prefixWord, tailWord_1745199, baseEnd_1745199] using wordTrace_append hprefix tailTrace_1745199
  have hstable : (prefixWord ++ tailWord_1745199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745199).length < 2 ^ (prefixWord ++ tailWord_1745199).sum := by decide
  have hdescent : baseEnd_1745199 < baseStart_1745199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745203 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 2, 3]
def baseStart_1745203 : Nat := 118140960795 + 1745203 * 2 ^ 59
def prefixEnd_1745203 : Nat := 4983230072969 + 3 ^ 40 * 1745203 * 2
def baseEnd_1745203 : Nat := 597418652445760412624309

theorem tailTrace_1745203 : CollatzResearch.WordTrace tailWord_1745203 prefixEnd_1745203 597418652445760412624309 := by
  unfold tailWord_1745203
  simp only [CollatzResearch.WordTrace]
  refine ⟨63652782696435062787984263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42435188464290041858656175 63652782696435062787984263)
  ·
    refine ⟨95479174044652594181976395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63652782696435062787984263 95479174044652594181976395)
    ·
      refine ⟨143218761066978891272964593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95479174044652594181976395 143218761066978891272964593)
      ·
        refine ⟨107414070800234168454723445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143218761066978891272964593 107414070800234168454723445)
        ·
          refine ⟨10070069137521953292630323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107414070800234168454723445 10070069137521953292630323)
          ·
            refine ⟨15105103706282929938945485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10070069137521953292630323 15105103706282929938945485)
            ·
              refine ⟨5664413889856098727104557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15105103706282929938945485 5664413889856098727104557)
              ·
                refine ⟨2124155208696037022664209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664413889856098727104557 2124155208696037022664209)
                ·
                  refine ⟨1593116406522027766998157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2124155208696037022664209 1593116406522027766998157)
                  ·
                    refine ⟨597418652445760412624309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593116406522027766998157 597418652445760412624309)
                    ·
                      rfl

theorem cell22_1745203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].length) (baseStart_1745203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745203 prefixEnd_1745203 := by exact prefixLift 1745203
  have htrace : WordTrace (prefixWord ++ tailWord_1745203) baseStart_1745203 baseEnd_1745203 := by
    simpa [prefixWord, tailWord_1745203, baseEnd_1745203] using wordTrace_append hprefix tailTrace_1745203
  have hstable : (prefixWord ++ tailWord_1745203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745203).length < 2 ^ (prefixWord ++ tailWord_1745203).sum := by decide
  have hdescent : baseEnd_1745203 < baseStart_1745203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745220 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1745220 : Nat := 118140960795 + 1745220 * 2 ^ 59
def prefixEnd_1745220 : Nat := 4983230072969 + 3 ^ 40 * 1745220 * 2
def baseEnd_1745220 : Nat := 597424471893178034949257

theorem tailTrace_1745220 : CollatzResearch.WordTrace tailWord_1745220 prefixEnd_1745220 597424471893178034949257 := by
  unfold tailWord_1745220
  simp only [CollatzResearch.WordTrace]
  refine ⟨31826701368686737345676557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42435601824915649794235409 31826701368686737345676557)
  ·
    refine ⟨11935013013257526504628709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31826701368686737345676557 11935013013257526504628709)
    ·
      refine ⟨2237814939985786219617883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11935013013257526504628709 2237814939985786219617883)
      ·
        refine ⟨3356722409978679329426825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237814939985786219617883 3356722409978679329426825)
        ·
          refine ⟨2517541807484009497070119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356722409978679329426825 2517541807484009497070119)
          ·
            refine ⟨3776312711226014245605179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517541807484009497070119 3776312711226014245605179)
            ·
              refine ⟨5664469066839021368407769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776312711226014245605179 5664469066839021368407769)
              ·
                refine ⟨4248351800129266026305827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5664469066839021368407769 4248351800129266026305827)
                ·
                  refine ⟨6372527700193899039458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248351800129266026305827 6372527700193899039458741)
                  ·
                    refine ⟨597424471893178034949257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6372527700193899039458741 597424471893178034949257)
                    ·
                      rfl

theorem cell22_1745220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1745220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745220 prefixEnd_1745220 := by exact prefixLift 1745220
  have htrace : WordTrace (prefixWord ++ tailWord_1745220) baseStart_1745220 baseEnd_1745220 := by
    simpa [prefixWord, tailWord_1745220, baseEnd_1745220] using wordTrace_append hprefix tailTrace_1745220
  have hstable : (prefixWord ++ tailWord_1745220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745220).length < 2 ^ (prefixWord ++ tailWord_1745220).sum := by decide
  have hdescent : baseEnd_1745220 < baseStart_1745220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745231 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 7, 3]
def baseStart_1745231 : Nat := 118140960795 + 1745231 * 2 ^ 59
def prefixEnd_1745231 : Nat := 4983230072969 + 3 ^ 40 * 1745231 * 2
def baseEnd_1745231 : Nat := 597428237417977672924223

theorem tailTrace_1745231 : CollatzResearch.WordTrace tailWord_1745231 prefixEnd_1745231 597428237417977672924223 := by
  unfold tailWord_1745231
  simp only [CollatzResearch.WordTrace]
  refine ⟨63653803940333623570003547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42435869293555749046669031 63653803940333623570003547)
  ·
    refine ⟨95480705910500435355005321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63653803940333623570003547 95480705910500435355005321)
    ·
      refine ⟨71610529432875326516253991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95480705910500435355005321 71610529432875326516253991)
      ·
        refine ⟨107415794149312989774380987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71610529432875326516253991 107415794149312989774380987)
        ·
          refine ⟨161123691223969484661571481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107415794149312989774380987 161123691223969484661571481)
          ·
            refine ⟨120842768417977113496178611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161123691223969484661571481 120842768417977113496178611)
            ·
              refine ⟨181264152626965670244267917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120842768417977113496178611 181264152626965670244267917)
              ·
                refine ⟨67974057235112126341600469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181264152626965670244267917 67974057235112126341600469)
                ·
                  refine ⟨1593141966447940461131261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 67974057235112126341600469 1593141966447940461131261)
                  ·
                    refine ⟨597428237417977672924223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593141966447940461131261 597428237417977672924223)
                    ·
                      rfl

theorem cell22_1745231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_1745231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745231 prefixEnd_1745231 := by exact prefixLift 1745231
  have htrace : WordTrace (prefixWord ++ tailWord_1745231) baseStart_1745231 baseEnd_1745231 := by
    simpa [prefixWord, tailWord_1745231, baseEnd_1745231] using wordTrace_append hprefix tailTrace_1745231
  have hstable : (prefixWord ++ tailWord_1745231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745231).length < 2 ^ (prefixWord ++ tailWord_1745231).sum := by decide
  have hdescent : baseEnd_1745231 < baseStart_1745231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745310 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1745310 : Nat := 118140960795 + 1745310 * 2 ^ 59
def prefixEnd_1745310 : Nat := 4983230072969 + 3 ^ 40 * 1745310 * 2
def baseEnd_1745310 : Nat := 597455280732447800198981

theorem tailTrace_1745310 : CollatzResearch.WordTrace tailWord_1745310 prefixEnd_1745310 597455280732447800198981 := by
  unfold tailWord_1745310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957085663380927507766173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42437790204698280041419589 7957085663380927507766173)
  ·
    refine ⟨2983907123767847815412315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7957085663380927507766173 2983907123767847815412315)
    ·
      refine ⟨4475860685651771723118473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983907123767847815412315 4475860685651771723118473)
      ·
        refine ⟨3356895514238828792338855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4475860685651771723118473 3356895514238828792338855)
        ·
          refine ⟨5035343271358243188508283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356895514238828792338855 5035343271358243188508283)
          ·
            refine ⟨7553014907037364782762425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035343271358243188508283 7553014907037364782762425)
            ·
              refine ⟨5664761180278023587071819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553014907037364782762425 5664761180278023587071819)
              ·
                refine ⟨8497141770417035380607729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664761180278023587071819 8497141770417035380607729)
                ·
                  refine ⟨6372856327812776535455797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8497141770417035380607729 6372856327812776535455797)
                  ·
                    refine ⟨597455280732447800198981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6372856327812776535455797 597455280732447800198981)
                    ·
                      rfl

theorem cell22_1745310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1745310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745310 prefixEnd_1745310 := by exact prefixLift 1745310
  have htrace : WordTrace (prefixWord ++ tailWord_1745310) baseStart_1745310 baseEnd_1745310 := by
    simpa [prefixWord, tailWord_1745310, baseEnd_1745310] using wordTrace_append hprefix tailTrace_1745310
  have hstable : (prefixWord ++ tailWord_1745310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745310).length < 2 ^ (prefixWord ++ tailWord_1745310).sum := by decide
  have hdescent : baseEnd_1745310 < baseStart_1745310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745351 : List Nat := [1, 1, 4, 1, 1, 4, 10]
def baseStart_1745351 : Nat := 118140960795 + 1745351 * 2 ^ 59
def prefixEnd_1745351 : Nat := 4983230072969 + 3 ^ 40 * 1745351 * 2
def baseEnd_1745351 : Nat := 22128493180382865182365

theorem tailTrace_1745351 : CollatzResearch.WordTrace tailWord_1745351 prefixEnd_1745351 22128493180382865182365 := by
  unfold tailWord_1745351
  simp only [CollatzResearch.WordTrace]
  refine ⟨63658180699898884064371907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42438787133265922709581271 63658180699898884064371907)
  ·
    refine ⟨95487271049848326096557861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63658180699898884064371907 95487271049848326096557861)
    ·
      refine ⟨17903863321846561143104599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95487271049848326096557861 17903863321846561143104599)
      ·
        refine ⟨26855794982769841714656899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903863321846561143104599 26855794982769841714656899)
        ·
          refine ⟨40283692474154762571985349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26855794982769841714656899 40283692474154762571985349)
          ·
            refine ⟨7553192338904017982247253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40283692474154762571985349 7553192338904017982247253)
            ·
              refine ⟨22128493180382865182365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7553192338904017982247253 22128493180382865182365)
              ·
                rfl

theorem cell22_1745351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 10].length) (baseStart_1745351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745351 prefixEnd_1745351 := by exact prefixLift 1745351
  have htrace : WordTrace (prefixWord ++ tailWord_1745351) baseStart_1745351 baseEnd_1745351 := by
    simpa [prefixWord, tailWord_1745351, baseEnd_1745351] using wordTrace_append hprefix tailTrace_1745351
  have hstable : (prefixWord ++ tailWord_1745351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745351).length < 2 ^ (prefixWord ++ tailWord_1745351).sum := by decide
  have hdescent : baseEnd_1745351 < baseStart_1745351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745413 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1745413 : Nat := 118140960795 + 1745413 * 2 ^ 59
def prefixEnd_1745413 : Nat := 4983230072969 + 3 ^ 40 * 1745413 * 2
def baseEnd_1745413 : Nat := 199163513245796621624555

theorem tailTrace_1745413 : CollatzResearch.WordTrace tailWord_1745413 prefixEnd_1745413 199163513245796621624555 := by
  unfold tailWord_1745413
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660442025674268653128893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42440294683782845768752595 63660442025674268653128893)
  ·
    refine ⟨23872665759627850744923335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63660442025674268653128893 23872665759627850744923335)
    ·
      refine ⟨35808998639441776117385003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23872665759627850744923335 35808998639441776117385003)
      ·
        refine ⟨53713497959162664176077505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35808998639441776117385003 53713497959162664176077505)
        ·
          refine ⟨40285123469371998132058129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53713497959162664176077505 40285123469371998132058129)
          ·
            refine ⟨30213842602028998599043597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40285123469371998132058129 30213842602028998599043597)
            ·
              refine ⟨11330190975760874474641349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30213842602028998599043597 11330190975760874474641349)
              ·
                refine ⟨2124410807955163963995253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11330190975760874474641349 2124410807955163963995253)
                ·
                  refine ⟨199163513245796621624555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2124410807955163963995253 199163513245796621624555)
                  ·
                    rfl

theorem cell22_1745413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1745413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745413 prefixEnd_1745413 := by exact prefixLift 1745413
  have htrace : WordTrace (prefixWord ++ tailWord_1745413) baseStart_1745413 baseEnd_1745413 := by
    simpa [prefixWord, tailWord_1745413, baseEnd_1745413] using wordTrace_append hprefix tailTrace_1745413
  have hstable : (prefixWord ++ tailWord_1745413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745413).length < 2 ^ (prefixWord ++ tailWord_1745413).sum := by decide
  have hdescent : baseEnd_1745413 < baseStart_1745413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745488 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_1745488 : Nat := 118140960795 + 1745488 * 2 ^ 59
def prefixEnd_1745488 : Nat := 4983230072969 + 3 ^ 40 * 1745488 * 2
def baseEnd_1745488 : Nat := 597516213770114669248435

theorem tailTrace_1745488 : CollatzResearch.WordTrace tailWord_1745488 prefixEnd_1745488 597516213770114669248435 := by
  unfold tailWord_1745488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831588750201278231054559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42442118333601704308072745 31831588750201278231054559)
  ·
    refine ⟨47747383125301917346581839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31831588750201278231054559 47747383125301917346581839)
    ·
      refine ⟨71621074687952876019872759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47747383125301917346581839 71621074687952876019872759)
      ·
        refine ⟨107431612031929314029809139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71621074687952876019872759 107431612031929314029809139)
        ·
          refine ⟨161147418047893971044713709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107431612031929314029809139 161147418047893971044713709)
          ·
            refine ⟨60430281767960239141767641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161147418047893971044713709 60430281767960239141767641)
            ·
              refine ⟨45322711325970179356325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60430281767960239141767641 45322711325970179356325731)
              ·
                refine ⟨67984066988955269034488597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45322711325970179356325731 67984066988955269034488597)
                ·
                  refine ⟨3186753140107278235991653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67984066988955269034488597 3186753140107278235991653)
                  ·
                    refine ⟨597516213770114669248435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186753140107278235991653 597516213770114669248435)
                    ·
                      rfl

theorem cell22_1745488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_1745488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745488 prefixEnd_1745488 := by exact prefixLift 1745488
  have htrace : WordTrace (prefixWord ++ tailWord_1745488) baseStart_1745488 baseEnd_1745488 := by
    simpa [prefixWord, tailWord_1745488, baseEnd_1745488] using wordTrace_append hprefix tailTrace_1745488
  have hstable : (prefixWord ++ tailWord_1745488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745488).length < 2 ^ (prefixWord ++ tailWord_1745488).sum := by decide
  have hdescent : baseEnd_1745488 < baseStart_1745488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745502 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1745502 : Nat := 118140960795 + 1745502 * 2 ^ 59
def prefixEnd_1745502 : Nat := 4983230072969 + 3 ^ 40 * 1745502 * 2
def baseEnd_1745502 : Nat := 597521006256223299398393

theorem tailTrace_1745502 : CollatzResearch.WordTrace tailWord_1745502 prefixEnd_1745502 597521006256223299398393 := by
  unfold tailWord_1745502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957961015293979606639845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42442458748234557902079173 7957961015293979606639845)
  ·
    refine ⟨1492117690367621176244971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7957961015293979606639845 1492117690367621176244971)
    ·
      refine ⟨2238176535551431764367457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492117690367621176244971 2238176535551431764367457)
      ·
        refine ⟨1678632401663573823275593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238176535551431764367457 1678632401663573823275593)
        ·
          refine ⟨1258974301247680367456695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678632401663573823275593 1258974301247680367456695)
          ·
            refine ⟨1888461451871520551185043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258974301247680367456695 1888461451871520551185043)
            ·
              refine ⟨2832692177807280826777565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888461451871520551185043 2832692177807280826777565)
              ·
                refine ⟨1062259566677730310041587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832692177807280826777565 1062259566677730310041587)
                ·
                  refine ⟨1593389350016595465062381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062259566677730310041587 1593389350016595465062381)
                  ·
                    refine ⟨597521006256223299398393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593389350016595465062381 597521006256223299398393)
                    ·
                      rfl

theorem cell22_1745502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1745502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745502 prefixEnd_1745502 := by exact prefixLift 1745502
  have htrace : WordTrace (prefixWord ++ tailWord_1745502) baseStart_1745502 baseEnd_1745502 := by
    simpa [prefixWord, tailWord_1745502, baseEnd_1745502] using wordTrace_append hprefix tailTrace_1745502
  have hstable : (prefixWord ++ tailWord_1745502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745502).length < 2 ^ (prefixWord ++ tailWord_1745502).sum := by decide
  have hdescent : baseEnd_1745502 < baseStart_1745502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745509 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 4]
def baseStart_1745509 : Nat := 118140960795 + 1745509 * 2 ^ 59
def prefixEnd_1745509 : Nat := 4983230072969 + 3 ^ 40 * 1745509 * 2
def baseEnd_1745509 : Nat := 199174467499759204824457

theorem tailTrace_1745509 : CollatzResearch.WordTrace tailWord_1745509 prefixEnd_1745509 199174467499759204824457 := by
  unfold tailWord_1745509
  simp only [CollatzResearch.WordTrace]
  refine ⟨63663943433326477048623581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42442628955550984699082387 63663943433326477048623581)
  ·
    refine ⟨23873978787497428893233843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63663943433326477048623581 23873978787497428893233843)
    ·
      refine ⟨35810968181246143339850765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23873978787497428893233843 35810968181246143339850765)
      ·
        refine ⟨13429113067967303752444037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35810968181246143339850765 13429113067967303752444037)
        ·
          refine ⟨2517958700243869453583257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13429113067967303752444037 2517958700243869453583257)
          ·
            refine ⟨1888469025182902090187443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517958700243869453583257 1888469025182902090187443)
            ·
              refine ⟨2832703537774353135281165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888469025182902090187443 2832703537774353135281165)
              ·
                refine ⟨1062263826665382425730437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2832703537774353135281165 1062263826665382425730437)
                ·
                  refine ⟨199174467499759204824457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062263826665382425730437 199174467499759204824457)
                  ·
                    rfl

theorem cell22_1745509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_1745509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745509 prefixEnd_1745509 := by exact prefixLift 1745509
  have htrace : WordTrace (prefixWord ++ tailWord_1745509) baseStart_1745509 baseEnd_1745509 := by
    simpa [prefixWord, tailWord_1745509, baseEnd_1745509] using wordTrace_append hprefix tailTrace_1745509
  have hstable : (prefixWord ++ tailWord_1745509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745509).length < 2 ^ (prefixWord ++ tailWord_1745509).sum := by decide
  have hdescent : baseEnd_1745509 < baseStart_1745509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745520 : List Nat := [2, 1, 1, 1, 7, 2, 8]
def baseStart_1745520 : Nat := 118140960795 + 1745520 * 2 ^ 59
def prefixEnd_1745520 : Nat := 4983230072969 + 3 ^ 40 * 1745520 * 2
def baseEnd_1745520 : Nat := 22130635852743601942531

theorem tailTrace_1745520 : CollatzResearch.WordTrace tailWord_1745520 prefixEnd_1745520 22130635852743601942531 := by
  unfold tailWord_1745520
  simp only [CollatzResearch.WordTrace]
  refine ⟨31832172318143312963637007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42442896424191083951516009 31832172318143312963637007)
  ·
    refine ⟨47748258477214969445455511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31832172318143312963637007 47748258477214969445455511)
    ·
      refine ⟨71622387715822454168183267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47748258477214969445455511 71622387715822454168183267)
      ·
        refine ⟨107433581573733681252274901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71622387715822454168183267 107433581573733681252274901)
        ·
          refine ⟨2517974568134383154350193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107433581573733681252274901 2517974568134383154350193)
          ·
            refine ⟨1888480926100787365762645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517974568134383154350193 1888480926100787365762645)
            ·
              refine ⟨22130635852743601942531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1888480926100787365762645 22130635852743601942531)
              ·
                rfl

theorem cell22_1745520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 8].length) (baseStart_1745520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745520 prefixEnd_1745520 := by exact prefixLift 1745520
  have htrace : WordTrace (prefixWord ++ tailWord_1745520) baseStart_1745520 baseEnd_1745520 := by
    simpa [prefixWord, tailWord_1745520, baseEnd_1745520] using wordTrace_append hprefix tailTrace_1745520
  have hstable : (prefixWord ++ tailWord_1745520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745520).length < 2 ^ (prefixWord ++ tailWord_1745520).sum := by decide
  have hdescent : baseEnd_1745520 < baseStart_1745520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745522 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1745522 : Nat := 118140960795 + 1745522 * 2 ^ 59
def prefixEnd_1745522 : Nat := 4983230072969 + 3 ^ 40 * 1745522 * 2
def baseEnd_1745522 : Nat := 597527852664949913898331

theorem tailTrace_1745522 : CollatzResearch.WordTrace tailWord_1745522 prefixEnd_1745522 597527852664949913898331 := by
  unfold tailWord_1745522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916104395569845067211705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42442945054852920179231213 15916104395569845067211705)
  ·
    refine ⟨11937078296677383800408779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916104395569845067211705 11937078296677383800408779)
    ·
      refine ⟨17905617445016075700613169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937078296677383800408779 17905617445016075700613169)
      ·
        refine ⟨13429213083762056775459877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17905617445016075700613169 13429213083762056775459877)
        ·
          refine ⟨2517977453205385645398727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13429213083762056775459877 2517977453205385645398727)
          ·
            refine ⟨3776966179808078468098091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517977453205385645398727 3776966179808078468098091)
            ·
              refine ⟨5665449269712117702147137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776966179808078468098091 5665449269712117702147137)
              ·
                refine ⟨4249086952284088276610353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665449269712117702147137 4249086952284088276610353)
                ·
                  refine ⟨3186815214213066207457765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249086952284088276610353 3186815214213066207457765)
                  ·
                    refine ⟨597527852664949913898331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186815214213066207457765 597527852664949913898331)
                    ·
                      rfl

theorem cell22_1745522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1745522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745522 prefixEnd_1745522 := by exact prefixLift 1745522
  have htrace : WordTrace (prefixWord ++ tailWord_1745522) baseStart_1745522 baseEnd_1745522 := by
    simpa [prefixWord, tailWord_1745522, baseEnd_1745522] using wordTrace_append hprefix tailTrace_1745522
  have hstable : (prefixWord ++ tailWord_1745522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745522).length < 2 ^ (prefixWord ++ tailWord_1745522).sum := by decide
  have hdescent : baseEnd_1745522 < baseStart_1745522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745526 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1745526 : Nat := 118140960795 + 1745526 * 2 ^ 59
def prefixEnd_1745526 : Nat := 4983230072969 + 3 ^ 40 * 1745526 * 2
def baseEnd_1745526 : Nat := 199176407315565078932773

theorem tailTrace_1745526 : CollatzResearch.WordTrace tailWord_1745526 prefixEnd_1745526 199176407315565078932773 := by
  unfold tailWord_1745526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979035217141555559499527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42443042316176592634661621 3979035217141555559499527)
  ·
    refine ⟨5968552825712333339249291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3979035217141555559499527 5968552825712333339249291)
    ·
      refine ⟨8952829238568500008873937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968552825712333339249291 8952829238568500008873937)
      ·
        refine ⟨6714621928926375006655453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8952829238568500008873937 6714621928926375006655453)
        ·
          refine ⟨2517983223347390627495795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6714621928926375006655453 2517983223347390627495795)
          ·
            refine ⟨3776974835021085941243693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517983223347390627495795 3776974835021085941243693)
            ·
              refine ⟨1416365563132907227966385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3776974835021085941243693 1416365563132907227966385)
              ·
                refine ⟨1062274172349680420974789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416365563132907227966385 1062274172349680420974789)
                ·
                  refine ⟨199176407315565078932773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062274172349680420974789 199176407315565078932773)
                  ·
                    rfl

theorem cell22_1745526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1745526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745526 prefixEnd_1745526 := by exact prefixLift 1745526
  have htrace : WordTrace (prefixWord ++ tailWord_1745526) baseStart_1745526 baseEnd_1745526 := by
    simpa [prefixWord, tailWord_1745526, baseEnd_1745526] using wordTrace_append hprefix tailTrace_1745526
  have hstable : (prefixWord ++ tailWord_1745526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745526).length < 2 ^ (prefixWord ++ tailWord_1745526).sum := by decide
  have hdescent : baseEnd_1745526 < baseStart_1745526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745535 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 3, 3]
def baseStart_1745535 : Nat := 118140960795 + 1745535 * 2 ^ 59
def prefixEnd_1745535 : Nat := 4983230072969 + 3 ^ 40 * 1745535 * 2
def baseEnd_1745535 : Nat := 597532302830622213323291

theorem tailTrace_1745535 : CollatzResearch.WordTrace tailWord_1745535 prefixEnd_1745535 597532302830622213323291 := by
  unfold tailWord_1745535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63664891731232283489070059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42443261154154855659380039 63664891731232283489070059)
  ·
    refine ⟨95497337596848425233605089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63664891731232283489070059 95497337596848425233605089)
    ·
      refine ⟨71623003197636318925203817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95497337596848425233605089 71623003197636318925203817)
      ·
        refine ⟨53717252398227239193902863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71623003197636318925203817 53717252398227239193902863)
        ·
          refine ⟨80575878597340858790854295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53717252398227239193902863 80575878597340858790854295)
          ·
            refine ⟨120863817896011288186281443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80575878597340858790854295 120863817896011288186281443)
            ·
              refine ⟨181295726844016932279422165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120863817896011288186281443 181295726844016932279422165)
              ·
                refine ⟨4249118597906646850298957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181295726844016932279422165 4249118597906646850298957)
                ·
                  refine ⟨1593419474214992568862109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4249118597906646850298957 1593419474214992568862109)
                  ·
                    refine ⟨597532302830622213323291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593419474214992568862109 597532302830622213323291)
                    ·
                      rfl

theorem cell22_1745535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_1745535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745535 prefixEnd_1745535 := by exact prefixLift 1745535
  have htrace : WordTrace (prefixWord ++ tailWord_1745535) baseStart_1745535 baseEnd_1745535 := by
    simpa [prefixWord, tailWord_1745535, baseEnd_1745535] using wordTrace_append hprefix tailTrace_1745535
  have hstable : (prefixWord ++ tailWord_1745535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745535).length < 2 ^ (prefixWord ++ tailWord_1745535).sum := by decide
  have hdescent : baseEnd_1745535 < baseStart_1745535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745548 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1745548 : Nat := 118140960795 + 1745548 * 2 ^ 59
def prefixEnd_1745548 : Nat := 4983230072969 + 3 ^ 40 * 1745548 * 2
def baseEnd_1745548 : Nat := 199178917665431504249417

theorem tailTrace_1745548 : CollatzResearch.WordTrace tailWord_1745548 prefixEnd_1745548 199178917665431504249417 := by
  unfold tailWord_1745548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31832682940092593354646649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42443577253456791139528865 31832682940092593354646649)
  ·
    refine ⟨23874512205069445015984987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31832682940092593354646649 23874512205069445015984987)
    ·
      refine ⟨35811768307604167523977481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23874512205069445015984987 35811768307604167523977481)
      ·
        refine ⟨26858826230703125642983111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35811768307604167523977481 26858826230703125642983111)
        ·
          refine ⟨40288239346054688464474667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26858826230703125642983111 40288239346054688464474667)
          ·
            refine ⟨60432359019082032696712001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40288239346054688464474667 60432359019082032696712001)
            ·
              refine ⟨45324269264311524522534001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60432359019082032696712001 45324269264311524522534001)
              ·
                refine ⟨33993201948233643391900501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45324269264311524522534001 33993201948233643391900501)
                ·
                  refine ⟨199178917665431504249417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33993201948233643391900501 199178917665431504249417)
                  ·
                    rfl

theorem cell22_1745548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1745548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745548 prefixEnd_1745548 := by exact prefixLift 1745548
  have htrace : WordTrace (prefixWord ++ tailWord_1745548) baseStart_1745548 baseEnd_1745548 := by
    simpa [prefixWord, tailWord_1745548, baseEnd_1745548] using wordTrace_append hprefix tailTrace_1745548
  have hstable : (prefixWord ++ tailWord_1745548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745548).length < 2 ^ (prefixWord ++ tailWord_1745548).sum := by decide
  have hdescent : baseEnd_1745548 < baseStart_1745548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745610 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1745610 : Nat := 118140960795 + 1745610 * 2 ^ 59
def prefixEnd_1745610 : Nat := 4983230072969 + 3 ^ 40 * 1745610 * 2
def baseEnd_1745610 : Nat := 199185992287782339232687

theorem tailTrace_1745610 : CollatzResearch.WordTrace tailWord_1745610 prefixEnd_1745610 199185992287782339232687 := by
  unfold tailWord_1745610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916906801490142824512571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42445084803973714198700189 15916906801490142824512571)
  ·
    refine ⟨23875360202235214236768857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15916906801490142824512571 23875360202235214236768857)
    ·
      refine ⟨17906520151676410677576643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23875360202235214236768857 17906520151676410677576643)
      ·
        refine ⟨26859780227514616016364965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906520151676410677576643 26859780227514616016364965)
        ·
          refine ⟨5036208792658990503068431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26859780227514616016364965 5036208792658990503068431)
          ·
            refine ⟨7554313188988485754602647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036208792658990503068431 7554313188988485754602647)
            ·
              refine ⟨11331469783482728631903971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554313188988485754602647 11331469783482728631903971)
              ·
                refine ⟨16997204675224092947855957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331469783482728631903971 16997204675224092947855957)
                ·
                  refine ⟨199185992287782339232687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16997204675224092947855957 199185992287782339232687)
                  ·
                    rfl

theorem cell22_1745610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1745610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745610 prefixEnd_1745610 := by exact prefixLift 1745610
  have htrace : WordTrace (prefixWord ++ tailWord_1745610) baseStart_1745610 baseEnd_1745610 := by
    simpa [prefixWord, tailWord_1745610, baseEnd_1745610] using wordTrace_append hprefix tailTrace_1745610
  have hstable : (prefixWord ++ tailWord_1745610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745610).length < 2 ^ (prefixWord ++ tailWord_1745610).sum := by decide
  have hdescent : baseEnd_1745610 < baseStart_1745610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745612 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_1745612 : Nat := 118140960795 + 1745612 * 2 ^ 59
def prefixEnd_1745612 : Nat := 4983230072969 + 3 ^ 40 * 1745612 * 2
def baseEnd_1745612 : Nat := 597558661504219679148055

theorem tailTrace_1745612 : CollatzResearch.WordTrace tailWord_1745612 prefixEnd_1745612 597558661504219679148055 := by
  unfold tailWord_1745612
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833850075976662819811545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42445133434635550426415393 31833850075976662819811545)
  ·
    refine ⟨23875387556982497114858659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31833850075976662819811545 23875387556982497114858659)
    ·
      refine ⟨35813081335473745672287989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23875387556982497114858659 35813081335473745672287989)
      ·
        refine ⟨3357476375200663656776999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35813081335473745672287989 3357476375200663656776999)
        ·
          refine ⟨5036214562800995485165499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357476375200663656776999 5036214562800995485165499)
          ·
            refine ⟨7554321844201493227748249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036214562800995485165499 7554321844201493227748249)
            ·
              refine ⟨5665741383151119920811187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554321844201493227748249 5665741383151119920811187)
              ·
                refine ⟨8498612074726679881216781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665741383151119920811187 8498612074726679881216781)
                ·
                  refine ⟨3186979528022504955456293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8498612074726679881216781 3186979528022504955456293)
                  ·
                    refine ⟨597558661504219679148055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3186979528022504955456293 597558661504219679148055)
                    ·
                      rfl

theorem cell22_1745612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_1745612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745612 prefixEnd_1745612 := by exact prefixLift 1745612
  have htrace : WordTrace (prefixWord ++ tailWord_1745612) baseStart_1745612 baseEnd_1745612 := by
    simpa [prefixWord, tailWord_1745612, baseEnd_1745612] using wordTrace_append hprefix tailTrace_1745612
  have hstable : (prefixWord ++ tailWord_1745612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745612).length < 2 ^ (prefixWord ++ tailWord_1745612).sum := by decide
  have hdescent : baseEnd_1745612 < baseStart_1745612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745625 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1745625 : Nat := 118140960795 + 1745625 * 2 ^ 59
def prefixEnd_1745625 : Nat := 4983230072969 + 3 ^ 40 * 1745625 * 2
def baseEnd_1745625 : Nat := 597563111669891978573015

theorem tailTrace_1745625 : CollatzResearch.WordTrace tailWord_1745625 prefixEnd_1745625 597563111669891978573015 := by
  unfold tailWord_1745625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63668174300906228859846329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42445449533937485906564219 63668174300906228859846329)
  ·
    refine ⟨47751130725679671644884747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63668174300906228859846329 47751130725679671644884747)
    ·
      refine ⟨71626696088519507467327121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47751130725679671644884747 71626696088519507467327121)
      ·
        refine ⟨53720022066389630600495341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71626696088519507467327121 53720022066389630600495341)
        ·
          refine ⟨20145008274896111475185753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53720022066389630600495341 20145008274896111475185753)
          ·
            refine ⟨15108756206172083606389315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20145008274896111475185753 15108756206172083606389315)
            ·
              refine ⟨22663134309258125409583973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108756206172083606389315 22663134309258125409583973)
              ·
                refine ⟨4249337682985898514296995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22663134309258125409583973 4249337682985898514296995)
                ·
                  refine ⟨6374006524478847771445493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249337682985898514296995 6374006524478847771445493)
                  ·
                    refine ⟨597563111669891978573015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6374006524478847771445493 597563111669891978573015)
                    ·
                      rfl

theorem cell22_1745625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1745625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745625 prefixEnd_1745625 := by exact prefixLift 1745625
  have htrace : WordTrace (prefixWord ++ tailWord_1745625) baseStart_1745625 baseEnd_1745625 := by
    simpa [prefixWord, tailWord_1745625, baseEnd_1745625] using wordTrace_append hprefix tailTrace_1745625
  have hstable : (prefixWord ++ tailWord_1745625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745625).length < 2 ^ (prefixWord ++ tailWord_1745625).sum := by decide
  have hdescent : baseEnd_1745625 < baseStart_1745625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745672 : List Nat := [2, 1, 3, 2, 2, 2, 4, 6]
def baseStart_1745672 : Nat := 118140960795 + 1745672 * 2 ^ 59
def prefixEnd_1745672 : Nat := 4983230072969 + 3 ^ 40 * 1745672 * 2
def baseEnd_1745672 : Nat := 66397688970044391405319

theorem tailTrace_1745672 : CollatzResearch.WordTrace tailWord_1745672 prefixEnd_1745672 66397688970044391405319 := by
  unfold tailWord_1745672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31834944265867977943403635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42446592354490637257871513 31834944265867977943403635)
  ·
    refine ⟨47752416398801966915105453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31834944265867977943403635 47752416398801966915105453)
    ·
      refine ⟨17907156149550737593164545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47752416398801966915105453 17907156149550737593164545)
      ·
        refine ⟨13430367112163053194873409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17907156149550737593164545 13430367112163053194873409)
        ·
          refine ⟨10072775334122289896155057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13430367112163053194873409 10072775334122289896155057)
          ·
            refine ⟨7554581500591717422116293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10072775334122289896155057 7554581500591717422116293)
            ·
              refine ⟨1416484031360947016646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7554581500591717422116293 1416484031360947016646805)
              ·
                refine ⟨66397688970044391405319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416484031360947016646805 66397688970044391405319)
                ·
                  rfl

theorem cell22_1745672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_1745672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745672 prefixEnd_1745672 := by exact prefixLift 1745672
  have htrace : WordTrace (prefixWord ++ tailWord_1745672) baseStart_1745672 baseEnd_1745672 := by
    simpa [prefixWord, tailWord_1745672, baseEnd_1745672] using wordTrace_append hprefix tailTrace_1745672
  have hstable : (prefixWord ++ tailWord_1745672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745672).length < 2 ^ (prefixWord ++ tailWord_1745672).sum := by decide
  have hdescent : baseEnd_1745672 < baseStart_1745672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745747 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 1, 4]
def baseStart_1745747 : Nat := 118140960795 + 1745747 * 2 ^ 59
def prefixEnd_1745747 : Nat := 4983230072969 + 3 ^ 40 * 1745747 * 2
def baseEnd_1745747 : Nat := 597604874763124327022641

theorem tailTrace_1745747 : CollatzResearch.WordTrace tailWord_1745747 prefixEnd_1745747 597604874763124327022641 := by
  unfold tailWord_1745747
  simp only [CollatzResearch.WordTrace]
  refine ⟨63672624006464243695787495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42448416004309495797191663 63672624006464243695787495)
  ·
    refine ⟨95508936009696365543681243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63672624006464243695787495 95508936009696365543681243)
    ·
      refine ⟨143263404014544548315521865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95508936009696365543681243 143263404014544548315521865)
      ·
        refine ⟨107447553010908411236641399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143263404014544548315521865 107447553010908411236641399)
        ·
          refine ⟨161171329516362616854962099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107447553010908411236641399 161171329516362616854962099)
          ·
            refine ⟨241756994274543925282443149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161171329516362616854962099 241756994274543925282443149)
            ·
              refine ⟨90658872852953971980916181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241756994274543925282443149 90658872852953971980916181)
              ·
                refine ⟨2124817332491108718302723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90658872852953971980916181 2124817332491108718302723)
                ·
                  refine ⟨3187225998736663077454085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2124817332491108718302723 3187225998736663077454085)
                  ·
                    refine ⟨597604874763124327022641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187225998736663077454085 597604874763124327022641)
                    ·
                      rfl

theorem cell22_1745747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_1745747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745747 prefixEnd_1745747 := by exact prefixLift 1745747
  have htrace : WordTrace (prefixWord ++ tailWord_1745747) baseStart_1745747 baseEnd_1745747 := by
    simpa [prefixWord, tailWord_1745747, baseEnd_1745747] using wordTrace_append hprefix tailTrace_1745747
  have hstable : (prefixWord ++ tailWord_1745747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745747).length < 2 ^ (prefixWord ++ tailWord_1745747).sum := by decide
  have hdescent : baseEnd_1745747 < baseStart_1745747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745777 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1745777 : Nat := 118140960795 + 1745777 * 2 ^ 59
def prefixEnd_1745777 : Nat := 4983230072969 + 3 ^ 40 * 1745777 * 2
def baseEnd_1745777 : Nat := 597615144376214248772549

theorem tailTrace_1745777 : CollatzResearch.WordTrace tailWord_1745777 prefixEnd_1745777 597615144376214248772549 := by
  unfold tailWord_1745777
  simp only [CollatzResearch.WordTrace]
  refine ⟨63673718196355558819379585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42449145464237039212919723 63673718196355558819379585)
  ·
    refine ⟨47755288647266669114534689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63673718196355558819379585 47755288647266669114534689)
    ·
      refine ⟨35816466485450001835901017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47755288647266669114534689 35816466485450001835901017)
      ·
        refine ⟨26862349864087501376925763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35816466485450001835901017 26862349864087501376925763)
        ·
          refine ⟨40293524796131252065388645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26862349864087501376925763 40293524796131252065388645)
          ·
            refine ⟨7555035899274609762260371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40293524796131252065388645 7555035899274609762260371)
            ·
              refine ⟨11332553848911914643390557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555035899274609762260371 11332553848911914643390557)
              ·
                refine ⟨4249707693341967991271459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11332553848911914643390557 4249707693341967991271459)
                ·
                  refine ⟨6374561540012951986907189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249707693341967991271459 6374561540012951986907189)
                  ·
                    refine ⟨597615144376214248772549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6374561540012951986907189 597615144376214248772549)
                    ·
                      rfl

theorem cell22_1745777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1745777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745777 prefixEnd_1745777 := by exact prefixLift 1745777
  have htrace : WordTrace (prefixWord ++ tailWord_1745777) baseStart_1745777 baseEnd_1745777 := by
    simpa [prefixWord, tailWord_1745777, baseEnd_1745777] using wordTrace_append hprefix tailTrace_1745777
  have hstable : (prefixWord ++ tailWord_1745777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745777).length < 2 ^ (prefixWord ++ tailWord_1745777).sum := by decide
  have hdescent : baseEnd_1745777 < baseStart_1745777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745792 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_1745792 : Nat := 118140960795 + 1745792 * 2 ^ 59
def prefixEnd_1745792 : Nat := 4983230072969 + 3 ^ 40 * 1745792 * 2
def baseEnd_1745792 : Nat := 597620279182759209647503

theorem tailTrace_1745792 : CollatzResearch.WordTrace tailWord_1745792 prefixEnd_1745792 597620279182759209647503 := by
  unfold tailWord_1745792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31837132645650608190587815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42449510194200810920783753 31837132645650608190587815)
  ·
    refine ⟨47755698968475912285881723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31837132645650608190587815 47755698968475912285881723)
    ·
      refine ⟨71633548452713868428822585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47755698968475912285881723 71633548452713868428822585)
      ·
        refine ⟨53725161339535401321616939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71633548452713868428822585 53725161339535401321616939)
        ·
          refine ⟨80587742009303101982425409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53725161339535401321616939 80587742009303101982425409)
          ·
            refine ⟨60440806506977326486819057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80587742009303101982425409 60440806506977326486819057)
            ·
              refine ⟨45330604880232994865114293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60440806506977326486819057 45330604880232994865114293)
              ·
                refine ⟨4249744207521843268604465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45330604880232994865114293 4249744207521843268604465)
                ·
                  refine ⟨3187308155641382451453349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4249744207521843268604465 3187308155641382451453349)
                  ·
                    refine ⟨597620279182759209647503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3187308155641382451453349 597620279182759209647503)
                    ·
                      rfl

theorem cell22_1745792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_1745792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745792 prefixEnd_1745792 := by exact prefixLift 1745792
  have htrace : WordTrace (prefixWord ++ tailWord_1745792) baseStart_1745792 baseEnd_1745792 := by
    simpa [prefixWord, tailWord_1745792, baseEnd_1745792] using wordTrace_append hprefix tailTrace_1745792
  have hstable : (prefixWord ++ tailWord_1745792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745792).length < 2 ^ (prefixWord ++ tailWord_1745792).sum := by decide
  have hdescent : baseEnd_1745792 < baseStart_1745792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745841 : List Nat := [1, 2, 2, 4, 3, 2, 2, 6]
def baseStart_1745841 : Nat := 118140960795 + 1745841 * 2 ^ 59
def prefixEnd_1745841 : Nat := 4983230072969 + 3 ^ 40 * 1745841 * 2
def baseEnd_1745841 : Nat := 66404116987126601685817

theorem tailTrace_1745841 : CollatzResearch.WordTrace tailWord_1745841 prefixEnd_1745841 66404116987126601685817 := by
  unfold tailWord_1745841
  simp only [CollatzResearch.WordTrace]
  refine ⟨63676052468123697749709377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42450701645415798499806251 63676052468123697749709377)
  ·
    refine ⟨47757039351092773312282033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63676052468123697749709377 47757039351092773312282033)
    ·
      refine ⟨35817779513319579984211525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47757039351092773312282033 35817779513319579984211525)
      ·
        refine ⟨6715833658747421247039661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35817779513319579984211525 6715833658747421247039661)
        ·
          refine ⟨2518437622030282967639873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6715833658747421247039661 2518437622030282967639873)
          ·
            refine ⟨1888828216522712225729905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518437622030282967639873 1888828216522712225729905)
            ·
              refine ⟨1416621162392034169297429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888828216522712225729905 1416621162392034169297429)
              ·
                refine ⟨66404116987126601685817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416621162392034169297429 66404116987126601685817)
                ·
                  rfl

theorem cell22_1745841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 6].length) (baseStart_1745841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745841 prefixEnd_1745841 := by exact prefixLift 1745841
  have htrace : WordTrace (prefixWord ++ tailWord_1745841) baseStart_1745841 baseEnd_1745841 := by
    simpa [prefixWord, tailWord_1745841, baseEnd_1745841] using wordTrace_append hprefix tailTrace_1745841
  have hstable : (prefixWord ++ tailWord_1745841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745841).length < 2 ^ (prefixWord ++ tailWord_1745841).sum := by decide
  have hdescent : baseEnd_1745841 < baseStart_1745841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745873 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_1745873 : Nat := 118140960795 + 1745873 * 2 ^ 59
def prefixEnd_1745873 : Nat := 4983230072969 + 3 ^ 40 * 1745873 * 2
def baseEnd_1745873 : Nat := 597648007138101998372255

theorem tailTrace_1745873 : CollatzResearch.WordTrace tailWord_1745873 prefixEnd_1745873 597648007138101998372255 := by
  unfold tailWord_1745873
  simp only [CollatzResearch.WordTrace]
  refine ⟨63677219604007767214874273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42451479736005178143249515 63677219604007767214874273)
  ·
    refine ⟨47757914703005825411155705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63677219604007767214874273 47757914703005825411155705)
    ·
      refine ⟨35818436027254369058366779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47757914703005825411155705 35818436027254369058366779)
      ·
        refine ⟨53727654040881553587550169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35818436027254369058366779 53727654040881553587550169)
        ·
          refine ⟨40295740530661165190662627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53727654040881553587550169 40295740530661165190662627)
          ·
            refine ⟨60443610795991747785993941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40295740530661165190662627 60443610795991747785993941)
            ·
              refine ⟨1416647128031056588734233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60443610795991747785993941 1416647128031056588734233)
              ·
                refine ⟨1062485346023292441550675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416647128031056588734233 1062485346023292441550675)
                ·
                  refine ⟨1593728019034938662326013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062485346023292441550675 1593728019034938662326013)
                  ·
                    refine ⟨597648007138101998372255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593728019034938662326013 597648007138101998372255)
                    ·
                      rfl

theorem cell22_1745873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_1745873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745873 prefixEnd_1745873 := by exact prefixLift 1745873
  have htrace : WordTrace (prefixWord ++ tailWord_1745873) baseStart_1745873 baseEnd_1745873 := by
    simpa [prefixWord, tailWord_1745873, baseEnd_1745873] using wordTrace_append hprefix tailTrace_1745873
  have hstable : (prefixWord ++ tailWord_1745873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745873).length < 2 ^ (prefixWord ++ tailWord_1745873).sum := by decide
  have hdescent : baseEnd_1745873 < baseStart_1745873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745929 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_1745929 : Nat := 118140960795 + 1745929 * 2 ^ 59
def prefixEnd_1745929 : Nat := 4983230072969 + 3 ^ 40 * 1745929 * 2
def baseEnd_1745929 : Nat := 597667177082536518972083

theorem tailTrace_1745929 : CollatzResearch.WordTrace tailWord_1745929 prefixEnd_1745929 597667177082536518972083 := by
  unfold tailWord_1745929
  simp only [CollatzResearch.WordTrace]
  refine ⟨63679262091804888778912841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42452841394536592519275227 63679262091804888778912841)
  ·
    refine ⟨47759446568853666584184631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63679262091804888778912841 47759446568853666584184631)
    ·
      refine ⟨71639169853280499876276947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47759446568853666584184631 71639169853280499876276947)
      ·
        refine ⟨107458754779920749814415421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71639169853280499876276947 107458754779920749814415421)
        ·
          refine ⟨40297033042470281180405783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107458754779920749814415421 40297033042470281180405783)
          ·
            refine ⟨60445549563705421770608675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40297033042470281180405783 60445549563705421770608675)
            ·
              refine ⟨90668324345558132655913013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60445549563705421770608675 90668324345558132655913013)
              ·
                refine ⟨8500155407396074936491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90668324345558132655913013 8500155407396074936491845)
                ·
                  refine ⟨1593779138886764050592221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8500155407396074936491845 1593779138886764050592221)
                  ·
                    refine ⟨597667177082536518972083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593779138886764050592221 597667177082536518972083)
                    ·
                      rfl

theorem cell22_1745929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_1745929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745929 prefixEnd_1745929 := by exact prefixLift 1745929
  have htrace : WordTrace (prefixWord ++ tailWord_1745929) baseStart_1745929 baseEnd_1745929 := by
    simpa [prefixWord, tailWord_1745929, baseEnd_1745929] using wordTrace_append hprefix tailTrace_1745929
  have hstable : (prefixWord ++ tailWord_1745929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745929).length < 2 ^ (prefixWord ++ tailWord_1745929).sum := by decide
  have hdescent : baseEnd_1745929 < baseStart_1745929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745931 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 4]
def baseStart_1745931 : Nat := 118140960795 + 1745931 * 2 ^ 59
def prefixEnd_1745931 : Nat := 4983230072969 + 3 ^ 40 * 1745931 * 2
def baseEnd_1745931 : Nat := 199222620574469726807359

theorem tailTrace_1745931 : CollatzResearch.WordTrace tailWord_1745931 prefixEnd_1745931 199222620574469726807359 := by
  unfold tailWord_1745931
  simp only [CollatzResearch.WordTrace]
  refine ⟨63679335037797643120485647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42452890025198428746990431 63679335037797643120485647)
  ·
    refine ⟨95519002556696464680728471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63679335037797643120485647 95519002556696464680728471)
    ·
      refine ⟨143278503835044697021092707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95519002556696464680728471 143278503835044697021092707)
      ·
        refine ⟨214917755752567045531639061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143278503835044697021092707 214917755752567045531639061)
        ·
          refine ⟨10074269800901580259295581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214917755752567045531639061 10074269800901580259295581)
          ·
            refine ⟨3777851175338092597235843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10074269800901580259295581 3777851175338092597235843)
            ·
              refine ⟨5666776763007138895853765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777851175338092597235843 5666776763007138895853765)
              ·
                refine ⟨1062520643063838542972581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5666776763007138895853765 1062520643063838542972581)
                ·
                  refine ⟨199222620574469726807359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062520643063838542972581 199222620574469726807359)
                  ·
                    rfl

theorem cell22_1745931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 4].length) (baseStart_1745931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745931 prefixEnd_1745931 := by exact prefixLift 1745931
  have htrace : WordTrace (prefixWord ++ tailWord_1745931) baseStart_1745931 baseEnd_1745931 := by
    simpa [prefixWord, tailWord_1745931, baseEnd_1745931] using wordTrace_append hprefix tailTrace_1745931
  have hstable : (prefixWord ++ tailWord_1745931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745931).length < 2 ^ (prefixWord ++ tailWord_1745931).sum := by decide
  have hdescent : baseEnd_1745931 < baseStart_1745931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745946 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1745946 : Nat := 118140960795 + 1745946 * 2 ^ 59
def prefixEnd_1745946 : Nat := 4983230072969 + 3 ^ 40 * 1745946 * 2
def baseEnd_1745946 : Nat := 597672996529954141297031

theorem tailTrace_1745946 : CollatzResearch.WordTrace tailWord_1745946 prefixEnd_1745946 597672996529954141297031 := by
  unfold tailWord_1745946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919970533185825170570423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42453254755162200454854461 15919970533185825170570423)
  ·
    refine ⟨23879955799778737755855635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15919970533185825170570423 23879955799778737755855635)
    ·
      refine ⟨35819933699668106633783453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23879955799778737755855635 35819933699668106633783453)
      ·
        refine ⟨13432475137375539987668795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35819933699668106633783453 13432475137375539987668795)
        ·
          refine ⟨20148712706063309981503193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432475137375539987668795 20148712706063309981503193)
          ·
            refine ⟨15111534529547482486127395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20148712706063309981503193 15111534529547482486127395)
            ·
              refine ⟨22667301794321223729191093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15111534529547482486127395 22667301794321223729191093)
              ·
                refine ⟨2125059543217614724611665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22667301794321223729191093 2125059543217614724611665)
                ·
                  refine ⟨1593794657413211043458749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125059543217614724611665 1593794657413211043458749)
                  ·
                    refine ⟨597672996529954141297031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593794657413211043458749 597672996529954141297031)
                    ·
                      rfl

theorem cell22_1745946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1745946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745946 prefixEnd_1745946 := by exact prefixLift 1745946
  have htrace : WordTrace (prefixWord ++ tailWord_1745946) baseStart_1745946 baseEnd_1745946 := by
    simpa [prefixWord, tailWord_1745946, baseEnd_1745946] using wordTrace_append hprefix tailTrace_1745946
  have hstable : (prefixWord ++ tailWord_1745946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745946).length < 2 ^ (prefixWord ++ tailWord_1745946).sum := by decide
  have hdescent : baseEnd_1745946 < baseStart_1745946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745991 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1745991 : Nat := 118140960795 + 1745991 * 2 ^ 59
def prefixEnd_1745991 : Nat := 4983230072969 + 3 ^ 40 * 1745991 * 2
def baseEnd_1745991 : Nat := 597688400949589023921893

theorem tailTrace_1745991 : CollatzResearch.WordTrace tailWord_1745991 prefixEnd_1745991 597688400949589023921893 := by
  unfold tailWord_1745991
  simp only [CollatzResearch.WordTrace]
  refine ⟨63681523417580273367669827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42454348945053515578446551 63681523417580273367669827)
  ·
    refine ⟨95522285126370410051504741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63681523417580273367669827 95522285126370410051504741)
    ·
      refine ⟨17910428461194451884657139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95522285126370410051504741 17910428461194451884657139)
      ·
        refine ⟨26865642691791677826985709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17910428461194451884657139 26865642691791677826985709)
        ·
          refine ⟨10074616009421879185119641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26865642691791677826985709 10074616009421879185119641)
          ·
            refine ⟨7555962007066409388839731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074616009421879185119641 7555962007066409388839731)
            ·
              refine ⟨11333943010599614083259597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555962007066409388839731 11333943010599614083259597)
              ·
                refine ⟨4250228628974855281222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11333943010599614083259597 4250228628974855281222349)
                ·
                  refine ⟨1593835735865570730458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4250228628974855281222349 1593835735865570730458381)
                  ·
                    refine ⟨597688400949589023921893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593835735865570730458381 597688400949589023921893)
                    ·
                      rfl

theorem cell22_1745991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1745991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1745991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1745991 prefixEnd_1745991 := by exact prefixLift 1745991
  have htrace : WordTrace (prefixWord ++ tailWord_1745991) baseStart_1745991 baseEnd_1745991 := by
    simpa [prefixWord, tailWord_1745991, baseEnd_1745991] using wordTrace_append hprefix tailTrace_1745991
  have hstable : (prefixWord ++ tailWord_1745991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745991).length < 2 ^ (prefixWord ++ tailWord_1745991).sum := by decide
  have hdescent : baseEnd_1745991 < baseStart_1745991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746025 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_1746025 : Nat := 118140960795 + 1746025 * 2 ^ 59
def prefixEnd_1746025 : Nat := 4983230072969 + 3 ^ 40 * 1746025 * 2
def baseEnd_1746025 : Nat := 597700039844424268571789

theorem tailTrace_1746025 : CollatzResearch.WordTrace tailWord_1746025 prefixEnd_1746025 597700039844424268571789 := by
  unfold tailWord_1746025
  simp only [CollatzResearch.WordTrace]
  refine ⟨63682763499457097174407529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42455175666304731449605019 63682763499457097174407529)
  ·
    refine ⟨47762072624592822880805647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63682763499457097174407529 47762072624592822880805647)
    ·
      refine ⟨71643108936889234321208471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47762072624592822880805647 71643108936889234321208471)
      ·
        refine ⟨107464663405333851481812707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71643108936889234321208471 107464663405333851481812707)
        ·
          refine ⟨161196995108000777222719061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107464663405333851481812707 161196995108000777222719061)
          ·
            refine ⟨1889027286421884108078739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 161196995108000777222719061 1889027286421884108078739)
            ·
              refine ⟨2833540929632826162118109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889027286421884108078739 2833540929632826162118109)
              ·
                refine ⟨1062577848612309810794291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833540929632826162118109 1062577848612309810794291)
                ·
                  refine ⟨1593866772918464716191437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062577848612309810794291 1593866772918464716191437)
                  ·
                    refine ⟨597700039844424268571789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593866772918464716191437 597700039844424268571789)
                    ·
                      rfl

theorem cell22_1746025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_1746025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746025 prefixEnd_1746025 := by exact prefixLift 1746025
  have htrace : WordTrace (prefixWord ++ tailWord_1746025) baseStart_1746025 baseEnd_1746025 := by
    simpa [prefixWord, tailWord_1746025, baseEnd_1746025] using wordTrace_append hprefix tailTrace_1746025
  have hstable : (prefixWord ++ tailWord_1746025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746025).length < 2 ^ (prefixWord ++ tailWord_1746025).sum := by decide
  have hdescent : baseEnd_1746025 < baseStart_1746025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746081 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1746081 : Nat := 118140960795 + 1746081 * 2 ^ 59
def prefixEnd_1746081 : Nat := 4983230072969 + 3 ^ 40 * 1746081 * 2
def baseEnd_1746081 : Nat := 597719209788858789171617

theorem tailTrace_1746081 : CollatzResearch.WordTrace tailWord_1746081 prefixEnd_1746081 597719209788858789171617 := by
  unfold tailWord_1746081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63684805987254218738446097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42456537324836145825630731 63684805987254218738446097)
  ·
    refine ⟨47763604490440664053834573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63684805987254218738446097 47763604490440664053834573)
    ·
      refine ⟨17911351683915249020187965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47763604490440664053834573 17911351683915249020187965)
      ·
        refine ⟨6716756881468218382570487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17911351683915249020187965 6716756881468218382570487)
        ·
          refine ⟨10075135322202327573855731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716756881468218382570487 10075135322202327573855731)
          ·
            refine ⟨15112702983303491360783597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075135322202327573855731 15112702983303491360783597)
            ·
              refine ⟨5667263618738809260293849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15112702983303491360783597 5667263618738809260293849)
              ·
                refine ⟨4250447714054106945220387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667263618738809260293849 4250447714054106945220387)
                ·
                  refine ⟨6375671571081160417830581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250447714054106945220387 6375671571081160417830581)
                  ·
                    refine ⟨597719209788858789171617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6375671571081160417830581 597719209788858789171617)
                    ·
                      rfl

theorem cell22_1746081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1746081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746081 prefixEnd_1746081 := by exact prefixLift 1746081
  have htrace : WordTrace (prefixWord ++ tailWord_1746081) baseStart_1746081 baseEnd_1746081 := by
    simpa [prefixWord, tailWord_1746081, baseEnd_1746081] using wordTrace_append hprefix tailTrace_1746081
  have hstable : (prefixWord ++ tailWord_1746081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746081).length < 2 ^ (prefixWord ++ tailWord_1746081).sum := by decide
  have hdescent : baseEnd_1746081 < baseStart_1746081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746098 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1746098 : Nat := 118140960795 + 1746098 * 2 ^ 59
def prefixEnd_1746098 : Nat := 4983230072969 + 3 ^ 40 * 1746098 * 2
def baseEnd_1746098 : Nat := 597725029236276411496565

theorem tailTrace_1746098 : CollatzResearch.WordTrace tailWord_1746098 prefixEnd_1746098 597725029236276411496565 := by
  unfold tailWord_1746098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921356507048157660453737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42456950685461753761209965 15921356507048157660453737)
  ·
    refine ⟨11941017380286118245340303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15921356507048157660453737 11941017380286118245340303)
    ·
      refine ⟨17911526070429177368010455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11941017380286118245340303 17911526070429177368010455)
      ·
        refine ⟨26867289105643766052015683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911526070429177368010455 26867289105643766052015683)
        ·
          refine ⟨40300933658465649078023525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867289105643766052015683 40300933658465649078023525)
          ·
            refine ⟨7556425060962309202129411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40300933658465649078023525 7556425060962309202129411)
            ·
              refine ⟨11334637591443463803194117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556425060962309202129411 11334637591443463803194117)
              ·
                refine ⟨2125244548395649463098897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11334637591443463803194117 2125244548395649463098897)
                ·
                  refine ⟨1593933411296737097324173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125244548395649463098897 1593933411296737097324173)
                  ·
                    refine ⟨597725029236276411496565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1593933411296737097324173 597725029236276411496565)
                    ·
                      rfl

theorem cell22_1746098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1746098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746098 prefixEnd_1746098 := by exact prefixLift 1746098
  have htrace : WordTrace (prefixWord ++ tailWord_1746098) baseStart_1746098 baseEnd_1746098 := by
    simpa [prefixWord, tailWord_1746098, baseEnd_1746098] using wordTrace_append hprefix tailTrace_1746098
  have hstable : (prefixWord ++ tailWord_1746098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746098).length < 2 ^ (prefixWord ++ tailWord_1746098).sum := by decide
  have hdescent : baseEnd_1746098 < baseStart_1746098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746156 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_1746156 : Nat := 118140960795 + 1746156 * 2 ^ 59
def prefixEnd_1746156 : Nat := 4983230072969 + 3 ^ 40 * 1746156 * 2
def baseEnd_1746156 : Nat := 199248294607194531182129

theorem tailTrace_1746156 : CollatzResearch.WordTrace tailWord_1746156 prefixEnd_1746156 199248294607194531182129 := by
  unfold tailWord_1746156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31843770730991253273713161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42458360974655004364950881 31843770730991253273713161)
  ·
    refine ⟨23882828048243439955284871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31843770730991253273713161 23882828048243439955284871)
    ·
      refine ⟨35824242072365159932927307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23882828048243439955284871 35824242072365159932927307)
      ·
        refine ⟨53736363108547739899390961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35824242072365159932927307 53736363108547739899390961)
        ·
          refine ⟨40302272331410804924543221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53736363108547739899390961 40302272331410804924543221)
          ·
            refine ⟨3778338031069762961675927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40302272331410804924543221 3778338031069762961675927)
            ·
              refine ⟨5667507046604644442513891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778338031069762961675927 5667507046604644442513891)
              ·
                refine ⟨8501260569906966663770837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667507046604644442513891 8501260569906966663770837)
                ·
                  refine ⟨199248294607194531182129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8501260569906966663770837 199248294607194531182129)
                  ·
                    rfl

theorem cell22_1746156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_1746156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746156 prefixEnd_1746156 := by exact prefixLift 1746156
  have htrace : WordTrace (prefixWord ++ tailWord_1746156) baseStart_1746156 baseEnd_1746156 := by
    simpa [prefixWord, tailWord_1746156, baseEnd_1746156] using wordTrace_append hprefix tailTrace_1746156
  have hstable : (prefixWord ++ tailWord_1746156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746156).length < 2 ^ (prefixWord ++ tailWord_1746156).sum := by decide
  have hdescent : baseEnd_1746156 < baseStart_1746156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746262 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1746262 : Nat := 118140960795 + 1746262 * 2 ^ 59
def prefixEnd_1746262 : Nat := 4983230072969 + 3 ^ 40 * 1746262 * 2
def baseEnd_1746262 : Nat := 597781169787834650396063

theorem tailTrace_1746262 : CollatzResearch.WordTrace tailWord_1746262 prefixEnd_1746262 597781169787834650396063 := by
  unfold tailWord_1746262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980712974974905415674065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42460938399732324433856693 3980712974974905415674065)
  ·
    refine ⟨2985534731231179061755549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3980712974974905415674065 2985534731231179061755549)
    ·
      refine ⟨1119575524211692148158331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2985534731231179061755549 1119575524211692148158331)
      ·
        refine ⟨1679363286317538222237497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119575524211692148158331 1679363286317538222237497)
        ·
          refine ⟨1259522464738153666678123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679363286317538222237497 1259522464738153666678123)
          ·
            refine ⟨1889283697107230500017185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259522464738153666678123 1889283697107230500017185)
            ·
              refine ⟨1416962772830422875012889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889283697107230500017185 1416962772830422875012889)
              ·
                refine ⟨1062722079622817156259667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416962772830422875012889 1062722079622817156259667)
                ·
                  refine ⟨1594083119434225734389501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062722079622817156259667 1594083119434225734389501)
                  ·
                    refine ⟨597781169787834650396063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594083119434225734389501 597781169787834650396063)
                    ·
                      rfl

theorem cell22_1746262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1746262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746262 prefixEnd_1746262 := by exact prefixLift 1746262
  have htrace : WordTrace (prefixWord ++ tailWord_1746262) baseStart_1746262 baseEnd_1746262 := by
    simpa [prefixWord, tailWord_1746262, baseEnd_1746262] using wordTrace_append hprefix tailTrace_1746262
  have hstable : (prefixWord ++ tailWord_1746262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746262).length < 2 ^ (prefixWord ++ tailWord_1746262).sum := by decide
  have hdescent : baseEnd_1746262 < baseStart_1746262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746280 : List Nat := [2, 1, 4, 2, 3, 2, 1, 7]
def baseStart_1746280 : Nat := 118140960795 + 1746280 * 2 ^ 59
def prefixEnd_1746280 : Nat := 4983230072969 + 3 ^ 40 * 1746280 * 2
def baseEnd_1746280 : Nat := 66420814617298733716223

theorem tailTrace_1746280 : CollatzResearch.WordTrace tailWord_1746280 prefixEnd_1746280 66420814617298733716223 := by
  unfold tailWord_1746280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846032056766637862470147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42461376075688850483293529 31846032056766637862470147)
  ·
    refine ⟨47769048085149956793705221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31846032056766637862470147 47769048085149956793705221)
    ·
      refine ⟨8956696515965616898819729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47769048085149956793705221 8956696515965616898819729)
      ·
        refine ⟨6717522386974212674114797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956696515965616898819729 6717522386974212674114797)
        ·
          refine ⟨2519070895115329752793049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6717522386974212674114797 2519070895115329752793049)
          ·
            refine ⟨1889303171336497314594787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2519070895115329752793049 1889303171336497314594787)
            ·
              refine ⟨2833954757004745971892181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889303171336497314594787 2833954757004745971892181)
              ·
                refine ⟨66420814617298733716223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2833954757004745971892181 66420814617298733716223)
                ·
                  rfl

theorem cell22_1746280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_1746280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746280 prefixEnd_1746280 := by exact prefixLift 1746280
  have htrace : WordTrace (prefixWord ++ tailWord_1746280) baseStart_1746280 baseEnd_1746280 := by
    simpa [prefixWord, tailWord_1746280, baseEnd_1746280] using wordTrace_append hprefix tailTrace_1746280
  have hstable : (prefixWord ++ tailWord_1746280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746280).length < 2 ^ (prefixWord ++ tailWord_1746280).sum := by decide
  have hdescent : baseEnd_1746280 < baseStart_1746280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746312 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_1746312 : Nat := 118140960795 + 1746312 * 2 ^ 59
def prefixEnd_1746312 : Nat := 4983230072969 + 3 ^ 40 * 1746312 * 2
def baseEnd_1746312 : Nat := 597798285809651186645909

theorem tailTrace_1746312 : CollatzResearch.WordTrace tailWord_1746312 prefixEnd_1746312 597798285809651186645909 := by
  unfold tailWord_1746312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846615624708672595052595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42462154166278230126736793 31846615624708672595052595)
  ·
    refine ⟨47769923437063008892578893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31846615624708672595052595 47769923437063008892578893)
    ·
      refine ⟨17913721288898628334717085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47769923437063008892578893 17913721288898628334717085)
      ·
        refine ⟨6717645483336985625518907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17913721288898628334717085 6717645483336985625518907)
        ·
          refine ⟨10076468225005478438278361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717645483336985625518907 10076468225005478438278361)
          ·
            refine ⟨7557351168754108828708771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076468225005478438278361 7557351168754108828708771)
            ·
              refine ⟨11336026753131163243063157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557351168754108828708771 11336026753131163243063157)
              ·
                refine ⟨1062752508106046554037171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11336026753131163243063157 1062752508106046554037171)
                ·
                  refine ⟨1594128762159069831055757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062752508106046554037171 1594128762159069831055757)
                  ·
                    refine ⟨597798285809651186645909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594128762159069831055757 597798285809651186645909)
                    ·
                      rfl

theorem cell22_1746312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_1746312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746312 prefixEnd_1746312 := by exact prefixLift 1746312
  have htrace : WordTrace (prefixWord ++ tailWord_1746312) baseStart_1746312 baseEnd_1746312 := by
    simpa [prefixWord, tailWord_1746312, baseEnd_1746312] using wordTrace_append hprefix tailTrace_1746312
  have hstable : (prefixWord ++ tailWord_1746312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746312).length < 2 ^ (prefixWord ++ tailWord_1746312).sum := by decide
  have hdescent : baseEnd_1746312 < baseStart_1746312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746353 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 6]
def baseStart_1746353 : Nat := 118140960795 + 1746353 * 2 ^ 59
def prefixEnd_1746353 : Nat := 4983230072969 + 3 ^ 40 * 1746353 * 2
def baseEnd_1746353 : Nat := 199270773649180248790261

theorem tailTrace_1746353 : CollatzResearch.WordTrace tailWord_1746353 prefixEnd_1746353 199270773649180248790261 := by
  unfold tailWord_1746353
  simp only [CollatzResearch.WordTrace]
  refine ⟨63694726642268809192347713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42463151094845872794898475 63694726642268809192347713)
  ·
    refine ⟨47771044981701606894260785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63694726642268809192347713 47771044981701606894260785)
    ·
      refine ⟨35828283736276205170695589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47771044981701606894260785 35828283736276205170695589)
      ·
        refine ⟨6717803200551788469505423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35828283736276205170695589 6717803200551788469505423)
        ·
          refine ⟨10076704800827682704258135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717803200551788469505423 10076704800827682704258135)
          ·
            refine ⟨15115057201241524056387203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076704800827682704258135 15115057201241524056387203)
            ·
              refine ⟨22672585801862286084580805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115057201241524056387203 22672585801862286084580805)
              ·
                refine ⟨4251109837849178640858901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22672585801862286084580805 4251109837849178640858901)
                ·
                  refine ⟨199270773649180248790261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4251109837849178640858901 199270773649180248790261)
                  ·
                    rfl

theorem cell22_1746353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_1746353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746353 prefixEnd_1746353 := by exact prefixLift 1746353
  have htrace : WordTrace (prefixWord ++ tailWord_1746353) baseStart_1746353 baseEnd_1746353 := by
    simpa [prefixWord, tailWord_1746353, baseEnd_1746353] using wordTrace_append hprefix tailTrace_1746353
  have hstable : (prefixWord ++ tailWord_1746353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746353).length < 2 ^ (prefixWord ++ tailWord_1746353).sum := by decide
  have hdescent : baseEnd_1746353 < baseStart_1746353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746368 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_1746368 : Nat := 118140960795 + 1746368 * 2 ^ 59
def prefixEnd_1746368 : Nat := 4983230072969 + 3 ^ 40 * 1746368 * 2
def baseEnd_1746368 : Nat := 597817455754085707245737

theorem tailTrace_1746368 : CollatzResearch.WordTrace tailWord_1746368 prefixEnd_1746368 597817455754085707245737 := by
  unfold tailWord_1746368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847636868607233377071879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42463515824809644502762505 31847636868607233377071879)
  ·
    refine ⟨47771455302910850065607819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31847636868607233377071879 47771455302910850065607819)
    ·
      refine ⟨71657182954366275098411729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47771455302910850065607819 71657182954366275098411729)
      ·
        refine ⟨53742887215774706323808797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71657182954366275098411729 53742887215774706323808797)
        ·
          refine ⟨20153582705915514871428299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53742887215774706323808797 20153582705915514871428299)
          ·
            refine ⟨30230374058873272307142449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20153582705915514871428299 30230374058873272307142449)
            ·
              refine ⟨22672780544154954230356837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30230374058873272307142449 22672780544154954230356837)
              ·
                refine ⟨4251146352029053918191907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22672780544154954230356837 4251146352029053918191907)
                ·
                  refine ⟨6376719528043580877287861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251146352029053918191907 6376719528043580877287861)
                  ·
                    refine ⟨597817455754085707245737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6376719528043580877287861 597817455754085707245737)
                    ·
                      rfl

theorem cell22_1746368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_1746368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746368 prefixEnd_1746368 := by exact prefixLift 1746368
  have htrace : WordTrace (prefixWord ++ tailWord_1746368) baseStart_1746368 baseEnd_1746368 := by
    simpa [prefixWord, tailWord_1746368, baseEnd_1746368] using wordTrace_append hprefix tailTrace_1746368
  have hstable : (prefixWord ++ tailWord_1746368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746368).length < 2 ^ (prefixWord ++ tailWord_1746368).sum := by decide
  have hdescent : baseEnd_1746368 < baseStart_1746368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746372 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1746372 : Nat := 118140960795 + 1746372 * 2 ^ 59
def prefixEnd_1746372 : Nat := 4983230072969 + 3 ^ 40 * 1746372 * 2
def baseEnd_1746372 : Nat := 597818825035831030145725

theorem tailTrace_1746372 : CollatzResearch.WordTrace tailWord_1746372 prefixEnd_1746372 597818825035831030145725 := by
  unfold tailWord_1746372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31847709814599987718644685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42463613086133316958192913 31847709814599987718644685)
  ·
    refine ⟨11942891180474995394491757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31847709814599987718644685 11942891180474995394491757)
    ·
      refine ⟨4478584192678123272934409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11942891180474995394491757 4478584192678123272934409)
      ·
        refine ⟨3358938144508592454700807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4478584192678123272934409 3358938144508592454700807)
        ·
          refine ⟨5038407216762888682051211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358938144508592454700807 5038407216762888682051211)
          ·
            refine ⟨7557610825144333023076817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038407216762888682051211 7557610825144333023076817)
            ·
              refine ⟨5668208118858249767307613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7557610825144333023076817 5668208118858249767307613)
              ·
                refine ⟨2125578044571843662740355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5668208118858249767307613 2125578044571843662740355)
                ·
                  refine ⟨3188367066857765494110533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125578044571843662740355 3188367066857765494110533)
                  ·
                    refine ⟨597818825035831030145725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188367066857765494110533 597818825035831030145725)
                    ·
                      rfl

theorem cell22_1746372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1746372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746372 prefixEnd_1746372 := by exact prefixLift 1746372
  have htrace : WordTrace (prefixWord ++ tailWord_1746372) baseStart_1746372 baseEnd_1746372 := by
    simpa [prefixWord, tailWord_1746372, baseEnd_1746372] using wordTrace_append hprefix tailTrace_1746372
  have hstable : (prefixWord ++ tailWord_1746372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746372).length < 2 ^ (prefixWord ++ tailWord_1746372).sum := by decide
  have hdescent : baseEnd_1746372 < baseStart_1746372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746383 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1746383 : Nat := 118140960795 + 1746383 * 2 ^ 59
def prefixEnd_1746383 : Nat := 4983230072969 + 3 ^ 40 * 1746383 * 2
def baseEnd_1746383 : Nat := 597822590560630668120691

theorem tailTrace_1746383 : CollatzResearch.WordTrace tailWord_1746383 prefixEnd_1746383 597822590560630668120691 := by
  unfold tailWord_1746383
  simp only [CollatzResearch.WordTrace]
  refine ⟨63695820832160124315939803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42463880554773416210626535 63695820832160124315939803)
  ·
    refine ⟨95543731248240186473909705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63695820832160124315939803 95543731248240186473909705)
    ·
      refine ⟨71657798436180139855432279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95543731248240186473909705 71657798436180139855432279)
      ·
        refine ⟨107486697654270209783148419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71657798436180139855432279 107486697654270209783148419)
        ·
          refine ⟨161230046481405314674722629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107486697654270209783148419 161230046481405314674722629)
          ·
            refine ⟨30230633715263496501510493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161230046481405314674722629 30230633715263496501510493)
            ·
              refine ⟨11336487643223811188066435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30230633715263496501510493 11336487643223811188066435)
              ·
                refine ⟨17004731464835716782099653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11336487643223811188066435 17004731464835716782099653)
                ·
                  refine ⟨3188387149656696896643685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17004731464835716782099653 3188387149656696896643685)
                  ·
                    refine ⟨597822590560630668120691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188387149656696896643685 597822590560630668120691)
                    ·
                      rfl

theorem cell22_1746383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1746383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746383 prefixEnd_1746383 := by exact prefixLift 1746383
  have htrace : WordTrace (prefixWord ++ tailWord_1746383) baseStart_1746383 baseEnd_1746383 := by
    simpa [prefixWord, tailWord_1746383, baseEnd_1746383] using wordTrace_append hprefix tailTrace_1746383
  have hstable : (prefixWord ++ tailWord_1746383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746383).length < 2 ^ (prefixWord ++ tailWord_1746383).sum := by decide
  have hdescent : baseEnd_1746383 < baseStart_1746383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746438 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1746438 : Nat := 118140960795 + 1746438 * 2 ^ 59
def prefixEnd_1746438 : Nat := 4983230072969 + 3 ^ 40 * 1746438 * 2
def baseEnd_1746438 : Nat := 199280472728209619331841

theorem tailTrace_1746438 : CollatzResearch.WordTrace tailWord_1746438 prefixEnd_1746438 199280472728209619331841 := by
  unfold tailWord_1746438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990557088967527147162249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42465217897973912472794645 1990557088967527147162249)
  ·
    refine ⟨1492917816725645360371687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1990557088967527147162249 1492917816725645360371687)
    ·
      refine ⟨2239376725088468040557531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492917816725645360371687 2239376725088468040557531)
      ·
        refine ⟨3359065087632702060836297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239376725088468040557531 3359065087632702060836297)
        ·
          refine ⟨2519298815724526545627223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359065087632702060836297 2519298815724526545627223)
          ·
            refine ⟨3778948223586789818440835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519298815724526545627223 3778948223586789818440835)
            ·
              refine ⟨5668422335380184727661253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3778948223586789818440835 5668422335380184727661253)
              ·
                refine ⟨1062829187883784636436485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5668422335380184727661253 1062829187883784636436485)
                ·
                  refine ⟨199280472728209619331841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062829187883784636436485 199280472728209619331841)
                  ·
                    rfl

theorem cell22_1746438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1746438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746438 prefixEnd_1746438 := by exact prefixLift 1746438
  have htrace : WordTrace (prefixWord ++ tailWord_1746438) baseStart_1746438 baseEnd_1746438 := by
    simpa [prefixWord, tailWord_1746438, baseEnd_1746438] using wordTrace_append hprefix tailTrace_1746438
  have hstable : (prefixWord ++ tailWord_1746438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746438).length < 2 ^ (prefixWord ++ tailWord_1746438).sum := by decide
  have hdescent : baseEnd_1746438 < baseStart_1746438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746460 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1746460 : Nat := 118140960795 + 1746460 * 2 ^ 59
def prefixEnd_1746460 : Nat := 4983230072969 + 3 ^ 40 * 1746460 * 2
def baseEnd_1746460 : Nat := 199282983078076044648485

theorem tailTrace_1746460 : CollatzResearch.WordTrace tailWord_1746460 prefixEnd_1746460 199282983078076044648485 := by
  unfold tailWord_1746460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31849314626440583233246417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42465752835254110977661889 31849314626440583233246417)
  ·
    refine ⟨23886985969830437424934813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31849314626440583233246417 23886985969830437424934813)
    ·
      refine ⟨8957619738686414034350555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23886985969830437424934813 8957619738686414034350555)
      ·
        refine ⟨13436429608029621051525833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8957619738686414034350555 13436429608029621051525833)
        ·
          refine ⟨10077322206022215788644375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13436429608029621051525833 10077322206022215788644375)
          ·
            refine ⟨15115983309033323682966563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077322206022215788644375 15115983309033323682966563)
            ·
              refine ⟨22673974963549985524449845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115983309033323682966563 22673974963549985524449845)
              ·
                refine ⟨2125685152832811142917173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22673974963549985524449845 2125685152832811142917173)
                ·
                  refine ⟨199282983078076044648485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2125685152832811142917173 199282983078076044648485)
                  ·
                    rfl

theorem cell22_1746460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1746460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746460 prefixEnd_1746460 := by exact prefixLift 1746460
  have htrace : WordTrace (prefixWord ++ tailWord_1746460) baseStart_1746460 baseEnd_1746460 := by
    simpa [prefixWord, tailWord_1746460, baseEnd_1746460] using wordTrace_append hprefix tailTrace_1746460
  have hstable : (prefixWord ++ tailWord_1746460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746460).length < 2 ^ (prefixWord ++ tailWord_1746460).sum := by decide
  have hdescent : baseEnd_1746460 < baseStart_1746460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746524 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1746524 : Nat := 118140960795 + 1746524 * 2 ^ 59
def prefixEnd_1746524 : Nat := 4983230072969 + 3 ^ 40 * 1746524 * 2
def baseEnd_1746524 : Nat := 597870857742153300345259

theorem tailTrace_1746524 : CollatzResearch.WordTrace tailWord_1746524 prefixEnd_1746524 597870857742153300345259 := by
  unfold tailWord_1746524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31850481762324652698411313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42467309016432870264548417 31850481762324652698411313)
  ·
    refine ⟨23887861321743489523808485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31850481762324652698411313 23887861321743489523808485)
    ·
      refine ⟨4478973997826904285714091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23887861321743489523808485 4478973997826904285714091)
      ·
        refine ⟨6718460996740356428571137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478973997826904285714091 6718460996740356428571137)
        ·
          refine ⟨5038845747555267321428353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718460996740356428571137 5038845747555267321428353)
          ·
            refine ⟨3779134310666450491071265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038845747555267321428353 3779134310666450491071265)
            ·
              refine ⟨2834350732999837868303449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779134310666450491071265 2834350732999837868303449)
              ·
                refine ⟨2125763049749878401227587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834350732999837868303449 2125763049749878401227587)
                ·
                  refine ⟨3188644574624817601841381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125763049749878401227587 3188644574624817601841381)
                  ·
                    refine ⟨597870857742153300345259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3188644574624817601841381 597870857742153300345259)
                    ·
                      rfl

theorem cell22_1746524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1746524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746524 prefixEnd_1746524 := by exact prefixLift 1746524
  have htrace : WordTrace (prefixWord ++ tailWord_1746524) baseStart_1746524 baseEnd_1746524 := by
    simpa [prefixWord, tailWord_1746524, baseEnd_1746524] using wordTrace_append hprefix tailTrace_1746524
  have hstable : (prefixWord ++ tailWord_1746524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746524).length < 2 ^ (prefixWord ++ tailWord_1746524).sum := by decide
  have hdescent : baseEnd_1746524 < baseStart_1746524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746535 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1746535 : Nat := 118140960795 + 1746535 * 2 ^ 59
def prefixEnd_1746535 : Nat := 4983230072969 + 3 ^ 40 * 1746535 * 2
def baseEnd_1746535 : Nat := 597874623266952938320225

theorem tailTrace_1746535 : CollatzResearch.WordTrace tailWord_1746535 prefixEnd_1746535 597874623266952938320225 := by
  unfold tailWord_1746535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63701364727609454275473059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42467576485072969516982039 63701364727609454275473059)
  ·
    refine ⟨95552047091414181413209589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63701364727609454275473059 95552047091414181413209589)
    ·
      refine ⟨8958004414820079507488399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95552047091414181413209589 8958004414820079507488399)
      ·
        refine ⟨13437006622230119261232599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958004414820079507488399 13437006622230119261232599)
        ·
          refine ⟨20155509933345178891848899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437006622230119261232599 20155509933345178891848899)
          ·
            refine ⟨30233264900017768337773349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20155509933345178891848899 30233264900017768337773349)
            ·
              refine ⟨5668737168753331563332503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30233264900017768337773349 5668737168753331563332503)
              ·
                refine ⟨8503105753129997344998755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668737168753331563332503 8503105753129997344998755)
                ·
                  refine ⟨12754658629694996017498133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503105753129997344998755 12754658629694996017498133)
                  ·
                    refine ⟨597874623266952938320225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12754658629694996017498133 597874623266952938320225)
                    ·
                      rfl

theorem cell22_1746535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1746535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746535 prefixEnd_1746535 := by exact prefixLift 1746535
  have htrace : WordTrace (prefixWord ++ tailWord_1746535) baseStart_1746535 baseEnd_1746535 := by
    simpa [prefixWord, tailWord_1746535, baseEnd_1746535] using wordTrace_append hprefix tailTrace_1746535
  have hstable : (prefixWord ++ tailWord_1746535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746535).length < 2 ^ (prefixWord ++ tailWord_1746535).sum := by decide
  have hdescent : baseEnd_1746535 < baseStart_1746535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746614 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1746614 : Nat := 118140960795 + 1746614 * 2 ^ 59
def prefixEnd_1746614 : Nat := 4983230072969 + 3 ^ 40 * 1746614 * 2
def baseEnd_1746614 : Nat := 597901666581423065594983

theorem tailTrace_1746614 : CollatzResearch.WordTrace tailWord_1746614 prefixEnd_1746614 597901666581423065594983 := by
  unfold tailWord_1746614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981515380895203172974931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42469497396215500511732597 3981515380895203172974931)
  ·
    refine ⟨5972273071342804759462397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981515380895203172974931 5972273071342804759462397)
    ·
      refine ⟨2239602401753551784798399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5972273071342804759462397 2239602401753551784798399)
      ·
        refine ⟨3359403602630327677197599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239602401753551784798399 3359403602630327677197599)
        ·
          refine ⟨5039105403945491515796399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359403602630327677197599 5039105403945491515796399)
          ·
            refine ⟨7558658105918237273694599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039105403945491515796399 7558658105918237273694599)
            ·
              refine ⟨11337987158877355910541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558658105918237273694599 11337987158877355910541899)
              ·
                refine ⟨17006980738316033865812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11337987158877355910541899 17006980738316033865812849)
                ·
                  refine ⟨12755235553737025399359637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17006980738316033865812849 12755235553737025399359637)
                  ·
                    refine ⟨597901666581423065594983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12755235553737025399359637 597901666581423065594983)
                    ·
                      rfl

theorem cell22_1746614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1746614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746614 prefixEnd_1746614 := by exact prefixLift 1746614
  have htrace : WordTrace (prefixWord ++ tailWord_1746614) baseStart_1746614 baseEnd_1746614 := by
    simpa [prefixWord, tailWord_1746614, baseEnd_1746614] using wordTrace_append hprefix tailTrace_1746614
  have hstable : (prefixWord ++ tailWord_1746614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746614).length < 2 ^ (prefixWord ++ tailWord_1746614).sum := by decide
  have hdescent : baseEnd_1746614 < baseStart_1746614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746663 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 5]
def baseStart_1746663 : Nat := 118140960795 + 1746663 * 2 ^ 59
def prefixEnd_1746663 : Nat := 4983230072969 + 3 ^ 40 * 1746663 * 2
def baseEnd_1746663 : Nat := 199306146760934423706611

theorem tailTrace_1746663 : CollatzResearch.WordTrace tailWord_1746663 prefixEnd_1746663 199306146760934423706611 := by
  unfold tailWord_1746663
  simp only [CollatzResearch.WordTrace]
  refine ⟨63706033271145732136132643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42470688847430488090755095 63706033271145732136132643)
  ·
    refine ⟨95559049906718598204198965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63706033271145732136132643 95559049906718598204198965)
    ·
      refine ⟨8958660928754868581643653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95559049906718598204198965 8958660928754868581643653)
      ·
        refine ⟨1679748924141537859058185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8958660928754868581643653 1679748924141537859058185)
        ·
          refine ⟨1259811693106153394293639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679748924141537859058185 1259811693106153394293639)
          ·
            refine ⟨1889717539659230091440459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259811693106153394293639 1889717539659230091440459)
            ·
              refine ⟨2834576309488845137160689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889717539659230091440459 2834576309488845137160689)
              ·
                refine ⟨2125932232116633852870517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834576309488845137160689 2125932232116633852870517)
                ·
                  refine ⟨199306146760934423706611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2125932232116633852870517 199306146760934423706611)
                  ·
                    rfl

theorem cell22_1746663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 5].length) (baseStart_1746663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746663 prefixEnd_1746663 := by exact prefixLift 1746663
  have htrace : WordTrace (prefixWord ++ tailWord_1746663) baseStart_1746663 baseEnd_1746663 := by
    simpa [prefixWord, tailWord_1746663, baseEnd_1746663] using wordTrace_append hprefix tailTrace_1746663
  have hstable : (prefixWord ++ tailWord_1746663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746663).length < 2 ^ (prefixWord ++ tailWord_1746663).sum := by decide
  have hdescent : baseEnd_1746663 < baseStart_1746663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746674 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1746674 : Nat := 118140960795 + 1746674 * 2 ^ 59
def prefixEnd_1746674 : Nat := 4983230072969 + 3 ^ 40 * 1746674 * 2
def baseEnd_1746674 : Nat := 199307401935867636364933

theorem tailTrace_1746674 : CollatzResearch.WordTrace tailWord_1746674 prefixEnd_1746674 199307401935867636364933 := by
  unfold tailWord_1746674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926608618526470253695769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42470956316070587343188717 15926608618526470253695769)
  ·
    refine ⟨11944956463894852690271827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15926608618526470253695769 11944956463894852690271827)
    ·
      refine ⟨17917434695842279035407741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11944956463894852690271827 17917434695842279035407741)
      ·
        refine ⟨6719038010940854638277903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17917434695842279035407741 6719038010940854638277903)
        ·
          refine ⟨10078557016411281957416855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719038010940854638277903 10078557016411281957416855)
          ·
            refine ⟨15117835524616922936125283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10078557016411281957416855 15117835524616922936125283)
            ·
              refine ⟨22676753286925384404187925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117835524616922936125283 22676753286925384404187925)
              ·
                refine ⟨1062972810324627393946309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22676753286925384404187925 1062972810324627393946309)
                ·
                  refine ⟨199307401935867636364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062972810324627393946309 199307401935867636364933)
                  ·
                    rfl

theorem cell22_1746674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1746674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746674 prefixEnd_1746674 := by exact prefixLift 1746674
  have htrace : WordTrace (prefixWord ++ tailWord_1746674) baseStart_1746674 baseEnd_1746674 := by
    simpa [prefixWord, tailWord_1746674, baseEnd_1746674] using wordTrace_append hprefix tailTrace_1746674
  have hstable : (prefixWord ++ tailWord_1746674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746674).length < 2 ^ (prefixWord ++ tailWord_1746674).sum := by decide
  have hdescent : baseEnd_1746674 < baseStart_1746674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746689 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1746689 : Nat := 118140960795 + 1746689 * 2 ^ 59
def prefixEnd_1746689 : Nat := 4983230072969 + 3 ^ 40 * 1746689 * 2
def baseEnd_1746689 : Nat := 597927340614147869969753

theorem tailTrace_1746689 : CollatzResearch.WordTrace tailWord_1746689 prefixEnd_1746689 597927340614147869969753 := by
  unfold tailWord_1746689
  simp only [CollatzResearch.WordTrace]
  refine ⟨63706981569051538576579121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42471321046034359051052747 63706981569051538576579121)
  ·
    refine ⟨47780236176788653932434341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63706981569051538576579121 47780236176788653932434341)
    ·
      refine ⟨8958794283147872612331439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47780236176788653932434341 8958794283147872612331439)
      ·
        refine ⟨13438191424721808918497159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958794283147872612331439 13438191424721808918497159)
        ·
          refine ⟨20157287137082713377745739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438191424721808918497159 20157287137082713377745739)
          ·
            refine ⟨30235930705624070066618609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157287137082713377745739 30235930705624070066618609)
            ·
              refine ⟨22676948029218052549963957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30235930705624070066618609 22676948029218052549963957)
              ·
                refine ⟨2125963877739192426559121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22676948029218052549963957 2125963877739192426559121)
                ·
                  refine ⟨1594472908304394319919341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2125963877739192426559121 1594472908304394319919341)
                  ·
                    refine ⟨597927340614147869969753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594472908304394319919341 597927340614147869969753)
                    ·
                      rfl

theorem cell22_1746689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1746689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746689 prefixEnd_1746689 := by exact prefixLift 1746689
  have htrace : WordTrace (prefixWord ++ tailWord_1746689) baseStart_1746689 baseEnd_1746689 := by
    simpa [prefixWord, tailWord_1746689, baseEnd_1746689] using wordTrace_append hprefix tailTrace_1746689
  have hstable : (prefixWord ++ tailWord_1746689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746689).length < 2 ^ (prefixWord ++ tailWord_1746689).sum := by decide
  have hdescent : baseEnd_1746689 < baseStart_1746689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746701 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1746701 : Nat := 118140960795 + 1746701 * 2 ^ 59
def prefixEnd_1746701 : Nat := 4983230072969 + 3 ^ 40 * 1746701 * 2
def baseEnd_1746701 : Nat := 597931448459383838669717

theorem tailTrace_1746701 : CollatzResearch.WordTrace tailWord_1746701 prefixEnd_1746701 597931448459383838669717 := by
  unfold tailWord_1746701
  simp only [CollatzResearch.WordTrace]
  refine ⟨63707419245008064626015957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42471612830005376417343971 63707419245008064626015957)
  ·
    refine ⟨1493142638554876514672249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 63707419245008064626015957 1493142638554876514672249)
    ·
      refine ⟨1119856978916157386004187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1493142638554876514672249 1119856978916157386004187)
      ·
        refine ⟨1679785468374236079006281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119856978916157386004187 1679785468374236079006281)
        ·
          refine ⟨1259839101280677059254711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1679785468374236079006281 1259839101280677059254711)
          ·
            refine ⟨1889758651921015588882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259839101280677059254711 1889758651921015588882067)
            ·
              refine ⟨2834637977881523383323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889758651921015588882067 2834637977881523383323101)
              ·
                refine ⟨1062989241705571268746163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2834637977881523383323101 1062989241705571268746163)
                ·
                  refine ⟨1594483862558356903119245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062989241705571268746163 1594483862558356903119245)
                  ·
                    refine ⟨597931448459383838669717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594483862558356903119245 597931448459383838669717)
                    ·
                      rfl

theorem cell22_1746701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1746701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746701 prefixEnd_1746701 := by exact prefixLift 1746701
  have htrace : WordTrace (prefixWord ++ tailWord_1746701) baseStart_1746701 baseEnd_1746701 := by
    simpa [prefixWord, tailWord_1746701, baseEnd_1746701] using wordTrace_append hprefix tailTrace_1746701
  have hstable : (prefixWord ++ tailWord_1746701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746701).length < 2 ^ (prefixWord ++ tailWord_1746701).sum := by decide
  have hdescent : baseEnd_1746701 < baseStart_1746701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746706 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1746706 : Nat := 118140960795 + 1746706 * 2 ^ 59
def prefixEnd_1746706 : Nat := 4983230072969 + 3 ^ 40 * 1746706 * 2
def baseEnd_1746706 : Nat := 597933160061565492294701

theorem tailTrace_1746706 : CollatzResearch.WordTrace tailWord_1746706 prefixEnd_1746706 597933160061565492294701 := by
  unfold tailWord_1746706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15926900402497487619986993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42471734406659966986631981 15926900402497487619986993)
  ·
    refine ⟨11945175301873115714990245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15926900402497487619986993 11945175301873115714990245)
    ·
      refine ⟨2239720369101209196560671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11945175301873115714990245 2239720369101209196560671)
      ·
        refine ⟨3359580553651813794841007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239720369101209196560671 3359580553651813794841007)
        ·
          refine ⟨5039370830477720692261511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359580553651813794841007 5039370830477720692261511)
          ·
            refine ⟨7559056245716581038392267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039370830477720692261511 7559056245716581038392267)
            ·
              refine ⟨11338584368574871557588401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559056245716581038392267 11338584368574871557588401)
              ·
                refine ⟨8503938276431153668191301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11338584368574871557588401 8503938276431153668191301)
                ·
                  refine ⟨1594488426830841312785869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8503938276431153668191301 1594488426830841312785869)
                  ·
                    refine ⟨597933160061565492294701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594488426830841312785869 597933160061565492294701)
                    ·
                      rfl

theorem cell22_1746706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1746706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746706 prefixEnd_1746706 := by exact prefixLift 1746706
  have htrace : WordTrace (prefixWord ++ tailWord_1746706) baseStart_1746706 baseEnd_1746706 := by
    simpa [prefixWord, tailWord_1746706, baseEnd_1746706] using wordTrace_append hprefix tailTrace_1746706
  have hstable : (prefixWord ++ tailWord_1746706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746706).length < 2 ^ (prefixWord ++ tailWord_1746706).sum := by decide
  have hdescent : baseEnd_1746706 < baseStart_1746706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746740 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1746740 : Nat := 118140960795 + 1746740 * 2 ^ 59
def prefixEnd_1746740 : Nat := 4983230072969 + 3 ^ 40 * 1746740 * 2
def baseEnd_1746740 : Nat := 597944798956400736944597

theorem tailTrace_1746740 : CollatzResearch.WordTrace tailWord_1746740 prefixEnd_1746740 597944798956400736944597 := by
  unfold tailWord_1746740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854420845933387143342837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42472561127911182857790449 31854420845933387143342837)
  ·
    refine ⟨2986351954306255044688391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31854420845933387143342837 2986351954306255044688391)
    ·
      refine ⟨4479527931459382567032587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2986351954306255044688391 4479527931459382567032587)
      ·
        refine ⟨6719291897189073850548881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479527931459382567032587 6719291897189073850548881)
        ·
          refine ⟨5039468922891805387911661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6719291897189073850548881 5039468922891805387911661)
          ·
            refine ⟨1889800846084427020466873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5039468922891805387911661 1889800846084427020466873)
            ·
              refine ⟨1417350634563320265350155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889800846084427020466873 1417350634563320265350155)
              ·
                refine ⟨2126025951844980398025233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417350634563320265350155 2126025951844980398025233)
                ·
                  refine ⟨1594519463883735298518925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126025951844980398025233 1594519463883735298518925)
                  ·
                    refine ⟨597944798956400736944597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594519463883735298518925 597944798956400736944597)
                    ·
                      rfl

theorem cell22_1746740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1746740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746740 prefixEnd_1746740 := by exact prefixLift 1746740
  have htrace : WordTrace (prefixWord ++ tailWord_1746740) baseStart_1746740 baseEnd_1746740 := by
    simpa [prefixWord, tailWord_1746740, baseEnd_1746740] using wordTrace_append hprefix tailTrace_1746740
  have hstable : (prefixWord ++ tailWord_1746740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746740).length < 2 ^ (prefixWord ++ tailWord_1746740).sum := by decide
  have hdescent : baseEnd_1746740 < baseStart_1746740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746837 : List Nat := [1, 3, 2, 1, 1, 3, 11]
def baseStart_1746837 : Nat := 118140960795 + 1746837 * 2 ^ 59
def prefixEnd_1746837 : Nat := 4983230072969 + 3 ^ 40 * 1746837 * 2
def baseEnd_1746837 : Nat := 22147333482915733972937

theorem tailTrace_1746837 : CollatzResearch.WordTrace tailWord_1746837 prefixEnd_1746837 22147333482915733972937 := by
  unfold tailWord_1746837
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712379572515359852966765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42474919715010239901977843 63712379572515359852966765)
  ·
    refine ⟨23892142339693259944862537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63712379572515359852966765 23892142339693259944862537)
    ·
      refine ⟨17919106754769944958646903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23892142339693259944862537 17919106754769944958646903)
      ·
        refine ⟨26878660132154917437970355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17919106754769944958646903 26878660132154917437970355)
        ·
          refine ⟨40317990198232376156955533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26878660132154917437970355 40317990198232376156955533)
          ·
            refine ⟨15119246324337141058858325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40317990198232376156955533 15119246324337141058858325)
            ·
              refine ⟨22147333482915733972937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15119246324337141058858325 22147333482915733972937)
              ·
                rfl

theorem cell22_1746837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 11].length) (baseStart_1746837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746837 prefixEnd_1746837 := by exact prefixLift 1746837
  have htrace : WordTrace (prefixWord ++ tailWord_1746837) baseStart_1746837 baseEnd_1746837 := by
    simpa [prefixWord, tailWord_1746837, baseEnd_1746837] using wordTrace_append hprefix tailTrace_1746837
  have hstable : (prefixWord ++ tailWord_1746837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746837).length < 2 ^ (prefixWord ++ tailWord_1746837).sum := by decide
  have hdescent : baseEnd_1746837 < baseStart_1746837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746841 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_1746841 : Nat := 118140960795 + 1746841 * 2 ^ 59
def prefixEnd_1746841 : Nat := 4983230072969 + 3 ^ 40 * 1746841 * 2
def baseEnd_1746841 : Nat := 597979373320470140169287

theorem tailTrace_1746841 : CollatzResearch.WordTrace tailWord_1746841 prefixEnd_1746841 597979373320470140169287 := by
  unfold tailWord_1746841
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712525464500868536112377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42475016976333912357408251 63712525464500868536112377)
  ·
    refine ⟨47784394098375651402084283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63712525464500868536112377 47784394098375651402084283)
    ·
      refine ⟨71676591147563477103126425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47784394098375651402084283 71676591147563477103126425)
      ·
        refine ⟨53757443360672607827344819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71676591147563477103126425 53757443360672607827344819)
        ·
          refine ⟨80636165041008911741017229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53757443360672607827344819 80636165041008911741017229)
          ·
            refine ⟨30238561890378341902881461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80636165041008911741017229 30238561890378341902881461)
            ·
              refine ⟨2834865177222969553395137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30238561890378341902881461 2834865177222969553395137)
              ·
                refine ⟨2126148882917227165046353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834865177222969553395137 2126148882917227165046353)
                ·
                  refine ⟨1594611662187920373784765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126148882917227165046353 1594611662187920373784765)
                  ·
                    refine ⟨597979373320470140169287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594611662187920373784765 597979373320470140169287)
                    ·
                      rfl

theorem cell22_1746841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_1746841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746841 prefixEnd_1746841 := by exact prefixLift 1746841
  have htrace : WordTrace (prefixWord ++ tailWord_1746841) baseStart_1746841 baseEnd_1746841 := by
    simpa [prefixWord, tailWord_1746841, baseEnd_1746841] using wordTrace_append hprefix tailTrace_1746841
  have hstable : (prefixWord ++ tailWord_1746841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746841).length < 2 ^ (prefixWord ++ tailWord_1746841).sum := by decide
  have hdescent : baseEnd_1746841 < baseStart_1746841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746862 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1746862 : Nat := 118140960795 + 1746862 * 2 ^ 59
def prefixEnd_1746862 : Nat := 4983230072969 + 3 ^ 40 * 1746862 * 2
def baseEnd_1746862 : Nat := 597986562049633085394223

theorem tailTrace_1746862 : CollatzResearch.WordTrace tailWord_1746862 prefixEnd_1746862 597986562049633085394223 := by
  unfold tailWord_1746862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964161424678098640328355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42475527598283192748417893 7964161424678098640328355)
  ·
    refine ⟨11946242137017147960492533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7964161424678098640328355 11946242137017147960492533)
    ·
      refine ⟨1119960200345357621296175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11946242137017147960492533 1119960200345357621296175)
      ·
        refine ⟨1679940300518036431944263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119960200345357621296175 1679940300518036431944263)
        ·
          refine ⟨2519910450777054647916395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679940300518036431944263 2519910450777054647916395)
          ·
            refine ⟨3779865676165581971874593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519910450777054647916395 3779865676165581971874593)
            ·
              refine ⟨2834899257124186478905945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779865676165581971874593 2834899257124186478905945)
              ·
                refine ⟨2126174442843139859179459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834899257124186478905945 2126174442843139859179459)
                ·
                  refine ⟨3189261664264709788769189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126174442843139859179459 3189261664264709788769189)
                  ·
                    refine ⟨597986562049633085394223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189261664264709788769189 597986562049633085394223)
                    ·
                      rfl

theorem cell22_1746862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1746862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746862 prefixEnd_1746862 := by exact prefixLift 1746862
  have htrace : WordTrace (prefixWord ++ tailWord_1746862) baseStart_1746862 baseEnd_1746862 := by
    simpa [prefixWord, tailWord_1746862, baseEnd_1746862] using wordTrace_append hprefix tailTrace_1746862
  have hstable : (prefixWord ++ tailWord_1746862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746862).length < 2 ^ (prefixWord ++ tailWord_1746862).sum := by decide
  have hdescent : baseEnd_1746862 < baseStart_1746862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746954 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1746954 : Nat := 118140960795 + 1746954 * 2 ^ 59
def prefixEnd_1746954 : Nat := 4983230072969 + 3 ^ 40 * 1746954 * 2
def baseEnd_1746954 : Nat := 598018055529775512093941

theorem tailTrace_1746954 : CollatzResearch.WordTrace tailWord_1746954 prefixEnd_1746954 598018055529775512093941 := by
  unfold tailWord_1746954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929161728272872208743979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42477764608727659223317277 15929161728272872208743979)
  ·
    refine ⟨23893742592409308313115969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929161728272872208743979 23893742592409308313115969)
    ·
      refine ⟨17920306944306981234836977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23893742592409308313115969 17920306944306981234836977)
      ·
        refine ⟨13440230208230235926127733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17920306944306981234836977 13440230208230235926127733)
        ·
          refine ⟨1260021582021584618074475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13440230208230235926127733 1260021582021584618074475)
          ·
            refine ⟨1890032373032376927111713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260021582021584618074475 1890032373032376927111713)
            ·
              refine ⟨1417524279774282695333785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890032373032376927111713 1417524279774282695333785)
              ·
                refine ⟨1063143209830712021500339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417524279774282695333785 1063143209830712021500339)
                ·
                  refine ⟨1594714814746068032250509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063143209830712021500339 1594714814746068032250509)
                  ·
                    refine ⟨598018055529775512093941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594714814746068032250509 598018055529775512093941)
                    ·
                      rfl

theorem cell22_1746954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1746954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1746954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1746954 prefixEnd_1746954 := by exact prefixLift 1746954
  have htrace : WordTrace (prefixWord ++ tailWord_1746954) baseStart_1746954 baseEnd_1746954 := by
    simpa [prefixWord, tailWord_1746954, baseEnd_1746954] using wordTrace_append hprefix tailTrace_1746954
  have hstable : (prefixWord ++ tailWord_1746954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746954).length < 2 ^ (prefixWord ++ tailWord_1746954).sum := by decide
  have hdescent : baseEnd_1746954 < baseStart_1746954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747055 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 1, 3]
def baseStart_1747055 : Nat := 118140960795 + 1747055 * 2 ^ 59
def prefixEnd_1747055 : Nat := 4983230072969 + 3 ^ 40 * 1747055 * 2
def baseEnd_1747055 : Nat := 598052629893844915318631

theorem tailTrace_1747055 : CollatzResearch.WordTrace tailWord_1747055 prefixEnd_1747055 598052629893844915318631 := by
  unfold tailWord_1747055
  simp only [CollatzResearch.WordTrace]
  refine ⟨63720330685725583084402619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42480220457150388722935079 63720330685725583084402619)
  ·
    refine ⟨95580496028588374626603929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63720330685725583084402619 95580496028588374626603929)
    ·
      refine ⟨71685372021441280969952947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95580496028588374626603929 71685372021441280969952947)
      ·
        refine ⟨107528058032161921454929421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71685372021441280969952947 107528058032161921454929421)
        ·
          refine ⟨40323021762060720545598533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107528058032161921454929421 40323021762060720545598533)
          ·
            refine ⟨7560566580386385102299725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40323021762060720545598533 7560566580386385102299725)
            ·
              refine ⟨2835212467644894413362397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7560566580386385102299725 2835212467644894413362397)
              ·
                refine ⟨1063204675366835405010899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835212467644894413362397 1063204675366835405010899)
                ·
                  refine ⟨1594807013050253107516349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063204675366835405010899 1594807013050253107516349)
                  ·
                    refine ⟨598052629893844915318631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594807013050253107516349 598052629893844915318631)
                    ·
                      rfl

theorem cell22_1747055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_1747055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747055 prefixEnd_1747055 := by exact prefixLift 1747055
  have htrace : WordTrace (prefixWord ++ tailWord_1747055) baseStart_1747055 baseEnd_1747055 := by
    simpa [prefixWord, tailWord_1747055, baseEnd_1747055] using wordTrace_append hprefix tailTrace_1747055
  have hstable : (prefixWord ++ tailWord_1747055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747055).length < 2 ^ (prefixWord ++ tailWord_1747055).sum := by decide
  have hdescent : baseEnd_1747055 < baseStart_1747055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747081 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1747081 : Nat := 118140960795 + 1747081 * 2 ^ 59
def prefixEnd_1747081 : Nat := 4983230072969 + 3 ^ 40 * 1747081 * 2
def baseEnd_1747081 : Nat := 598061530225189514168551

theorem tailTrace_1747081 : CollatzResearch.WordTrace tailWord_1747081 prefixEnd_1747081 598061530225189514168551 := by
  unfold tailWord_1747081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721278983631389524849097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42480852655754259683232731 63721278983631389524849097)
  ·
    refine ⟨47790959237723542143636823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63721278983631389524849097 47790959237723542143636823)
    ·
      refine ⟨71686438856585313215455235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47790959237723542143636823 71686438856585313215455235)
      ·
        refine ⟨107529658284877969823182853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71686438856585313215455235 107529658284877969823182853)
        ·
          refine ⟨20161810928414619341846785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107529658284877969823182853 20161810928414619341846785)
          ·
            refine ⟨15121358196310964506385089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20161810928414619341846785 15121358196310964506385089)
            ·
              refine ⟨11341018647233223379788817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15121358196310964506385089 11341018647233223379788817)
              ·
                refine ⟨8505763985424917534841613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11341018647233223379788817 8505763985424917534841613)
                ·
                  refine ⟨3189661494534344075565605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8505763985424917534841613 3189661494534344075565605)
                  ·
                    refine ⟨598061530225189514168551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189661494534344075565605 598061530225189514168551)
                    ·
                      rfl

theorem cell22_1747081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1747081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747081 prefixEnd_1747081 := by exact prefixLift 1747081
  have htrace : WordTrace (prefixWord ++ tailWord_1747081) baseStart_1747081 baseEnd_1747081 := by
    simpa [prefixWord, tailWord_1747081, baseEnd_1747081] using wordTrace_append hprefix tailTrace_1747081
  have hstable : (prefixWord ++ tailWord_1747081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747081).length < 2 ^ (prefixWord ++ tailWord_1747081).sum := by decide
  have hdescent : baseEnd_1747081 < baseStart_1747081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747130 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_1747130 : Nat := 118140960795 + 1747130 * 2 ^ 59
def prefixEnd_1747130 : Nat := 4983230072969 + 3 ^ 40 * 1747130 * 2
def baseEnd_1747130 : Nat := 199359434642189906564467

theorem tailTrace_1747130 : CollatzResearch.WordTrace tailWord_1747130 prefixEnd_1747130 199359434642189906564467 := by
  unfold tailWord_1747130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930766540113467723345711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42482044106969247262255229 15930766540113467723345711)
  ·
    refine ⟨23896149810170201585018567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15930766540113467723345711 23896149810170201585018567)
    ·
      refine ⟨35844224715255302377527851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896149810170201585018567 35844224715255302377527851)
      ·
        refine ⟨53766337072882953566291777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35844224715255302377527851 53766337072882953566291777)
        ·
          refine ⟨40324752804662215174718833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53766337072882953566291777 40324752804662215174718833)
          ·
            refine ⟨30243564603496661381039125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40324752804662215174718833 30243564603496661381039125)
            ·
              refine ⟨1417667090788906002236209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30243564603496661381039125 1417667090788906002236209)
              ·
                refine ⟨1063250318091679501677157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417667090788906002236209 1063250318091679501677157)
                ·
                  refine ⟨199359434642189906564467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063250318091679501677157 199359434642189906564467)
                  ·
                    rfl

theorem cell22_1747130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_1747130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747130 prefixEnd_1747130 := by exact prefixLift 1747130
  have htrace : WordTrace (prefixWord ++ tailWord_1747130) baseStart_1747130 baseEnd_1747130 := by
    simpa [prefixWord, tailWord_1747130, baseEnd_1747130] using wordTrace_append hprefix tailTrace_1747130
  have hstable : (prefixWord ++ tailWord_1747130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747130).length < 2 ^ (prefixWord ++ tailWord_1747130).sum := by decide
  have hdescent : baseEnd_1747130 < baseStart_1747130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747141 : List Nat := [1, 3, 1, 1, 1, 1, 7, 7]
def baseStart_1747141 : Nat := 118140960795 + 1747141 * 2 ^ 59
def prefixEnd_1747141 : Nat := 4983230072969 + 3 ^ 40 * 1747141 * 2
def baseEnd_1747141 : Nat := 66453563272374373074263

theorem tailTrace_1747141 : CollatzResearch.WordTrace tailWord_1747141 prefixEnd_1747141 66453563272374373074263 := by
  unfold tailWord_1747141
  simp only [CollatzResearch.WordTrace]
  refine ⟨63723467363414019772033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42482311575609346514688851 63723467363414019772033277)
  ·
    refine ⟨23896300261280257414512479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63723467363414019772033277 23896300261280257414512479)
    ·
      refine ⟨35844450391920386121768719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896300261280257414512479 35844450391920386121768719)
      ·
        refine ⟨53766675587880579182653079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35844450391920386121768719 53766675587880579182653079)
        ·
          refine ⟨80650013381820868773979619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53766675587880579182653079 80650013381820868773979619)
          ·
            refine ⟨120975020072731303160969429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80650013381820868773979619 120975020072731303160969429)
            ·
              refine ⟨2835352032954639917835221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120975020072731303160969429 2835352032954639917835221)
              ·
                refine ⟨66453563272374373074263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2835352032954639917835221 66453563272374373074263)
                ·
                  rfl

theorem cell22_1747141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 7].length) (baseStart_1747141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747141 prefixEnd_1747141 := by exact prefixLift 1747141
  have htrace : WordTrace (prefixWord ++ tailWord_1747141) baseStart_1747141 baseEnd_1747141 := by
    simpa [prefixWord, tailWord_1747141, baseEnd_1747141] using wordTrace_append hprefix tailTrace_1747141
  have hstable : (prefixWord ++ tailWord_1747141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747141).length < 2 ^ (prefixWord ++ tailWord_1747141).sum := by decide
  have hdescent : baseEnd_1747141 < baseStart_1747141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
