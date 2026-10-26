import V185TrunkScan22Chunk188

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1686305 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 4]
def baseStart_1686305 : Nat := 118140960795 + 1686305 * 2 ^ 59
def prefixEnd_1686305 : Nat := 4983230072969 + 3 ^ 40 * 1686305 * 2
def baseEnd_1686305 : Nat := 192418887795584457251629

theorem tailTrace_1686305 : CollatzResearch.WordTrace tailWord_1686305 prefixEnd_1686305 192418887795584457251629 := by
  unfold tailWord_1686305
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504596155812457810420369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41003064103874971873613579 61504596155812457810420369)
  ·
    refine ⟨46128447116859343357815277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61504596155812457810420369 46128447116859343357815277)
    ·
      refine ⟨17298167668822253759180729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46128447116859343357815277 17298167668822253759180729)
      ·
        refine ⟨12973625751616690319385547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17298167668822253759180729 12973625751616690319385547)
        ·
          refine ⟨19460438627425035479078321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973625751616690319385547 19460438627425035479078321)
          ·
            refine ⟨14595328970568776609308741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19460438627425035479078321 14595328970568776609308741)
            ·
              refine ⟨2736624181981645614245389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14595328970568776609308741 2736624181981645614245389)
              ·
                refine ⟨1026234068243117105342021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2736624181981645614245389 1026234068243117105342021)
                ·
                  refine ⟨192418887795584457251629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026234068243117105342021 192418887795584457251629)
                  ·
                    rfl

theorem cell22_1686305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_1686305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686305 prefixEnd_1686305 := by exact prefixLift 1686305
  have htrace : WordTrace (prefixWord ++ tailWord_1686305) baseStart_1686305 baseEnd_1686305 := by
    simpa [prefixWord, tailWord_1686305, baseEnd_1686305] using wordTrace_append hprefix tailTrace_1686305
  have hstable : (prefixWord ++ tailWord_1686305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686305).length < 2 ^ (prefixWord ++ tailWord_1686305).sum := by decide
  have hdescent : baseEnd_1686305 < baseStart_1686305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686316 : List Nat := [2, 2, 1, 1, 1, 4, 11]
def baseStart_1686316 : Nat := 118140960795 + 1686316 * 2 ^ 59
def prefixEnd_1686316 : Nat := 4983230072969 + 3 ^ 40 * 1686316 * 2
def baseEnd_1686316 : Nat := 21380015885613074434439

theorem tailTrace_1686316 : CollatzResearch.WordTrace tailWord_1686316 prefixEnd_1686316 21380015885613074434439 := by
  unfold tailWord_1686316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30752498679386303344535401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41003331572515071126047201 30752498679386303344535401)
  ·
    refine ⟨23064374009539727508401551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30752498679386303344535401 23064374009539727508401551)
    ·
      refine ⟨34596561014309591262602327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23064374009539727508401551 34596561014309591262602327)
      ·
        refine ⟨51894841521464386893903491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34596561014309591262602327 51894841521464386893903491)
        ·
          refine ⟨77842262282196580340855237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51894841521464386893903491 77842262282196580340855237)
          ·
            refine ⟨14595424177911858813910357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77842262282196580340855237 14595424177911858813910357)
            ·
              refine ⟨21380015885613074434439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14595424177911858813910357 21380015885613074434439)
              ·
                rfl

theorem cell22_1686316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 11].length) (baseStart_1686316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686316 prefixEnd_1686316 := by exact prefixLift 1686316
  have htrace : WordTrace (prefixWord ++ tailWord_1686316) baseStart_1686316 baseEnd_1686316 := by
    simpa [prefixWord, tailWord_1686316, baseEnd_1686316] using wordTrace_append hprefix tailTrace_1686316
  have hstable : (prefixWord ++ tailWord_1686316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686316).length < 2 ^ (prefixWord ++ tailWord_1686316).sum := by decide
  have hdescent : baseEnd_1686316 < baseStart_1686316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686395 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 5]
def baseStart_1686395 : Nat := 118140960795 + 1686395 * 2 ^ 59
def prefixEnd_1686395 : Nat := 4983230072969 + 3 ^ 40 * 1686395 * 2
def baseEnd_1686395 : Nat := 192429157408674379001537

theorem tailTrace_1686395 : CollatzResearch.WordTrace tailWord_1686395 prefixEnd_1686395 192429157408674379001537 := by
  unfold tailWord_1686395
  simp only [CollatzResearch.WordTrace]
  refine ⟨61507878725486403181196639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41005252483657602120797759 61507878725486403181196639)
  ·
    refine ⟨92261818088229604771794959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61507878725486403181196639 92261818088229604771794959)
    ·
      refine ⟨138392727132344407157692439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92261818088229604771794959 138392727132344407157692439)
      ·
        refine ⟨207589090698516610736538659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138392727132344407157692439 207589090698516610736538659)
        ·
          refine ⟨311383636047774916104807989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207589090698516610736538659 311383636047774916104807989)
          ·
            refine ⟨29192215879478898384825749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311383636047774916104807989 29192215879478898384825749)
            ·
              refine ⟨1368385119350573361788707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29192215879478898384825749 1368385119350573361788707)
              ·
                refine ⟨2052577679025860042683061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368385119350573361788707 2052577679025860042683061)
                ·
                  refine ⟨192429157408674379001537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052577679025860042683061 192429157408674379001537)
                  ·
                    rfl

theorem cell22_1686395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 5].length) (baseStart_1686395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686395 prefixEnd_1686395 := by exact prefixLift 1686395
  have htrace : WordTrace (prefixWord ++ tailWord_1686395) baseStart_1686395 baseEnd_1686395 := by
    simpa [prefixWord, tailWord_1686395, baseEnd_1686395] using wordTrace_append hprefix tailTrace_1686395
  have hstable : (prefixWord ++ tailWord_1686395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686395).length < 2 ^ (prefixWord ++ tailWord_1686395).sum := by decide
  have hdescent : baseEnd_1686395 < baseStart_1686395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686485 : List Nat := [1, 3, 2, 3, 3, 1, 9]
def baseStart_1686485 : Nat := 118140960795 + 1686485 * 2 ^ 59
def prefixEnd_1686485 : Nat := 4983230072969 + 3 ^ 40 * 1686485 * 2
def baseEnd_1686485 : Nat := 21382158557973811194605

theorem tailTrace_1686485 : CollatzResearch.WordTrace tailWord_1686485 prefixEnd_1686485 21382158557973811194605 := by
  unfold tailWord_1686485
  simp only [CollatzResearch.WordTrace]
  refine ⟨61511161295160348551972909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41007440863440232367981939 61511161295160348551972909)
  ·
    refine ⟨23066685485685130706989841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61511161295160348551972909 23066685485685130706989841)
    ·
      refine ⟨17300014114263848030242381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23066685485685130706989841 17300014114263848030242381)
      ·
        refine ⟨6487505292848943011340893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17300014114263848030242381 6487505292848943011340893)
        ·
          refine ⟨2432814484818353629252835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6487505292848943011340893 2432814484818353629252835)
          ·
            refine ⟨3649221727227530443879253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432814484818353629252835 3649221727227530443879253)
            ·
              refine ⟨21382158557973811194605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3649221727227530443879253 21382158557973811194605)
              ·
                rfl

theorem cell22_1686485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 9].length) (baseStart_1686485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686485 prefixEnd_1686485 := by exact prefixLift 1686485
  have htrace : WordTrace (prefixWord ++ tailWord_1686485) baseStart_1686485 baseEnd_1686485 := by
    simpa [prefixWord, tailWord_1686485, baseEnd_1686485] using wordTrace_append hprefix tailTrace_1686485
  have hstable : (prefixWord ++ tailWord_1686485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686485).length < 2 ^ (prefixWord ++ tailWord_1686485).sum := by decide
  have hdescent : baseEnd_1686485 < baseStart_1686485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686489 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_1686489 : Nat := 118140960795 + 1686489 * 2 ^ 59
def prefixEnd_1686489 : Nat := 4983230072969 + 3 ^ 40 * 1686489 * 2
def baseEnd_1686489 : Nat := 577319650347038225154323

theorem tailTrace_1686489 : CollatzResearch.WordTrace tailWord_1686489 prefixEnd_1686489 577319650347038225154323 := by
  unfold tailWord_1686489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61511307187145857235118521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41007538124763904823412347 61511307187145857235118521)
  ·
    refine ⟨46133480390359392926338891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61511307187145857235118521 46133480390359392926338891)
    ·
      refine ⟨69200220585539089389508337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46133480390359392926338891 69200220585539089389508337)
      ·
        refine ⟨51900165439154317042131253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69200220585539089389508337 51900165439154317042131253)
        ·
          refine ⟨4865640509920717222699805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51900165439154317042131253 4865640509920717222699805)
          ·
            refine ⟨1824615191220268958512427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865640509920717222699805 1824615191220268958512427)
            ·
              refine ⟨2736922786830403437768641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824615191220268958512427 2736922786830403437768641)
              ·
                refine ⟨2052692090122802578326481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736922786830403437768641 2052692090122802578326481)
                ·
                  refine ⟨1539519067592101933744861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052692090122802578326481 1539519067592101933744861)
                  ·
                    refine ⟨577319650347038225154323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539519067592101933744861 577319650347038225154323)
                    ·
                      rfl

theorem cell22_1686489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_1686489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686489 prefixEnd_1686489 := by exact prefixLift 1686489
  have htrace : WordTrace (prefixWord ++ tailWord_1686489) baseStart_1686489 baseEnd_1686489 := by
    simpa [prefixWord, tailWord_1686489, baseEnd_1686489] using wordTrace_append hprefix tailTrace_1686489
  have hstable : (prefixWord ++ tailWord_1686489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686489).length < 2 ^ (prefixWord ++ tailWord_1686489).sum := by decide
  have hdescent : baseEnd_1686489 < baseStart_1686489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686564 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1686564 : Nat := 118140960795 + 1686564 * 2 ^ 59
def prefixEnd_1686564 : Nat := 4983230072969 + 3 ^ 40 * 1686564 * 2
def baseEnd_1686564 : Nat := 192448441459921009843031

theorem tailTrace_1686564 : CollatzResearch.WordTrace tailWord_1686564 prefixEnd_1686564 192448441459921009843031 := by
  unfold tailWord_1686564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757021330937072522049373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41009361774582763362732497 30757021330937072522049373)
  ·
    refine ⟨11533882999101402195768515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30757021330937072522049373 11533882999101402195768515)
    ·
      refine ⟨17300824498652103293652773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11533882999101402195768515 17300824498652103293652773)
      ·
        refine ⟨3243904593497269367559895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17300824498652103293652773 3243904593497269367559895)
        ·
          refine ⟨4865856890245904051339843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243904593497269367559895 4865856890245904051339843)
          ·
            refine ⟨7298785335368856077009765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865856890245904051339843 7298785335368856077009765)
            ·
              refine ⟨1368522250381660514439331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7298785335368856077009765 1368522250381660514439331)
              ·
                refine ⟨2052783375572490771658997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368522250381660514439331 2052783375572490771658997)
                ·
                  refine ⟨192448441459921009843031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052783375572490771658997 192448441459921009843031)
                  ·
                    rfl

theorem cell22_1686564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1686564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686564 prefixEnd_1686564 := by exact prefixLift 1686564
  have htrace : WordTrace (prefixWord ++ tailWord_1686564) baseStart_1686564 baseEnd_1686564 := by
    simpa [prefixWord, tailWord_1686564, baseEnd_1686564] using wordTrace_append hprefix tailTrace_1686564
  have hstable : (prefixWord ++ tailWord_1686564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686564).length < 2 ^ (prefixWord ++ tailWord_1686564).sum := by decide
  have hdescent : baseEnd_1686564 < baseStart_1686564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686592 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_1686592 : Nat := 118140960795 + 1686592 * 2 ^ 59
def prefixEnd_1686592 : Nat := 4983230072969 + 3 ^ 40 * 1686592 * 2
def baseEnd_1686592 : Nat := 192451636450660096609669

theorem tailTrace_1686592 : CollatzResearch.WordTrace tailWord_1686592 prefixEnd_1686592 192451636450660096609669 := by
  unfold tailWord_1686592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757531952886352913059015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41010042603848470550745353 30757531952886352913059015)
  ·
    refine ⟨46136297929329529369588523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30757531952886352913059015 46136297929329529369588523)
    ·
      refine ⟨69204446893994294054382785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46136297929329529369588523 69204446893994294054382785)
      ·
        refine ⟨51903335170495720540787089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69204446893994294054382785 51903335170495720540787089)
        ·
          refine ⟨38927501377871790405590317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51903335170495720540787089 38927501377871790405590317)
          ·
            refine ⟨14597813016701921402096369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38927501377871790405590317 14597813016701921402096369)
            ·
              refine ⟨10948359762526441051572277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14597813016701921402096369 10948359762526441051572277)
              ·
                refine ⟨1026408727736853848584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10948359762526441051572277 1026408727736853848584901)
                ·
                  refine ⟨192451636450660096609669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026408727736853848584901 192451636450660096609669)
                  ·
                    rfl

theorem cell22_1686592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_1686592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686592 prefixEnd_1686592 := by exact prefixLift 1686592
  have htrace : WordTrace (prefixWord ++ tailWord_1686592) baseStart_1686592 baseEnd_1686592 := by
    simpa [prefixWord, tailWord_1686592, baseEnd_1686592] using wordTrace_append hprefix tailTrace_1686592
  have hstable : (prefixWord ++ tailWord_1686592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686592).length < 2 ^ (prefixWord ++ tailWord_1686592).sum := by decide
  have hdescent : baseEnd_1686592 < baseStart_1686592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686609 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 4]
def baseStart_1686609 : Nat := 118140960795 + 1686609 * 2 ^ 59
def prefixEnd_1686609 : Nat := 4983230072969 + 3 ^ 40 * 1686609 * 2
def baseEnd_1686609 : Nat := 192453576266465970717985

theorem tailTrace_1686609 : CollatzResearch.WordTrace tailWord_1686609 prefixEnd_1686609 192453576266465970717985 := by
  unfold tailWord_1686609
  simp only [CollatzResearch.WordTrace]
  refine ⟨61515683946711117729486881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41010455964474078486324587 61515683946711117729486881)
  ·
    refine ⟨46136762960033338297115161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61515683946711117729486881 46136762960033338297115161)
    ·
      refine ⟨34602572220025003722836371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46136762960033338297115161 34602572220025003722836371)
      ·
        refine ⟨51903858330037505584254557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34602572220025003722836371 51903858330037505584254557)
        ·
          refine ⟨19463946873764064594095459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51903858330037505584254557 19463946873764064594095459)
          ·
            refine ⟨29195920310646096891143189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463946873764064594095459 29195920310646096891143189)
            ·
              refine ⟨1368558764561535791772337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29195920310646096891143189 1368558764561535791772337)
              ·
                refine ⟨1026419073421151843829253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368558764561535791772337 1026419073421151843829253)
                ·
                  refine ⟨192453576266465970717985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026419073421151843829253 192453576266465970717985)
                  ·
                    rfl

theorem cell22_1686609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_1686609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686609 prefixEnd_1686609 := by exact prefixLift 1686609
  have htrace : WordTrace (prefixWord ++ tailWord_1686609) baseStart_1686609 baseEnd_1686609 := by
    simpa [prefixWord, tailWord_1686609, baseEnd_1686609] using wordTrace_append hprefix tailTrace_1686609
  have hstable : (prefixWord ++ tailWord_1686609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686609).length < 2 ^ (prefixWord ++ tailWord_1686609).sum := by decide
  have hdescent : baseEnd_1686609 < baseStart_1686609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686645 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1686645 : Nat := 118140960795 + 1686645 * 2 ^ 59
def prefixEnd_1686645 : Nat := 4983230072969 + 3 ^ 40 * 1686645 * 2
def baseEnd_1686645 : Nat := 577373052335105818253845

theorem tailTrace_1686645 : CollatzResearch.WordTrace tailWord_1686645 prefixEnd_1686645 577373052335105818253845 := by
  unfold tailWord_1686645
  simp only [CollatzResearch.WordTrace]
  refine ⟨61516996974580695877797389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41011331316387130585198259 61516996974580695877797389)
  ·
    refine ⟨23068873865467760954174021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61516996974580695877797389 23068873865467760954174021)
    ·
      refine ⟨4325413849775205178907629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23068873865467760954174021 4325413849775205178907629)
      ·
        refine ⟨1622030193665701942090361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4325413849775205178907629 1622030193665701942090361)
        ·
          refine ⟨1216522645249276456567771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622030193665701942090361 1216522645249276456567771)
          ·
            refine ⟨1824783967873914684851657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216522645249276456567771 1824783967873914684851657)
            ·
              refine ⟨1368587975905436013638743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824783967873914684851657 1368587975905436013638743)
              ·
                refine ⟨2052881963858154020458115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368587975905436013638743 2052881963858154020458115)
                ·
                  refine ⟨3079322945787231030687173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052881963858154020458115 3079322945787231030687173)
                  ·
                    refine ⟨577373052335105818253845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079322945787231030687173 577373052335105818253845)
                    ·
                      rfl

theorem cell22_1686645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1686645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686645 prefixEnd_1686645 := by exact prefixLift 1686645
  have htrace : WordTrace (prefixWord ++ tailWord_1686645) baseStart_1686645 baseEnd_1686645 := by
    simpa [prefixWord, tailWord_1686645, baseEnd_1686645] using wordTrace_append hprefix tailTrace_1686645
  have hstable : (prefixWord ++ tailWord_1686645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686645).length < 2 ^ (prefixWord ++ tailWord_1686645).sum := by decide
  have hdescent : baseEnd_1686645 < baseStart_1686645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686652 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1686652 : Nat := 118140960795 + 1686652 * 2 ^ 59
def prefixEnd_1686652 : Nat := 4983230072969 + 3 ^ 40 * 1686652 * 2
def baseEnd_1686652 : Nat := 577375448578160133328823

theorem tailTrace_1686652 : CollatzResearch.WordTrace tailWord_1686652 prefixEnd_1686652 577375448578160133328823 := by
  unfold tailWord_1686652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758626142777668036651105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41011501523703557382201473 30758626142777668036651105)
  ·
    refine ⟨23068969607083251027488329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30758626142777668036651105 23068969607083251027488329)
    ·
      refine ⟨17301727205312438270616247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23068969607083251027488329 17301727205312438270616247)
      ·
        refine ⟨25952590807968657405924371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17301727205312438270616247 25952590807968657405924371)
        ·
          refine ⟨38928886211952986108886557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25952590807968657405924371 38928886211952986108886557)
          ·
            refine ⟨14598332329482369790832459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38928886211952986108886557 14598332329482369790832459)
            ·
              refine ⟨21897498494223554686248689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14598332329482369790832459 21897498494223554686248689)
              ·
                refine ⟨16423123870667666014686517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21897498494223554686248689 16423123870667666014686517)
                ·
                  refine ⟨1539667862875093688876861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16423123870667666014686517 1539667862875093688876861)
                  ·
                    refine ⟨577375448578160133328823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539667862875093688876861 577375448578160133328823)
                    ·
                      rfl

theorem cell22_1686652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1686652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686652 prefixEnd_1686652 := by exact prefixLift 1686652
  have htrace : WordTrace (prefixWord ++ tailWord_1686652) baseStart_1686652 baseEnd_1686652 := by
    simpa [prefixWord, tailWord_1686652, baseEnd_1686652] using wordTrace_append hprefix tailTrace_1686652
  have hstable : (prefixWord ++ tailWord_1686652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686652).length < 2 ^ (prefixWord ++ tailWord_1686652).sum := by decide
  have hdescent : baseEnd_1686652 < baseStart_1686652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686686 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1686686 : Nat := 118140960795 + 1686686 * 2 ^ 59
def prefixEnd_1686686 : Nat := 4983230072969 + 3 ^ 40 * 1686686 * 2
def baseEnd_1686686 : Nat := 577387087472995377978719

theorem tailTrace_1686686 : CollatzResearch.WordTrace tailWord_1686686 prefixEnd_1686686 577387087472995377978719 := by
  unfold tailWord_1686686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689811545929019985004989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41012328244954773253359941 7689811545929019985004989)
  ·
    refine ⟨2883679329723382494376871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7689811545929019985004989 2883679329723382494376871)
    ·
      refine ⟨4325518994585073741565307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883679329723382494376871 4325518994585073741565307)
      ·
        refine ⟨6488278491877610612347961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325518994585073741565307 6488278491877610612347961)
        ·
          refine ⟨4866208868908207959260971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6488278491877610612347961 4866208868908207959260971)
          ·
            refine ⟨7299313303362311938891457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866208868908207959260971 7299313303362311938891457)
            ·
              refine ⟨5474484977521733954168593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299313303362311938891457 5474484977521733954168593)
              ·
                refine ⟨4105863733141300465626445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5474484977521733954168593 4105863733141300465626445)
                ·
                  refine ⟨1539698899927987674609917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4105863733141300465626445 1539698899927987674609917)
                  ·
                    refine ⟨577387087472995377978719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539698899927987674609917 577387087472995377978719)
                    ·
                      rfl

theorem cell22_1686686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1686686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686686 prefixEnd_1686686 := by exact prefixLift 1686686
  have htrace : WordTrace (prefixWord ++ tailWord_1686686) baseStart_1686686 baseEnd_1686686 := by
    simpa [prefixWord, tailWord_1686686, baseEnd_1686686] using wordTrace_append hprefix tailTrace_1686686
  have hstable : (prefixWord ++ tailWord_1686686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686686).length < 2 ^ (prefixWord ++ tailWord_1686686).sum := by decide
  have hdescent : baseEnd_1686686 < baseStart_1686686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686733 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1686733 : Nat := 118140960795 + 1686733 * 2 ^ 59
def prefixEnd_1686733 : Nat := 4983230072969 + 3 ^ 40 * 1686733 * 2
def baseEnd_1686733 : Nat := 192467725511167640684525

theorem tailTrace_1686733 : CollatzResearch.WordTrace tailWord_1686733 prefixEnd_1686733 192467725511167640684525 := by
  unfold tailWord_1686733
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520206598261886907000853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41013471065507924604667235 61520206598261886907000853)
  ·
    refine ⟨2883759684293525948765665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61520206598261886907000853 2883759684293525948765665)
    ·
      refine ⟨2162819763220144461574249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2883759684293525948765665 2162819763220144461574249)
      ·
        refine ⟨1622114822415108346180687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2162819763220144461574249 1622114822415108346180687)
        ·
          refine ⟨2433172233622662519271031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622114822415108346180687 2433172233622662519271031)
          ·
            refine ⟨3649758350433993778906547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433172233622662519271031 3649758350433993778906547)
            ·
              refine ⟨5474637525650990668359821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649758350433993778906547 5474637525650990668359821)
              ·
                refine ⟨2052989072119121500634933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474637525650990668359821 2052989072119121500634933)
                ·
                  refine ⟨192467725511167640684525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2052989072119121500634933 192467725511167640684525)
                  ·
                    rfl

theorem cell22_1686733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1686733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686733 prefixEnd_1686733 := by exact prefixLift 1686733
  have htrace : WordTrace (prefixWord ++ tailWord_1686733) baseStart_1686733 baseEnd_1686733 := by
    simpa [prefixWord, tailWord_1686733, baseEnd_1686733] using wordTrace_append hprefix tailTrace_1686733
  have hstable : (prefixWord ++ tailWord_1686733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686733).length < 2 ^ (prefixWord ++ tailWord_1686733).sum := by decide
  have hdescent : baseEnd_1686733 < baseStart_1686733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686817 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 7]
def baseStart_1686817 : Nat := 118140960795 + 1686817 * 2 ^ 59
def prefixEnd_1686817 : Nat := 4983230072969 + 3 ^ 40 * 1686817 * 2
def baseEnd_1686817 : Nat := 192477310483384900984439

theorem tailTrace_1686817 : CollatzResearch.WordTrace tailWord_1686817 prefixEnd_1686817 192477310483384900984439 := by
  unfold tailWord_1686817
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523270329957569253058705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41015513553305046168705803 61523270329957569253058705)
  ·
    refine ⟨46142452747468176939794029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61523270329957569253058705 46142452747468176939794029)
    ·
      refine ⟨17303419780300566352422761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46142452747468176939794029 17303419780300566352422761)
      ·
        refine ⟨12977564835225424764317071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17303419780300566352422761 12977564835225424764317071)
        ·
          refine ⟨19466347252838137146475607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977564835225424764317071 19466347252838137146475607)
          ·
            refine ⟨29199520879257205719713411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19466347252838137146475607 29199520879257205719713411)
            ·
              refine ⟨43799281318885808579570117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29199520879257205719713411 43799281318885808579570117)
              ·
                refine ⟨8212365247291089108669397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43799281318885808579570117 8212365247291089108669397)
                ·
                  refine ⟨192477310483384900984439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8212365247291089108669397 192477310483384900984439)
                  ·
                    rfl

theorem cell22_1686817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_1686817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686817 prefixEnd_1686817 := by exact prefixLift 1686817
  have htrace : WordTrace (prefixWord ++ tailWord_1686817) baseStart_1686817 baseEnd_1686817 := by
    simpa [prefixWord, tailWord_1686817, baseEnd_1686817] using wordTrace_append hprefix tailTrace_1686817
  have hstable : (prefixWord ++ tailWord_1686817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686817).length < 2 ^ (prefixWord ++ tailWord_1686817).sum := by decide
  have hdescent : baseEnd_1686817 < baseStart_1686817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686832 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_1686832 : Nat := 118140960795 + 1686832 * 2 ^ 59
def prefixEnd_1686832 : Nat := 4983230072969 + 3 ^ 40 * 1686832 * 2
def baseEnd_1686832 : Nat := 577437066256699663828271

theorem tailTrace_1686832 : CollatzResearch.WordTrace tailWord_1686832 prefixEnd_1686832 577437066256699663828271 := by
  unfold tailWord_1686832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761908712451613407427375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41015878283268817876569833 30761908712451613407427375)
  ·
    refine ⟨46142863068677420111141063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30761908712451613407427375 46142863068677420111141063)
    ·
      refine ⟨69214294603016130166711595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46142863068677420111141063 69214294603016130166711595)
      ·
        refine ⟨103821441904524195250067393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69214294603016130166711595 103821441904524195250067393)
        ·
          refine ⟨77866081428393146437550545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103821441904524195250067393 77866081428393146437550545)
          ·
            refine ⟨58399561071294859828162909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77866081428393146437550545 58399561071294859828162909)
            ·
              refine ⟨21899835401735572435561091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58399561071294859828162909 21899835401735572435561091)
              ·
                refine ⟨32849753102603358653341637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21899835401735572435561091 32849753102603358653341637)
                ·
                  refine ⟨6159328706738129747501557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32849753102603358653341637 6159328706738129747501557)
                  ·
                    refine ⟨577437066256699663828271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6159328706738129747501557 577437066256699663828271)
                    ·
                      rfl

theorem cell22_1686832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_1686832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686832 prefixEnd_1686832 := by exact prefixLift 1686832
  have htrace : WordTrace (prefixWord ++ tailWord_1686832) baseStart_1686832 baseEnd_1686832 := by
    simpa [prefixWord, tailWord_1686832, baseEnd_1686832] using wordTrace_append hprefix tailTrace_1686832
  have hstable : (prefixWord ++ tailWord_1686832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686832).length < 2 ^ (prefixWord ++ tailWord_1686832).sum := by decide
  have hdescent : baseEnd_1686832 < baseStart_1686832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686834 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1686834 : Nat := 118140960795 + 1686834 * 2 ^ 59
def prefixEnd_1686834 : Nat := 4983230072969 + 3 ^ 40 * 1686834 * 2
def baseEnd_1686834 : Nat := 192479250299190775092755

theorem tailTrace_1686834 : CollatzResearch.WordTrace tailWord_1686834 prefixEnd_1686834 192479250299190775092755 := by
  unfold tailWord_1686834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15380972592723995289106889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41015926913930654104285037 15380972592723995289106889)
  ·
    refine ⟨11535729444542996466830167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15380972592723995289106889 11535729444542996466830167)
    ·
      refine ⟨17303594166814494700245251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11535729444542996466830167 17303594166814494700245251)
      ·
        refine ⟨25955391250221742050367877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17303594166814494700245251 25955391250221742050367877)
        ·
          refine ⟨4866635859416576634443977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25955391250221742050367877 4866635859416576634443977)
          ·
            refine ⟨3649976894562432475832983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4866635859416576634443977 3649976894562432475832983)
            ·
              refine ⟨5474965341843648713749475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649976894562432475832983 5474965341843648713749475)
              ·
                refine ⟨8212448012765473070624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474965341843648713749475 8212448012765473070624213)
                ·
                  refine ⟨192479250299190775092755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8212448012765473070624213 192479250299190775092755)
                  ·
                    rfl

theorem cell22_1686834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1686834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686834 prefixEnd_1686834 := by exact prefixLift 1686834
  have htrace : WordTrace (prefixWord ++ tailWord_1686834) baseStart_1686834 baseEnd_1686834 := by
    simpa [prefixWord, tailWord_1686834, baseEnd_1686834] using wordTrace_append hprefix tailTrace_1686834
  have hstable : (prefixWord ++ tailWord_1686834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686834).length < 2 ^ (prefixWord ++ tailWord_1686834).sum := by decide
  have hdescent : baseEnd_1686834 < baseStart_1686834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686909 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1686909 : Nat := 118140960795 + 1686909 * 2 ^ 59
def prefixEnd_1686909 : Nat := 4983230072969 + 3 ^ 40 * 1686909 * 2
def baseEnd_1686909 : Nat := 577463424930297129653035

theorem tailTrace_1686909 : CollatzResearch.WordTrace tailWord_1686909 prefixEnd_1686909 577463424930297129653035 := by
  unfold tailWord_1686909
  simp only [CollatzResearch.WordTrace]
  refine ⟨61526625845624268965407781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41017750563749512643605187 61526625845624268965407781)
  ·
    refine ⟨11536242346054550431013959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61526625845624268965407781 11536242346054550431013959)
    ·
      refine ⟨17304363519081825646520939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536242346054550431013959 17304363519081825646520939)
      ·
        refine ⟨25956545278622738469781409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304363519081825646520939 25956545278622738469781409)
        ·
          refine ⟨19467408958967053852336057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25956545278622738469781409 19467408958967053852336057)
          ·
            refine ⟨14600556719225290389252043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19467408958967053852336057 14600556719225290389252043)
            ·
              refine ⟨21900835078837935583878065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600556719225290389252043 21900835078837935583878065)
              ·
                refine ⟨16425626309128451687908549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21900835078837935583878065 16425626309128451687908549)
                ·
                  refine ⟨3079804932961584691482853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16425626309128451687908549 3079804932961584691482853)
                  ·
                    refine ⟨577463424930297129653035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079804932961584691482853 577463424930297129653035)
                    ·
                      rfl

theorem cell22_1686909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1686909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686909 prefixEnd_1686909 := by exact prefixLift 1686909
  have htrace : WordTrace (prefixWord ++ tailWord_1686909) baseStart_1686909 baseEnd_1686909 := by
    simpa [prefixWord, tailWord_1686909, baseEnd_1686909] using wordTrace_append hprefix tailTrace_1686909
  have hstable : (prefixWord ++ tailWord_1686909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686909).length < 2 ^ (prefixWord ++ tailWord_1686909).sum := by decide
  have hdescent : baseEnd_1686909 < baseStart_1686909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686984 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1686984 : Nat := 118140960795 + 1686984 * 2 ^ 59
def prefixEnd_1686984 : Nat := 4983230072969 + 3 ^ 40 * 1686984 * 2
def baseEnd_1686984 : Nat := 577489098963021934027805

theorem tailTrace_1686984 : CollatzResearch.WordTrace tailWord_1686984 prefixEnd_1686984 577489098963021934027805 := by
  unfold tailWord_1686984
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764680660176278387194003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41019574213568371182925337 30764680660176278387194003)
  ·
    refine ⟨46147020990264417580791005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30764680660176278387194003 46147020990264417580791005)
    ·
      refine ⟨17305132871349156592796627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46147020990264417580791005 17305132871349156592796627)
      ·
        refine ⟨25957699307023734889194941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17305132871349156592796627 25957699307023734889194941)
        ·
          refine ⟨9734137240133900583448103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25957699307023734889194941 9734137240133900583448103)
          ·
            refine ⟨14601205860200850875172155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734137240133900583448103 14601205860200850875172155)
            ·
              refine ⟨21901808790301276312758233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14601205860200850875172155 21901808790301276312758233)
              ·
                refine ⟨16426356592725957234568675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21901808790301276312758233 16426356592725957234568675)
                ·
                  refine ⟨24639534889088935851853013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16426356592725957234568675 24639534889088935851853013)
                  ·
                    refine ⟨577489098963021934027805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24639534889088935851853013 577489098963021934027805)
                    ·
                      rfl

theorem cell22_1686984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1686984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686984 prefixEnd_1686984 := by exact prefixLift 1686984
  have htrace : WordTrace (prefixWord ++ tailWord_1686984) baseStart_1686984 baseEnd_1686984 := by
    simpa [prefixWord, tailWord_1686984, baseEnd_1686984] using wordTrace_append hprefix tailTrace_1686984
  have hstable : (prefixWord ++ tailWord_1686984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686984).length < 2 ^ (prefixWord ++ tailWord_1686984).sum := by decide
  have hdescent : baseEnd_1686984 < baseStart_1686984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687048 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_1687048 : Nat := 118140960795 + 1687048 * 2 ^ 59
def prefixEnd_1687048 : Nat := 4983230072969 + 3 ^ 40 * 1687048 * 2
def baseEnd_1687048 : Nat := 192503669156982366809203

theorem tailTrace_1687048 : CollatzResearch.WordTrace tailWord_1687048 prefixEnd_1687048 192503669156982366809203 := by
  unfold tailWord_1687048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765847796060347852358899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41021130394747130469811865 30765847796060347852358899)
  ·
    refine ⟨46148771694090521778538349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30765847796060347852358899 46148771694090521778538349)
    ·
      refine ⟨17305789385283945666951881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46148771694090521778538349 17305789385283945666951881)
      ·
        refine ⟨12979342038962959250213911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17305789385283945666951881 12979342038962959250213911)
        ·
          refine ⟨19469013058444438875320867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12979342038962959250213911 19469013058444438875320867)
          ·
            refine ⟨29203519587666658312981301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19469013058444438875320867 29203519587666658312981301)
            ·
              refine ⟨2737829961343749216841997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29203519587666658312981301 2737829961343749216841997)
              ·
                refine ⟨1026686235503905956315749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737829961343749216841997 1026686235503905956315749)
                ·
                  refine ⟨192503669156982366809203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1026686235503905956315749 192503669156982366809203)
                  ·
                    rfl

theorem cell22_1687048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_1687048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687048 prefixEnd_1687048 := by exact prefixLift 1687048
  have htrace : WordTrace (prefixWord ++ tailWord_1687048) baseStart_1687048 baseEnd_1687048 := by
    simpa [prefixWord, tailWord_1687048, baseEnd_1687048] using wordTrace_append hprefix tailTrace_1687048
  have hstable : (prefixWord ++ tailWord_1687048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687048).length < 2 ^ (prefixWord ++ tailWord_1687048).sum := by decide
  have hdescent : baseEnd_1687048 < baseStart_1687048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687059 : List Nat := [1, 1, 1, 2, 1, 6, 10]
def baseStart_1687059 : Nat := 118140960795 + 1687059 * 2 ^ 59
def prefixEnd_1687059 : Nat := 4983230072969 + 3 ^ 40 * 1687059 * 2
def baseEnd_1687059 : Nat := 21389436036879508829725

theorem tailTrace_1687059 : CollatzResearch.WordTrace tailWord_1687059 prefixEnd_1687059 21389436036879508829725 := by
  unfold tailWord_1687059
  simp only [CollatzResearch.WordTrace]
  refine ⟨61532096795080844583368231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41021397863387229722245487 61532096795080844583368231)
  ·
    refine ⟨92298145192621266875052347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61532096795080844583368231 92298145192621266875052347)
    ·
      refine ⟨138447217788931900312578521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92298145192621266875052347 138447217788931900312578521)
      ·
        refine ⟨103835413341698925234433891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138447217788931900312578521 103835413341698925234433891)
        ·
          refine ⟨155753120012548387851650837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103835413341698925234433891 155753120012548387851650837)
          ·
            refine ⟨7300927500588205680546133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155753120012548387851650837 7300927500588205680546133)
            ·
              refine ⟨21389436036879508829725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7300927500588205680546133 21389436036879508829725)
              ·
                rfl

theorem cell22_1687059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 10].length) (baseStart_1687059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687059 prefixEnd_1687059 := by exact prefixLift 1687059
  have htrace : WordTrace (prefixWord ++ tailWord_1687059) baseStart_1687059 baseEnd_1687059 := by
    simpa [prefixWord, tailWord_1687059, baseEnd_1687059] using wordTrace_append hprefix tailTrace_1687059
  have hstable : (prefixWord ++ tailWord_1687059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687059).length < 2 ^ (prefixWord ++ tailWord_1687059).sum := by decide
  have hdescent : baseEnd_1687059 < baseStart_1687059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687061 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1687061 : Nat := 118140960795 + 1687061 * 2 ^ 59
def prefixEnd_1687061 : Nat := 4983230072969 + 3 ^ 40 * 1687061 * 2
def baseEnd_1687061 : Nat := 577515457636619399852569

theorem tailTrace_1687061 : CollatzResearch.WordTrace tailWord_1687061 prefixEnd_1687061 577515457636619399852569 := by
  unfold tailWord_1687061
  simp only [CollatzResearch.WordTrace]
  refine ⟨61532169741073598924941037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41021446494049065949960691 61532169741073598924941037)
  ·
    refine ⟨23074563652902599596852889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61532169741073598924941037 23074563652902599596852889)
    ·
      refine ⟨17305922739676949697639667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23074563652902599596852889 17305922739676949697639667)
      ·
        refine ⟨25958884109515424546459501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17305922739676949697639667 25958884109515424546459501)
        ·
          refine ⟨9734581541068284204922313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25958884109515424546459501 9734581541068284204922313)
          ·
            refine ⟨7300936155801213153691735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9734581541068284204922313 7300936155801213153691735)
            ·
              refine ⟨10951404233701819730537603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300936155801213153691735 10951404233701819730537603)
              ·
                refine ⟨16427106350552729595806405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951404233701819730537603 16427106350552729595806405)
                ·
                  refine ⟨3080082440728636799213701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16427106350552729595806405 3080082440728636799213701)
                  ·
                    refine ⟨577515457636619399852569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080082440728636799213701 577515457636619399852569)
                    ·
                      rfl

theorem cell22_1687061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1687061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687061 prefixEnd_1687061 := by exact prefixLift 1687061
  have htrace : WordTrace (prefixWord ++ tailWord_1687061) baseStart_1687061 baseEnd_1687061 := by
    simpa [prefixWord, tailWord_1687061, baseEnd_1687061] using wordTrace_append hprefix tailTrace_1687061
  have hstable : (prefixWord ++ tailWord_1687061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687061).length < 2 ^ (prefixWord ++ tailWord_1687061).sum := by decide
  have hdescent : baseEnd_1687061 < baseStart_1687061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687110 : List Nat := [6, 1, 1, 1, 4, 9]
def baseStart_1687110 : Nat := 118140960795 + 1687110 * 2 ^ 59
def prefixEnd_1687110 : Nat := 4983230072969 + 3 ^ 40 * 1687110 * 2
def baseEnd_1687110 : Nat := 7130027547382711177499

theorem tailTrace_1687110 : CollatzResearch.WordTrace tailWord_1687110 prefixEnd_1687110 7130027547382711177499 := by
  unfold tailWord_1687110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922936153684252509171087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41022637945264053528983189 1922936153684252509171087)
  ·
    refine ⟨2884404230526378763756631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922936153684252509171087 2884404230526378763756631)
    ·
      refine ⟨4326606345789568145634947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884404230526378763756631 4326606345789568145634947)
      ·
        refine ⟨6489909518684352218452421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326606345789568145634947 6489909518684352218452421)
        ·
          refine ⟨1216858034753316040959829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6489909518684352218452421 1216858034753316040959829)
          ·
            refine ⟨7130027547382711177499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1216858034753316040959829 7130027547382711177499)
            ·
              rfl

theorem cell22_1687110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 9].length) (baseStart_1687110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687110 prefixEnd_1687110 := by exact prefixLift 1687110
  have htrace : WordTrace (prefixWord ++ tailWord_1687110) baseStart_1687110 baseEnd_1687110 := by
    simpa [prefixWord, tailWord_1687110, baseEnd_1687110] using wordTrace_append hprefix tailTrace_1687110
  have hstable : (prefixWord ++ tailWord_1687110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687110).length < 2 ^ (prefixWord ++ tailWord_1687110).sum := by decide
  have hdescent : baseEnd_1687110 < baseStart_1687110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687168 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_1687168 : Nat := 118140960795 + 1687168 * 2 ^ 59
def prefixEnd_1687168 : Nat := 4983230072969 + 3 ^ 40 * 1687168 * 2
def baseEnd_1687168 : Nat := 577552085923306787427241

theorem tailTrace_1687168 : CollatzResearch.WordTrace tailWord_1687168 prefixEnd_1687168 577552085923306787427241 := by
  unfold tailWord_1687168
  simp only [CollatzResearch.WordTrace]
  refine ⟨30768036175842978099543079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41024048234457304132724105 30768036175842978099543079)
  ·
    refine ⟨46152054263764467149314619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30768036175842978099543079 46152054263764467149314619)
    ·
      refine ⟨69228081395646700723971929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46152054263764467149314619 69228081395646700723971929)
      ·
        refine ⟨51921061046735025542978947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69228081395646700723971929 51921061046735025542978947)
        ·
          refine ⟨77881591570102538314468421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51921061046735025542978947 77881591570102538314468421)
          ·
            refine ⟨14602798419394225933962829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77881591570102538314468421 14602798419394225933962829)
            ·
              refine ⟨5476049407272834725236061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14602798419394225933962829 5476049407272834725236061)
              ·
                refine ⟨2053518527727313021963523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5476049407272834725236061 2053518527727313021963523)
                ·
                  refine ⟨3080277791590969532945285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053518527727313021963523 3080277791590969532945285)
                  ·
                    refine ⟨577552085923306787427241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080277791590969532945285 577552085923306787427241)
                    ·
                      rfl

theorem cell22_1687168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_1687168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687168 prefixEnd_1687168 := by exact prefixLift 1687168
  have htrace : WordTrace (prefixWord ++ tailWord_1687168) baseStart_1687168 baseEnd_1687168 := by
    simpa [prefixWord, tailWord_1687168, baseEnd_1687168] using wordTrace_append hprefix tailTrace_1687168
  have hstable : (prefixWord ++ tailWord_1687168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687168).length < 2 ^ (prefixWord ++ tailWord_1687168).sum := by decide
  have hdescent : baseEnd_1687168 < baseStart_1687168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687172 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1687172 : Nat := 118140960795 + 1687172 * 2 ^ 59
def prefixEnd_1687172 : Nat := 4983230072969 + 3 ^ 40 * 1687172 * 2
def baseEnd_1687172 : Nat := 192517818401684036775743

theorem tailTrace_1687172 : CollatzResearch.WordTrace tailWord_1687172 prefixEnd_1687172 192517818401684036775743 := by
  unfold tailWord_1687172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30768109121835732441115885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41024145495780976588154513 30768109121835732441115885)
  ·
    refine ⟨11538040920688399665418457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30768109121835732441115885 11538040920688399665418457)
    ·
      refine ⟨8653530690516299749063843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11538040920688399665418457 8653530690516299749063843)
      ·
        refine ⟨12980296035774449623595765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653530690516299749063843 12980296035774449623595765)
        ·
          refine ⟨1216902753353854652212103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12980296035774449623595765 1216902753353854652212103)
          ·
            refine ⟨1825354130030781978318155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216902753353854652212103 1825354130030781978318155)
            ·
              refine ⟨2738031195046172967477233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825354130030781978318155 2738031195046172967477233)
              ·
                refine ⟨2053523396284629725607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738031195046172967477233 2053523396284629725607925)
                ·
                  refine ⟨192517818401684036775743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2053523396284629725607925 192517818401684036775743)
                  ·
                    rfl

theorem cell22_1687172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1687172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687172 prefixEnd_1687172 := by exact prefixLift 1687172
  have htrace : WordTrace (prefixWord ++ tailWord_1687172) baseStart_1687172 baseEnd_1687172 := by
    simpa [prefixWord, tailWord_1687172, baseEnd_1687172] using wordTrace_append hprefix tailTrace_1687172
  have hstable : (prefixWord ++ tailWord_1687172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687172).length < 2 ^ (prefixWord ++ tailWord_1687172).sum := by decide
  have hdescent : baseEnd_1687172 < baseStart_1687172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687213 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1687213 : Nat := 118140960795 + 1687213 * 2 ^ 59
def prefixEnd_1687213 : Nat := 4983230072969 + 3 ^ 40 * 1687213 * 2
def baseEnd_1687213 : Nat := 577567490342941670052103

theorem tailTrace_1687213 : CollatzResearch.WordTrace tailWord_1687213 prefixEnd_1687213 577567490342941670052103 := by
  unfold tailWord_1687213
  simp only [CollatzResearch.WordTrace]
  refine ⟨61537713636522928884474293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41025142424348619256316195 61537713636522928884474293)
  ·
    refine ⟨5769160653424024582919465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61537713636522928884474293 5769160653424024582919465)
    ·
      refine ⟨4326870490068018437189599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5769160653424024582919465 4326870490068018437189599)
      ·
        refine ⟨6490305735102027655784399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326870490068018437189599 6490305735102027655784399)
        ·
          refine ⟨9735458602653041483676599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490305735102027655784399 9735458602653041483676599)
          ·
            refine ⟨14603187903979562225514899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735458602653041483676599 14603187903979562225514899)
            ·
              refine ⟨21904781855969343338272349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14603187903979562225514899 21904781855969343338272349)
              ·
                refine ⟨8214293195988503751852131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21904781855969343338272349 8214293195988503751852131)
                ·
                  refine ⟨12321439793982755627778197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214293195988503751852131 12321439793982755627778197)
                  ·
                    refine ⟨577567490342941670052103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12321439793982755627778197 577567490342941670052103)
                    ·
                      rfl

theorem cell22_1687213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1687213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687213 prefixEnd_1687213 := by exact prefixLift 1687213
  have htrace : WordTrace (prefixWord ++ tailWord_1687213) baseStart_1687213 baseEnd_1687213 := by
    simpa [prefixWord, tailWord_1687213, baseEnd_1687213] using wordTrace_append hprefix tailTrace_1687213
  have hstable : (prefixWord ++ tailWord_1687213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687213).length < 2 ^ (prefixWord ++ tailWord_1687213).sum := by decide
  have hdescent : baseEnd_1687213 < baseStart_1687213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687228 : List Nat := [2, 2, 2, 3, 1, 4, 8]
def baseStart_1687228 : Nat := 118140960795 + 1687228 * 2 ^ 59
def prefixEnd_1687228 : Nat := 4983230072969 + 3 ^ 40 * 1687228 * 2
def baseEnd_1687228 : Nat := 21391578709240245589891

theorem tailTrace_1687228 : CollatzResearch.WordTrace tailWord_1687228 prefixEnd_1687228 21391578709240245589891 := by
  unfold tailWord_1687228
  simp only [CollatzResearch.WordTrace]
  refine ⟨30769130365734293223135169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41025507154312390964180225 30769130365734293223135169)
  ·
    refine ⟨23076847774300719917351377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30769130365734293223135169 23076847774300719917351377)
    ·
      refine ⟨17307635830725539938013533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23076847774300719917351377 17307635830725539938013533)
      ·
        refine ⟨6490363436522077476755075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17307635830725539938013533 6490363436522077476755075)
        ·
          refine ⟨9735545154783116215132613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490363436522077476755075 9735545154783116215132613)
          ·
            refine ⟨1825414716521834290337365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9735545154783116215132613 1825414716521834290337365)
            ·
              refine ⟨21391578709240245589891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1825414716521834290337365 21391578709240245589891)
              ·
                rfl

theorem cell22_1687228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 8].length) (baseStart_1687228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687228 prefixEnd_1687228 := by exact prefixLift 1687228
  have htrace : WordTrace (prefixWord ++ tailWord_1687228) baseStart_1687228 baseEnd_1687228 := by
    simpa [prefixWord, tailWord_1687228, baseEnd_1687228] using wordTrace_append hprefix tailTrace_1687228
  have hstable : (prefixWord ++ tailWord_1687228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687228).length < 2 ^ (prefixWord ++ tailWord_1687228).sum := by decide
  have hdescent : baseEnd_1687228 < baseStart_1687228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687230 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1687230 : Nat := 118140960795 + 1687230 * 2 ^ 59
def prefixEnd_1687230 : Nat := 4983230072969 + 3 ^ 40 * 1687230 * 2
def baseEnd_1687230 : Nat := 577573309790359292377051

theorem tailTrace_1687230 : CollatzResearch.WordTrace tailWord_1687230 prefixEnd_1687230 577573309790359292377051 := by
  unfold tailWord_1687230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692291709682667598480393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41025555784974227191895429 7692291709682667598480393)
  ·
    refine ⟨5769218782262000698860295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7692291709682667598480393 5769218782262000698860295)
    ·
      refine ⟨8653828173393001048290443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769218782262000698860295 8653828173393001048290443)
      ·
        refine ⟨12980742260089501572435665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653828173393001048290443 12980742260089501572435665)
        ·
          refine ⟨9735556695067126179326749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12980742260089501572435665 9735556695067126179326749)
          ·
            refine ⟨3650833760650172317247531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9735556695067126179326749 3650833760650172317247531)
            ·
              refine ⟨5476250640975258475871297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650833760650172317247531 5476250640975258475871297)
              ·
                refine ⟨4107187980731443856903473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476250640975258475871297 4107187980731443856903473)
                ·
                  refine ⟨3080390985548582892677605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107187980731443856903473 3080390985548582892677605)
                  ·
                    refine ⟨577573309790359292377051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080390985548582892677605 577573309790359292377051)
                    ·
                      rfl

theorem cell22_1687230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1687230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687230 prefixEnd_1687230 := by exact prefixLift 1687230
  have htrace : WordTrace (prefixWord ++ tailWord_1687230) baseStart_1687230 baseEnd_1687230 := by
    simpa [prefixWord, tailWord_1687230, baseEnd_1687230] using wordTrace_append hprefix tailTrace_1687230
  have hstable : (prefixWord ++ tailWord_1687230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687230).length < 2 ^ (prefixWord ++ tailWord_1687230).sum := by decide
  have hdescent : baseEnd_1687230 < baseStart_1687230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687245 : List Nat := [1, 6, 2, 1, 1, 1, 1, 9]
def baseStart_1687245 : Nat := 118140960795 + 1687245 * 2 ^ 59
def prefixEnd_1687245 : Nat := 4983230072969 + 3 ^ 40 * 1687245 * 2
def baseEnd_1687245 : Nat := 64175382732989361472445

theorem tailTrace_1687245 : CollatzResearch.WordTrace tailWord_1687245 prefixEnd_1687245 64175382732989361472445 := by
  unfold tailWord_1687245
  simp only [CollatzResearch.WordTrace]
  refine ⟨61538880772406998349639189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41025920514937998899759459 61538880772406998349639189)
  ·
    refine ⟨2884635036206578047639337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61538880772406998349639189 2884635036206578047639337)
    ·
      refine ⟨2163476277154933535729503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884635036206578047639337 2163476277154933535729503)
      ·
        refine ⟨3245214415732400303594255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163476277154933535729503 3245214415732400303594255)
        ·
          refine ⟨4867821623598600455391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245214415732400303594255 4867821623598600455391383)
          ·
            refine ⟨7301732435397900683087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867821623598600455391383 7301732435397900683087075)
            ·
              refine ⟨10952598653096851024630613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301732435397900683087075 10952598653096851024630613)
              ·
                refine ⟨64175382732989361472445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10952598653096851024630613 64175382732989361472445)
                ·
                  rfl

theorem cell22_1687245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 9].length) (baseStart_1687245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687245 prefixEnd_1687245 := by exact prefixLift 1687245
  have htrace : WordTrace (prefixWord ++ tailWord_1687245) baseStart_1687245 baseEnd_1687245 := by
    simpa [prefixWord, tailWord_1687245, baseEnd_1687245] using wordTrace_append hprefix tailTrace_1687245
  have hstable : (prefixWord ++ tailWord_1687245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687245).length < 2 ^ (prefixWord ++ tailWord_1687245).sum := by decide
  have hdescent : baseEnd_1687245 < baseStart_1687245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687380 : List Nat := [2, 4, 1, 1, 3, 2, 1, 8]
def baseStart_1687380 : Nat := 118140960795 + 1687380 * 2 ^ 59
def prefixEnd_1687380 : Nat := 4983230072969 + 3 ^ 40 * 1687380 * 2
def baseEnd_1687380 : Nat := 64180517539534322347399

theorem tailTrace_1687380 : CollatzResearch.WordTrace tailWord_1687380 prefixEnd_1687380 64180517539534322347399 := by
  unfold tailWord_1687380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771902313458958202901797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41029203084611944270535729 30771902313458958202901797)
  ·
    refine ⟨5769731683773554663044087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30771902313458958202901797 5769731683773554663044087)
    ·
      refine ⟨8654597525660331994566131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769731683773554663044087 8654597525660331994566131)
      ·
        refine ⟨12981896288490497991849197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8654597525660331994566131 12981896288490497991849197)
        ·
          refine ⟨4868211108183936746943449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12981896288490497991849197 4868211108183936746943449)
          ·
            refine ⟨3651158331137952560207587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868211108183936746943449 3651158331137952560207587)
            ·
              refine ⟨5476737496706928840311381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651158331137952560207587 5476737496706928840311381)
              ·
                refine ⟨64180517539534322347399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5476737496706928840311381 64180517539534322347399)
                ·
                  rfl

theorem cell22_1687380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_1687380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687380 prefixEnd_1687380 := by exact prefixLift 1687380
  have htrace : WordTrace (prefixWord ++ tailWord_1687380) baseStart_1687380 baseEnd_1687380 := by
    simpa [prefixWord, tailWord_1687380, baseEnd_1687380] using wordTrace_append hprefix tailTrace_1687380
  have hstable : (prefixWord ++ tailWord_1687380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687380).length < 2 ^ (prefixWord ++ tailWord_1687380).sum := by decide
  have hdescent : baseEnd_1687380 < baseStart_1687380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687423 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1687423 : Nat := 118140960795 + 1687423 * 2 ^ 59
def prefixEnd_1687423 : Nat := 4983230072969 + 3 ^ 40 * 1687423 * 2
def baseEnd_1687423 : Nat := 577639377634571122301459

theorem tailTrace_1687423 : CollatzResearch.WordTrace tailWord_1687423 prefixEnd_1687423 577639377634571122301459 := by
  unfold tailWord_1687423
  simp only [CollatzResearch.WordTrace]
  refine ⟨61545372965762134749618923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41030248643841423166412615 61545372965762134749618923)
  ·
    refine ⟨92318059448643202124428385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61545372965762134749618923 92318059448643202124428385)
    ·
      refine ⟨69238544586482401593321289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92318059448643202124428385 69238544586482401593321289)
      ·
        refine ⟨51928908439861801194990967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69238544586482401593321289 51928908439861801194990967)
        ·
          refine ⟨77893362659792701792486451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51928908439861801194990967 77893362659792701792486451)
          ·
            refine ⟨116840043989689052688729677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77893362659792701792486451 116840043989689052688729677)
            ·
              refine ⟨43815016496133394758273629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116840043989689052688729677 43815016496133394758273629)
              ·
                refine ⟨16430631186050023034352611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43815016496133394758273629 16430631186050023034352611)
                ·
                  refine ⟨24645946779075034551528917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16430631186050023034352611 24645946779075034551528917)
                  ·
                    refine ⟨577639377634571122301459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24645946779075034551528917 577639377634571122301459)
                    ·
                      rfl

theorem cell22_1687423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1687423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687423 prefixEnd_1687423 := by exact prefixLift 1687423
  have htrace : WordTrace (prefixWord ++ tailWord_1687423) baseStart_1687423 baseEnd_1687423 := by
    simpa [prefixWord, tailWord_1687423, baseEnd_1687423] using wordTrace_append hprefix tailTrace_1687423
  have hstable : (prefixWord ++ tailWord_1687423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687423).length < 2 ^ (prefixWord ++ tailWord_1687423).sum := by decide
  have hdescent : baseEnd_1687423 < baseStart_1687423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687463 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1687463 : Nat := 118140960795 + 1687463 * 2 ^ 59
def prefixEnd_1687463 : Nat := 4983230072969 + 3 ^ 40 * 1687463 * 2
def baseEnd_1687463 : Nat := 577653070452024351301337

theorem tailTrace_1687463 : CollatzResearch.WordTrace tailWord_1687463 prefixEnd_1687463 577653070452024351301337 := by
  unfold tailWord_1687463
  simp only [CollatzResearch.WordTrace]
  refine ⟨61546831885617221581075043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41031221257078147720716695 61546831885617221581075043)
  ·
    refine ⟨92320247828425832371612565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61546831885617221581075043 92320247828425832371612565)
    ·
      refine ⟨4327511616957460892419339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92320247828425832371612565 4327511616957460892419339)
      ·
        refine ⟨6491267425436191338629009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327511616957460892419339 6491267425436191338629009)
        ·
          refine ⟨4868450569077143503971757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491267425436191338629009 4868450569077143503971757)
          ·
            refine ⟨1825668963403928813989409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4868450569077143503971757 1825668963403928813989409)
            ·
              refine ⟨1369251722552946610492057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825668963403928813989409 1369251722552946610492057)
              ·
                refine ⟨1026938791914709957869043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369251722552946610492057 1026938791914709957869043)
                ·
                  refine ⟨1540408187872064936803565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026938791914709957869043 1540408187872064936803565)
                  ·
                    refine ⟨577653070452024351301337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540408187872064936803565 577653070452024351301337)
                    ·
                      rfl

theorem cell22_1687463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1687463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687463 prefixEnd_1687463 := by exact prefixLift 1687463
  have htrace : WordTrace (prefixWord ++ tailWord_1687463) baseStart_1687463 baseEnd_1687463 := by
    simpa [prefixWord, tailWord_1687463, baseEnd_1687463] using wordTrace_append hprefix tailTrace_1687463
  have hstable : (prefixWord ++ tailWord_1687463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687463).length < 2 ^ (prefixWord ++ tailWord_1687463).sum := by decide
  have hdescent : baseEnd_1687463 < baseStart_1687463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687502 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1687502 : Nat := 118140960795 + 1687502 * 2 ^ 59
def prefixEnd_1687502 : Nat := 4983230072969 + 3 ^ 40 * 1687502 * 2
def baseEnd_1687502 : Nat := 577666420949041249576217

theorem tailTrace_1687502 : CollatzResearch.WordTrace tailWord_1687502 prefixEnd_1687502 577666420949041249576217 := by
  unfold tailWord_1687502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7693531791559491405218095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41032169554983954161163173 7693531791559491405218095)
  ·
    refine ⟨11540297687339237107827143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7693531791559491405218095 11540297687339237107827143)
    ·
      refine ⟨17310446531008855661740715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11540297687339237107827143 17310446531008855661740715)
      ·
        refine ⟨25965669796513283492611073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310446531008855661740715 25965669796513283492611073)
        ·
          refine ⟨19474252347384962619458305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25965669796513283492611073 19474252347384962619458305)
          ·
            refine ⟨14605689260538721964593729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19474252347384962619458305 14605689260538721964593729)
            ·
              refine ⟨10954266945404041473445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14605689260538721964593729 10954266945404041473445297)
              ·
                refine ⟨8215700209053031105083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954266945404041473445297 8215700209053031105083973)
                ·
                  refine ⟨1540443789197443332203245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8215700209053031105083973 1540443789197443332203245)
                  ·
                    refine ⟨577666420949041249576217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540443789197443332203245 577666420949041249576217)
                    ·
                      rfl

theorem cell22_1687502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1687502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687502 prefixEnd_1687502 := by exact prefixLift 1687502
  have htrace : WordTrace (prefixWord ++ tailWord_1687502) baseStart_1687502 baseEnd_1687502 := by
    simpa [prefixWord, tailWord_1687502, baseEnd_1687502] using wordTrace_append hprefix tailTrace_1687502
  have hstable : (prefixWord ++ tailWord_1687502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687502).length < 2 ^ (prefixWord ++ tailWord_1687502).sum := by decide
  have hdescent : baseEnd_1687502 < baseStart_1687502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687519 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 2, 3]
def baseStart_1687519 : Nat := 118140960795 + 1687519 * 2 ^ 59
def prefixEnd_1687519 : Nat := 4983230072969 + 3 ^ 40 * 1687519 * 2
def baseEnd_1687519 : Nat := 577672240396458871901165

theorem tailTrace_1687519 : CollatzResearch.WordTrace tailWord_1687519 prefixEnd_1687519 577672240396458871901165 := by
  unfold tailWord_1687519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61548874373414343145113611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41032582915609562096742407 61548874373414343145113611)
  ·
    refine ⟨92323311560121514717670417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61548874373414343145113611 92323311560121514717670417)
    ·
      refine ⟨69242483670091136038252813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92323311560121514717670417 69242483670091136038252813)
      ·
        refine ⟨25965931376284176014344805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69242483670091136038252813 25965931376284176014344805)
        ·
          refine ⟨4868612133053283002689651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25965931376284176014344805 4868612133053283002689651)
          ·
            refine ⟨7302918199579924504034477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868612133053283002689651 7302918199579924504034477)
            ·
              refine ⟨2738594324842471689012929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7302918199579924504034477 2738594324842471689012929)
              ·
                refine ⟨2053945743631853766759697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738594324842471689012929 2053945743631853766759697)
                ·
                  refine ⟨1540459307723890325069773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2053945743631853766759697 1540459307723890325069773)
                  ·
                    refine ⟨577672240396458871901165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540459307723890325069773 577672240396458871901165)
                    ·
                      rfl

theorem cell22_1687519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_1687519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687519 prefixEnd_1687519 := by exact prefixLift 1687519
  have htrace : WordTrace (prefixWord ++ tailWord_1687519) baseStart_1687519 baseEnd_1687519 := by
    simpa [prefixWord, tailWord_1687519, baseEnd_1687519] using wordTrace_append hprefix tailTrace_1687519
  have hstable : (prefixWord ++ tailWord_1687519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687519).length < 2 ^ (prefixWord ++ tailWord_1687519).sum := by decide
  have hdescent : baseEnd_1687519 < baseStart_1687519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687547 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 3, 3]
def baseStart_1687547 : Nat := 118140960795 + 1687547 * 2 ^ 59
def prefixEnd_1687547 : Nat := 4983230072969 + 3 ^ 40 * 1687547 * 2
def baseEnd_1687547 : Nat := 577681825368676132201079

theorem tailTrace_1687547 : CollatzResearch.WordTrace tailWord_1687547 prefixEnd_1687547 577681825368676132201079 := by
  unfold tailWord_1687547
  simp only [CollatzResearch.WordTrace]
  refine ⟨61549895617312903927132895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41033263744875269284755263 61549895617312903927132895)
  ·
    refine ⟨92324843425969355890699343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61549895617312903927132895 92324843425969355890699343)
    ·
      refine ⟨138487265138954033836049015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92324843425969355890699343 138487265138954033836049015)
      ·
        refine ⟨207730897708431050754073523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138487265138954033836049015 207730897708431050754073523)
        ·
          refine ⟨311596346562646576131110285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207730897708431050754073523 311596346562646576131110285)
          ·
            refine ⟨116848629960992466049166357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311596346562646576131110285 116848629960992466049166357)
            ·
              refine ⟨5477279529421521846054673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116848629960992466049166357 5477279529421521846054673)
              ·
                refine ⟨4107959647066141384541005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5477279529421521846054673 4107959647066141384541005)
                ·
                  refine ⟨1540484867649803019202877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4107959647066141384541005 1540484867649803019202877)
                  ·
                    refine ⟨577681825368676132201079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540484867649803019202877 577681825368676132201079)
                    ·
                      rfl

theorem cell22_1687547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].length) (baseStart_1687547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687547 prefixEnd_1687547 := by exact prefixLift 1687547
  have htrace : WordTrace (prefixWord ++ tailWord_1687547) baseStart_1687547 baseEnd_1687547 := by
    simpa [prefixWord, tailWord_1687547, baseEnd_1687547] using wordTrace_append hprefix tailTrace_1687547
  have hstable : (prefixWord ++ tailWord_1687547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687547).length < 2 ^ (prefixWord ++ tailWord_1687547).sum := by decide
  have hdescent : baseEnd_1687547 < baseStart_1687547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687560 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_1687560 : Nat := 118140960795 + 1687560 * 2 ^ 59
def prefixEnd_1687560 : Nat := 4983230072969 + 3 ^ 40 * 1687560 * 2
def baseEnd_1687560 : Nat := 192562091844782810542013

theorem tailTrace_1687560 : CollatzResearch.WordTrace tailWord_1687560 prefixEnd_1687560 192562091844782810542013 := by
  unfold tailWord_1687560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30775184883132903573678067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41033579844177204764904089 30775184883132903573678067)
  ·
    refine ⟨46162777324699355360517101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30775184883132903573678067 46162777324699355360517101)
    ·
      refine ⟨17311041496762258260193913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46162777324699355360517101 17311041496762258260193913)
      ·
        refine ⟨12983281122571693695145435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17311041496762258260193913 12983281122571693695145435)
        ·
          refine ⟨19474921683857540542718153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983281122571693695145435 19474921683857540542718153)
          ·
            refine ⟨14606191262893155407038615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19474921683857540542718153 14606191262893155407038615)
            ·
              refine ⟨21909286894339733110557923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14606191262893155407038615 21909286894339733110557923)
              ·
                refine ⟨32863930341509599665836885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21909286894339733110557923 32863930341509599665836885)
                ·
                  refine ⟨192562091844782810542013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32863930341509599665836885 192562091844782810542013)
                  ·
                    rfl

theorem cell22_1687560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_1687560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687560 prefixEnd_1687560 := by exact prefixLift 1687560
  have htrace : WordTrace (prefixWord ++ tailWord_1687560) baseStart_1687560 baseEnd_1687560 := by
    simpa [prefixWord, tailWord_1687560, baseEnd_1687560] using wordTrace_append hprefix tailTrace_1687560
  have hstable : (prefixWord ++ tailWord_1687560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687560).length < 2 ^ (prefixWord ++ tailWord_1687560).sum := by decide
  have hdescent : baseEnd_1687560 < baseStart_1687560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687581 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1687581 : Nat := 118140960795 + 1687581 * 2 ^ 59
def prefixEnd_1687581 : Nat := 4983230072969 + 3 ^ 40 * 1687581 * 2
def baseEnd_1687581 : Nat := 577693464263511376850975

theorem tailTrace_1687581 : CollatzResearch.WordTrace tailWord_1687581 prefixEnd_1687581 577693464263511376850975 := by
  unfold tailWord_1687581
  simp only [CollatzResearch.WordTrace]
  refine ⟨61551135699189727733870597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41034090466126485155913731 61551135699189727733870597)
  ·
    refine ⟨11540837943598073950100737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61551135699189727733870597 11540837943598073950100737)
    ·
      refine ⟨8655628457698555462575553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11540837943598073950100737 8655628457698555462575553)
      ·
        refine ⟨6491721343273916596931665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8655628457698555462575553 6491721343273916596931665)
        ·
          refine ⟨4868791007455437447698749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491721343273916596931665 4868791007455437447698749)
          ·
            refine ⟨1825796627795789042887031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4868791007455437447698749 1825796627795789042887031)
            ·
              refine ⟨2738694941693683564330547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825796627795789042887031 2738694941693683564330547)
              ·
                refine ⟨4108042412540525346495821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738694941693683564330547 4108042412540525346495821)
                ·
                  refine ⟨1540515904702697004935933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4108042412540525346495821 1540515904702697004935933)
                  ·
                    refine ⟨577693464263511376850975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540515904702697004935933 577693464263511376850975)
                    ·
                      rfl

theorem cell22_1687581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1687581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687581 prefixEnd_1687581 := by exact prefixLift 1687581
  have htrace : WordTrace (prefixWord ++ tailWord_1687581) baseStart_1687581 baseEnd_1687581 := by
    simpa [prefixWord, tailWord_1687581, baseEnd_1687581] using wordTrace_append hprefix tailTrace_1687581
  have hstable : (prefixWord ++ tailWord_1687581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687581).length < 2 ^ (prefixWord ++ tailWord_1687581).sum := by decide
  have hdescent : baseEnd_1687581 < baseStart_1687581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687594 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1687594 : Nat := 118140960795 + 1687594 * 2 ^ 59
def prefixEnd_1687594 : Nat := 4983230072969 + 3 ^ 40 * 1687594 * 2
def baseEnd_1687594 : Nat := 192565971476394558758645

theorem tailTrace_1687594 : CollatzResearch.WordTrace tailWord_1687594 prefixEnd_1687594 192565971476394558758645 := by
  unfold tailWord_1687594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387902462035657738523459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41034406565428420636062557 15387902462035657738523459)
  ·
    refine ⟨23081853693053486607785189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15387902462035657738523459 23081853693053486607785189)
    ·
      refine ⟨4327847567447528738959723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23081853693053486607785189 4327847567447528738959723)
      ·
        refine ⟨6491771351171293108439585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327847567447528738959723 6491771351171293108439585)
        ·
          refine ⟨4868828513378469831329689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491771351171293108439585 4868828513378469831329689)
          ·
            refine ⟨3651621385033852373497267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868828513378469831329689 3651621385033852373497267)
            ·
              refine ⟨5477432077550778560245901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651621385033852373497267 5477432077550778560245901)
              ·
                refine ⟨2054037029081541960092213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5477432077550778560245901 2054037029081541960092213)
                ·
                  refine ⟨192565971476394558758645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2054037029081541960092213 192565971476394558758645)
                  ·
                    rfl

theorem cell22_1687594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1687594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687594 prefixEnd_1687594 := by exact prefixLift 1687594
  have htrace : WordTrace (prefixWord ++ tailWord_1687594) baseStart_1687594 baseEnd_1687594 := by
    simpa [prefixWord, tailWord_1687594, baseEnd_1687594] using wordTrace_append hprefix tailTrace_1687594
  have hstable : (prefixWord ++ tailWord_1687594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687594).length < 2 ^ (prefixWord ++ tailWord_1687594).sum := by decide
  have hdescent : baseEnd_1687594 < baseStart_1687594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687652 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1687652 : Nat := 118140960795 + 1687652 * 2 ^ 59
def prefixEnd_1687652 : Nat := 4983230072969 + 3 ^ 40 * 1687652 * 2
def baseEnd_1687652 : Nat := 577717769014490858325757

theorem tailTrace_1687652 : CollatzResearch.WordTrace tailWord_1687652 prefixEnd_1687652 577717769014490858325757 := by
  unfold tailWord_1687652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776862640966253429852605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41035816854621671239803473 30776862640966253429852605)
  ·
    refine ⟨11541323490362345036194727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30776862640966253429852605 11541323490362345036194727)
    ·
      refine ⟨17311985235543517554292091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541323490362345036194727 17311985235543517554292091)
      ·
        refine ⟨25967977853315276331438137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311985235543517554292091 25967977853315276331438137)
        ·
          refine ⟨19475983389986457248578603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25967977853315276331438137 19475983389986457248578603)
          ·
            refine ⟨29213975084979685872867905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19475983389986457248578603 29213975084979685872867905)
            ·
              refine ⟨21910481313734764404650929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29213975084979685872867905 21910481313734764404650929)
              ·
                refine ⟨16432860985301073303488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21910481313734764404650929 16432860985301073303488197)
                ·
                  refine ⟨3081161434743951244404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16432860985301073303488197 3081161434743951244404037)
                  ·
                    refine ⟨577717769014490858325757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081161434743951244404037 577717769014490858325757)
                    ·
                      rfl

theorem cell22_1687652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1687652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687652 prefixEnd_1687652 := by exact prefixLift 1687652
  have htrace : WordTrace (prefixWord ++ tailWord_1687652) baseStart_1687652 baseEnd_1687652 := by
    simpa [prefixWord, tailWord_1687652, baseEnd_1687652] using wordTrace_append hprefix tailTrace_1687652
  have hstable : (prefixWord ++ tailWord_1687652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687652).length < 2 ^ (prefixWord ++ tailWord_1687652).sum := by decide
  have hdescent : baseEnd_1687652 < baseStart_1687652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687688 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1687688 : Nat := 118140960795 + 1687688 * 2 ^ 59
def prefixEnd_1687688 : Nat := 4983230072969 + 3 ^ 40 * 1687688 * 2
def baseEnd_1687688 : Nat := 577730092550198764425647

theorem tailTrace_1687688 : CollatzResearch.WordTrace tailWord_1687688 prefixEnd_1687688 577730092550198764425647 := by
  unfold tailWord_1687688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30777519154901042504007859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41036692206534723338677145 30777519154901042504007859)
  ·
    refine ⟨46166278732351563756011789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30777519154901042504007859 46166278732351563756011789)
    ·
      refine ⟨17312354524631836408504421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46166278732351563756011789 17312354524631836408504421)
      ·
        refine ⟨3246066473368469326594579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17312354524631836408504421 3246066473368469326594579)
        ·
          refine ⟨4869099710052703989891869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246066473368469326594579 4869099710052703989891869)
          ·
            refine ⟨1825912391269763996209451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4869099710052703989891869 1825912391269763996209451)
            ·
              refine ⟨2738868586904645994314177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825912391269763996209451 2738868586904645994314177)
              ·
                refine ⟨2054151440178484495735633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738868586904645994314177 2054151440178484495735633)
                ·
                  refine ⟨1540613580133863371801725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054151440178484495735633 1540613580133863371801725)
                  ·
                    refine ⟨577730092550198764425647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540613580133863371801725 577730092550198764425647)
                    ·
                      rfl

theorem cell22_1687688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1687688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687688 prefixEnd_1687688 := by exact prefixLift 1687688
  have htrace : WordTrace (prefixWord ++ tailWord_1687688) baseStart_1687688 baseEnd_1687688 := by
    simpa [prefixWord, tailWord_1687688, baseEnd_1687688] using wordTrace_append hprefix tailTrace_1687688
  have hstable : (prefixWord ++ tailWord_1687688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687688).length < 2 ^ (prefixWord ++ tailWord_1687688).sum := by decide
  have hdescent : baseEnd_1687688 < baseStart_1687688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687802 : List Nat := [3, 1, 1, 1, 1, 15]
def baseStart_1687802 : Nat := 118140960795 + 1687802 * 2 ^ 59
def prefixEnd_1687802 : Nat := 4983230072969 + 3 ^ 40 * 1687802 * 2
def baseEnd_1687802 : Nat := 7132952062715314408337

theorem tailTrace_1687802 : CollatzResearch.WordTrace tailWord_1687802 prefixEnd_1687802 7132952062715314408337 := by
  unfold tailWord_1687802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389799057847270619416415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41039464154259388318443773 15389799057847270619416415)
  ·
    refine ⟨23084698586770905929124623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15389799057847270619416415 23084698586770905929124623)
    ·
      refine ⟨34627047880156358893686935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23084698586770905929124623 34627047880156358893686935)
      ·
        refine ⟨51940571820234538340530403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34627047880156358893686935 51940571820234538340530403)
        ·
          refine ⟨77910857730351807510795605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51940571820234538340530403 77910857730351807510795605)
          ·
            refine ⟨7132952062715314408337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 77910857730351807510795605 7132952062715314408337)
            ·
              rfl

theorem cell22_1687802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 15].length) (baseStart_1687802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687802 prefixEnd_1687802 := by exact prefixLift 1687802
  have htrace : WordTrace (prefixWord ++ tailWord_1687802) baseStart_1687802 baseEnd_1687802 := by
    simpa [prefixWord, tailWord_1687802, baseEnd_1687802] using wordTrace_append hprefix tailTrace_1687802
  have hstable : (prefixWord ++ tailWord_1687802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687802).length < 2 ^ (prefixWord ++ tailWord_1687802).sum := by decide
  have hdescent : baseEnd_1687802 < baseStart_1687802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687838 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1687838 : Nat := 118140960795 + 1687838 * 2 ^ 59
def prefixEnd_1687838 : Nat := 4983230072969 + 3 ^ 40 * 1687838 * 2
def baseEnd_1687838 : Nat := 577781440615648373175187

theorem tailTrace_1687838 : CollatzResearch.WordTrace tailWord_1687838 prefixEnd_1687838 577781440615648373175187 := by
  unfold tailWord_1687838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695063657407332578247021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41040339506172440417317445 7695063657407332578247021)
  ·
    refine ⟨2885648871527749716842633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7695063657407332578247021 2885648871527749716842633)
    ·
      refine ⟨2164236653645812287631975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2885648871527749716842633 2164236653645812287631975)
      ·
        refine ⟨3246354980468718431447963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164236653645812287631975 3246354980468718431447963)
        ·
          refine ⟨4869532470703077647171945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246354980468718431447963 4869532470703077647171945)
          ·
            refine ⟨3652149353027308235378959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4869532470703077647171945 3652149353027308235378959)
            ·
              refine ⟨5478224029540962353068439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652149353027308235378959 5478224029540962353068439)
              ·
                refine ⟨8217336044311443529602659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478224029540962353068439 8217336044311443529602659)
                ·
                  refine ⟨12326004066467165294403989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8217336044311443529602659 12326004066467165294403989)
                  ·
                    refine ⟨577781440615648373175187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12326004066467165294403989 577781440615648373175187)
                    ·
                      rfl

theorem cell22_1687838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1687838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687838 prefixEnd_1687838 := by exact prefixLift 1687838
  have htrace : WordTrace (prefixWord ++ tailWord_1687838) baseStart_1687838 baseEnd_1687838 := by
    simpa [prefixWord, tailWord_1687838, baseEnd_1687838] using wordTrace_append hprefix tailTrace_1687838
  have hstable : (prefixWord ++ tailWord_1687838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687838).length < 2 ^ (prefixWord ++ tailWord_1687838).sum := by decide
  have hdescent : baseEnd_1687838 < baseStart_1687838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687868 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_1687868 : Nat := 118140960795 + 1687868 * 2 ^ 59
def prefixEnd_1687868 : Nat := 4983230072969 + 3 ^ 40 * 1687868 * 2
def baseEnd_1687868 : Nat := 577791710228738294925095

theorem tailTrace_1687868 : CollatzResearch.WordTrace tailWord_1687868 prefixEnd_1687868 577791710228738294925095 := by
  unfold tailWord_1687868
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780801724574987874784129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41041068966099983833045505 30780801724574987874784129)
  ·
    refine ⟨23085601293431240906088097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30780801724574987874784129 23085601293431240906088097)
    ·
      refine ⟨17314200970073430679566073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23085601293431240906088097 17314200970073430679566073)
      ·
        refine ⟨12985650727555073009674555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17314200970073430679566073 12985650727555073009674555)
        ·
          refine ⟨19478476091332609514511833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985650727555073009674555 19478476091332609514511833)
          ·
            refine ⟨14608857068499457135883875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19478476091332609514511833 14608857068499457135883875)
            ·
              refine ⟨21913285602749185703825813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608857068499457135883875 21913285602749185703825813)
              ·
                refine ⟨1027185262628868079866835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21913285602749185703825813 1027185262628868079866835)
                ·
                  refine ⟨1540777893943302119800253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027185262628868079866835 1540777893943302119800253)
                  ·
                    refine ⟨577791710228738294925095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540777893943302119800253 577791710228738294925095)
                    ·
                      rfl

theorem cell22_1687868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_1687868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687868 prefixEnd_1687868 := by exact prefixLift 1687868
  have htrace : WordTrace (prefixWord ++ tailWord_1687868) baseStart_1687868 baseEnd_1687868 := by
    simpa [prefixWord, tailWord_1687868, baseEnd_1687868] using wordTrace_append hprefix tailTrace_1687868
  have hstable : (prefixWord ++ tailWord_1687868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687868).length < 2 ^ (prefixWord ++ tailWord_1687868).sum := by decide
  have hdescent : baseEnd_1687868 < baseStart_1687868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687879 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1687879 : Nat := 118140960795 + 1687879 * 2 ^ 59
def prefixEnd_1687879 : Nat := 4983230072969 + 3 ^ 40 * 1687879 * 2
def baseEnd_1687879 : Nat := 577795475753537932900061

theorem tailTrace_1687879 : CollatzResearch.WordTrace tailWord_1687879 prefixEnd_1687879 577795475753537932900061 := by
  unfold tailWord_1687879
  simp only [CollatzResearch.WordTrace]
  refine ⟨61562004652110124628218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41041336434740083085479127 61562004652110124628218691)
  ·
    refine ⟨92343006978165186942328037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61562004652110124628218691 92343006978165186942328037)
    ·
      refine ⟨17314313808405972551686507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92343006978165186942328037 17314313808405972551686507)
      ·
        refine ⟨25971470712608958827529761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17314313808405972551686507 25971470712608958827529761)
        ·
          refine ⟨19478603034456719120647321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25971470712608958827529761 19478603034456719120647321)
          ·
            refine ⟨14608952275842539340485491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19478603034456719120647321 14608952275842539340485491)
            ·
              refine ⟨21913428413763809010728237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608952275842539340485491 21913428413763809010728237)
              ·
                refine ⟨8217535655161428379023089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21913428413763809010728237 8217535655161428379023089)
                ·
                  refine ⟨6163151741371071284267317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217535655161428379023089 6163151741371071284267317)
                  ·
                    refine ⟨577795475753537932900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6163151741371071284267317 577795475753537932900061)
                    ·
                      rfl

theorem cell22_1687879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1687879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687879 prefixEnd_1687879 := by exact prefixLift 1687879
  have htrace : WordTrace (prefixWord ++ tailWord_1687879) baseStart_1687879 baseEnd_1687879 := by
    simpa [prefixWord, tailWord_1687879, baseEnd_1687879] using wordTrace_append hprefix tailTrace_1687879
  have hstable : (prefixWord ++ tailWord_1687879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687879).length < 2 ^ (prefixWord ++ tailWord_1687879).sum := by decide
  have hdescent : baseEnd_1687879 < baseStart_1687879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687975 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1687975 : Nat := 118140960795 + 1687975 * 2 ^ 59
def prefixEnd_1687975 : Nat := 4983230072969 + 3 ^ 40 * 1687975 * 2
def baseEnd_1687975 : Nat := 577828338515425682499767

theorem tailTrace_1687975 : CollatzResearch.WordTrace tailWord_1687975 prefixEnd_1687975 577828338515425682499767 := by
  unfold tailWord_1687975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61565506059762333023713379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41043670706508222015808919 61565506059762333023713379)
  ·
    refine ⟨92348259089643499535570069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61565506059762333023713379 92348259089643499535570069)
    ·
      refine ⟨4328824644827039040729847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92348259089643499535570069 4328824644827039040729847)
      ·
        refine ⟨6493236967240558561094771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328824644827039040729847 6493236967240558561094771)
        ·
          refine ⟨9739855450860837841642157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493236967240558561094771 9739855450860837841642157)
          ·
            refine ⟨3652445794072814190615809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9739855450860837841642157 3652445794072814190615809)
            ·
              refine ⟨2739334345554610642961857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652445794072814190615809 2739334345554610642961857)
              ·
                refine ⟨2054500759165957982221393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739334345554610642961857 2054500759165957982221393)
                ·
                  refine ⟨1540875569374468486666045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054500759165957982221393 1540875569374468486666045)
                  ·
                    refine ⟨577828338515425682499767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540875569374468486666045 577828338515425682499767)
                    ·
                      rfl

theorem cell22_1687975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1687975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687975 prefixEnd_1687975 := by exact prefixLift 1687975
  have htrace : WordTrace (prefixWord ++ tailWord_1687975) baseStart_1687975 baseEnd_1687975 := by
    simpa [prefixWord, tailWord_1687975, baseEnd_1687975] using wordTrace_append hprefix tailTrace_1687975
  have hstable : (prefixWord ++ tailWord_1687975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687975).length < 2 ^ (prefixWord ++ tailWord_1687975).sum := by decide
  have hdescent : baseEnd_1687975 < baseStart_1687975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687999 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 11]
def baseStart_1687999 : Nat := 118140960795 + 1687999 * 2 ^ 59
def prefixEnd_1687999 : Nat := 4983230072969 + 3 ^ 40 * 1687999 * 2
def baseEnd_1687999 : Nat := 192612184735299206633231

theorem tailTrace_1687999 : CollatzResearch.WordTrace tailWord_1687999 prefixEnd_1687999 192612184735299206633231 := by
  unfold tailWord_1687999
  simp only [CollatzResearch.WordTrace]
  refine ⟨61566381411675385122587051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41044254274450256748391367 61566381411675385122587051)
  ·
    refine ⟨92349572117513077683880577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61566381411675385122587051 92349572117513077683880577)
    ·
      refine ⟨69262179088134808262910433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92349572117513077683880577 69262179088134808262910433)
      ·
        refine ⟨51946634316101106197182825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69262179088134808262910433 51946634316101106197182825)
        ·
          refine ⟨38959975737075829647887119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51946634316101106197182825 38959975737075829647887119)
          ·
            refine ⟨58439963605613744471830679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38959975737075829647887119 58439963605613744471830679)
            ·
              refine ⟨87659945408420616707746019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58439963605613744471830679 87659945408420616707746019)
              ·
                refine ⟨131489918112630925061619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87659945408420616707746019 131489918112630925061619029)
                ·
                  refine ⟨192612184735299206633231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 131489918112630925061619029 192612184735299206633231)
                  ·
                    rfl

theorem cell22_1687999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_1687999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1687999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1687999 prefixEnd_1687999 := by exact prefixLift 1687999
  have htrace : WordTrace (prefixWord ++ tailWord_1687999) baseStart_1687999 baseEnd_1687999 := by
    simpa [prefixWord, tailWord_1687999, baseEnd_1687999] using wordTrace_append hprefix tailTrace_1687999
  have hstable : (prefixWord ++ tailWord_1687999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687999).length < 2 ^ (prefixWord ++ tailWord_1687999).sum := by decide
  have hdescent : baseEnd_1687999 < baseStart_1687999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688031 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1688031 : Nat := 118140960795 + 1688031 * 2 ^ 59
def prefixEnd_1688031 : Nat := 4983230072969 + 3 ^ 40 * 1688031 * 2
def baseEnd_1688031 : Nat := 577847508459860203099595

theorem tailTrace_1688031 : CollatzResearch.WordTrace tailWord_1688031 prefixEnd_1688031 577847508459860203099595 := by
  unfold tailWord_1688031
  simp only [CollatzResearch.WordTrace]
  refine ⟨61567548547559454587751947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41045032365039636391834631 61567548547559454587751947)
  ·
    refine ⟨92351322821339181881627921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61567548547559454587751947 92351322821339181881627921)
    ·
      refine ⟨69263492116004386411220941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92351322821339181881627921 69263492116004386411220941)
      ·
        refine ⟨25973809543501644904207853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69263492116004386411220941 25973809543501644904207853)
        ·
          refine ⟨9740178578813116839077945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25973809543501644904207853 9740178578813116839077945)
          ·
            refine ⟨7305133934109837629308459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740178578813116839077945 7305133934109837629308459)
            ·
              refine ⟨10957700901164756443962689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305133934109837629308459 10957700901164756443962689)
              ·
                refine ⟨8218275675873567332972017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10957700901164756443962689 8218275675873567332972017)
                ·
                  refine ⟨6163706756905175499729013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8218275675873567332972017 6163706756905175499729013)
                  ·
                    refine ⟨577847508459860203099595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6163706756905175499729013 577847508459860203099595)
                    ·
                      rfl

theorem cell22_1688031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1688031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688031 prefixEnd_1688031 := by exact prefixLift 1688031
  have htrace : WordTrace (prefixWord ++ tailWord_1688031) baseStart_1688031 baseEnd_1688031 := by
    simpa [prefixWord, tailWord_1688031, baseEnd_1688031] using wordTrace_append hprefix tailTrace_1688031
  have hstable : (prefixWord ++ tailWord_1688031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688031).length < 2 ^ (prefixWord ++ tailWord_1688031).sum := by decide
  have hdescent : baseEnd_1688031 < baseStart_1688031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688061 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1688061 : Nat := 118140960795 + 1688061 * 2 ^ 59
def prefixEnd_1688061 : Nat := 4983230072969 + 3 ^ 40 * 1688061 * 2
def baseEnd_1688061 : Nat := 192619259357650041616501

theorem tailTrace_1688061 : CollatzResearch.WordTrace tailWord_1688061 prefixEnd_1688061 192619259357650041616501 := by
  unfold tailWord_1688061
  simp only [CollatzResearch.WordTrace]
  refine ⟨61568642737450769711344037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41045761824967179807562691 61568642737450769711344037)
  ·
    refine ⟨11544120513272019320877007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61568642737450769711344037 11544120513272019320877007)
    ·
      refine ⟨17316180769908028981315511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544120513272019320877007 17316180769908028981315511)
      ·
        refine ⟨25974271154862043471973267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316180769908028981315511 25974271154862043471973267)
        ·
          refine ⟨38961406732293065207959901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25974271154862043471973267 38961406732293065207959901)
          ·
            refine ⟨14610527524609899452984963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38961406732293065207959901 14610527524609899452984963)
            ·
              refine ⟨21915791286914849179477445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14610527524609899452984963 21915791286914849179477445)
              ·
                refine ⟨4109210866296534221152021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21915791286914849179477445 4109210866296534221152021)
                ·
                  refine ⟨192619259357650041616501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4109210866296534221152021 192619259357650041616501)
                  ·
                    rfl

theorem cell22_1688061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1688061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688061 prefixEnd_1688061 := by exact prefixLift 1688061
  have htrace : WordTrace (prefixWord ++ tailWord_1688061) baseStart_1688061 baseEnd_1688061 := by
    simpa [prefixWord, tailWord_1688061, baseEnd_1688061] using wordTrace_append hprefix tailTrace_1688061
  have hstable : (prefixWord ++ tailWord_1688061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688061).length < 2 ^ (prefixWord ++ tailWord_1688061).sum := by decide
  have hdescent : baseEnd_1688061 < baseStart_1688061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688063 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 1, 4]
def baseStart_1688063 : Nat := 118140960795 + 1688063 * 2 ^ 59
def prefixEnd_1688063 : Nat := 4983230072969 + 3 ^ 40 * 1688063 * 2
def baseEnd_1688063 : Nat := 577858462713822786299497

theorem tailTrace_1688063 : CollatzResearch.WordTrace tailWord_1688063 prefixEnd_1688063 577858462713822786299497 := by
  unfold tailWord_1688063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61568715683443524052916843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41045810455629016035277895 61568715683443524052916843)
  ·
    refine ⟨92353073525165286079375265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61568715683443524052916843 92353073525165286079375265)
    ·
      refine ⟨69264805143873964559531449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92353073525165286079375265 69264805143873964559531449)
      ·
        refine ⟨51948603857905473419648587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69264805143873964559531449 51948603857905473419648587)
        ·
          refine ⟨77922905786858210129472881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51948603857905473419648587 77922905786858210129472881)
          ·
            refine ⟨58442179340143657597104661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77922905786858210129472881 58442179340143657597104661)
            ·
              refine ⟨2739477156569233949864281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58442179340143657597104661 2739477156569233949864281)
              ·
                refine ⟨2054607867426925462398211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739477156569233949864281 2054607867426925462398211)
                ·
                  refine ⟨3081911801140388193597317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054607867426925462398211 3081911801140388193597317)
                  ·
                    refine ⟨577858462713822786299497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081911801140388193597317 577858462713822786299497)
                    ·
                      rfl

theorem cell22_1688063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_1688063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688063 prefixEnd_1688063 := by exact prefixLift 1688063
  have htrace : WordTrace (prefixWord ++ tailWord_1688063) baseStart_1688063 baseEnd_1688063 := by
    simpa [prefixWord, tailWord_1688063, baseEnd_1688063] using wordTrace_append hprefix tailTrace_1688063
  have hstable : (prefixWord ++ tailWord_1688063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688063).length < 2 ^ (prefixWord ++ tailWord_1688063).sum := by decide
  have hdescent : baseEnd_1688063 < baseStart_1688063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688125 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1688125 : Nat := 118140960795 + 1688125 * 2 ^ 59
def prefixEnd_1688125 : Nat := 4983230072969 + 3 ^ 40 * 1688125 * 2
def baseEnd_1688125 : Nat := 577879686580875291249307

theorem tailTrace_1688125 : CollatzResearch.WordTrace tailWord_1688125 prefixEnd_1688125 577879686580875291249307 := by
  unfold tailWord_1688125
  simp only [CollatzResearch.WordTrace]
  refine ⟨61570977009218908641673829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41047318006145939094449219 61570977009218908641673829)
  ·
    refine ⟨11544558189228545370313843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61570977009218908641673829 11544558189228545370313843)
    ·
      refine ⟨17316837283842818055470765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544558189228545370313843 17316837283842818055470765)
      ·
        refine ⟨6493813981441056770801537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17316837283842818055470765 6493813981441056770801537)
        ·
          refine ⟨4870360486080792578101153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6493813981441056770801537 4870360486080792578101153)
          ·
            refine ⟨3652770364560594433575865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870360486080792578101153 3652770364560594433575865)
            ·
              refine ⟨2739577773420445825181899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652770364560594433575865 2739577773420445825181899)
              ·
                refine ⟨4109366660130668737772849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739577773420445825181899 4109366660130668737772849)
                ·
                  refine ⟨3082024995098001553329637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109366660130668737772849 3082024995098001553329637)
                  ·
                    refine ⟨577879686580875291249307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082024995098001553329637 577879686580875291249307)
                    ·
                      rfl

theorem cell22_1688125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1688125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688125 prefixEnd_1688125 := by exact prefixLift 1688125
  have htrace : WordTrace (prefixWord ++ tailWord_1688125) baseStart_1688125 baseEnd_1688125 := by
    simpa [prefixWord, tailWord_1688125, baseEnd_1688125] using wordTrace_append hprefix tailTrace_1688125
  have hstable : (prefixWord ++ tailWord_1688125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688125).length < 2 ^ (prefixWord ++ tailWord_1688125).sum := by decide
  have hdescent : baseEnd_1688125 < baseStart_1688125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688136 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1688136 : Nat := 118140960795 + 1688136 * 2 ^ 59
def prefixEnd_1688136 : Nat := 4983230072969 + 3 ^ 40 * 1688136 * 2
def baseEnd_1688136 : Nat := 577883452105674929224273

theorem tailTrace_1688136 : CollatzResearch.WordTrace tailWord_1688136 prefixEnd_1688136 577883452105674929224273 := by
  unfold tailWord_1688136
  simp only [CollatzResearch.WordTrace]
  refine ⟨30785689106089528760162131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41047585474786038346882841 30785689106089528760162131)
  ·
    refine ⟨46178533659134293140243197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30785689106089528760162131 46178533659134293140243197)
    ·
      refine ⟨17316950122175359927591199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46178533659134293140243197 17316950122175359927591199)
      ·
        refine ⟨25975425183263039891386799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316950122175359927591199 25975425183263039891386799)
        ·
          refine ⟨38963137774894559837080199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975425183263039891386799 38963137774894559837080199)
          ·
            refine ⟨58444706662341839755620299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38963137774894559837080199 58444706662341839755620299)
            ·
              refine ⟨87667059993512759633430449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58444706662341839755620299 87667059993512759633430449)
              ·
                refine ⟨65750294995134569725072837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87667059993512759633430449 65750294995134569725072837)
                ·
                  refine ⟨12328180311587731823451157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65750294995134569725072837 12328180311587731823451157)
                  ·
                    refine ⟨577883452105674929224273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12328180311587731823451157 577883452105674929224273)
                    ·
                      rfl

theorem cell22_1688136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1688136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688136 prefixEnd_1688136 := by exact prefixLift 1688136
  have htrace : WordTrace (prefixWord ++ tailWord_1688136) baseStart_1688136 baseEnd_1688136 := by
    simpa [prefixWord, tailWord_1688136, baseEnd_1688136] using wordTrace_append hprefix tailTrace_1688136
  have hstable : (prefixWord ++ tailWord_1688136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688136).length < 2 ^ (prefixWord ++ tailWord_1688136).sum := by decide
  have hdescent : baseEnd_1688136 < baseStart_1688136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688189 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_1688189 : Nat := 118140960795 + 1688189 * 2 ^ 59
def prefixEnd_1688189 : Nat := 4983230072969 + 3 ^ 40 * 1688189 * 2
def baseEnd_1688189 : Nat := 577901595088800457649111

theorem tailTrace_1688189 : CollatzResearch.WordTrace tailWord_1688189 prefixEnd_1688189 577901595088800457649111 := by
  unfold tailWord_1688189
  simp only [CollatzResearch.WordTrace]
  refine ⟨61573311280987047572003621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41048874187324698381335747 61573311280987047572003621)
  ·
    refine ⟨11544995865185071419750679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61573311280987047572003621 11544995865185071419750679)
    ·
      refine ⟨17317493797777607129626019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544995865185071419750679 17317493797777607129626019)
      ·
        refine ⟨25976240696666410694439029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317493797777607129626019 25976240696666410694439029)
        ·
          refine ⟨2435272565312476002603659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25976240696666410694439029 2435272565312476002603659)
          ·
            refine ⟨3652908847968714003905489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435272565312476002603659 3652908847968714003905489)
            ·
              refine ⟨2739681635976535502929117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652908847968714003905489 2739681635976535502929117)
              ·
                refine ⟨1027380613491200813598419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2739681635976535502929117 1027380613491200813598419)
                ·
                  refine ⟨1541070920236801220397629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027380613491200813598419 1541070920236801220397629)
                  ·
                    refine ⟨577901595088800457649111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541070920236801220397629 577901595088800457649111)
                    ·
                      rfl

theorem cell22_1688189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_1688189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688189 prefixEnd_1688189 := by exact prefixLift 1688189
  have htrace : WordTrace (prefixWord ++ tailWord_1688189) baseStart_1688189 baseEnd_1688189 := by
    simpa [prefixWord, tailWord_1688189, baseEnd_1688189] using wordTrace_append hprefix tailTrace_1688189
  have hstable : (prefixWord ++ tailWord_1688189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688189).length < 2 ^ (prefixWord ++ tailWord_1688189).sum := by decide
  have hdescent : baseEnd_1688189 < baseStart_1688189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688202 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_1688202 : Nat := 118140960795 + 1688202 * 2 ^ 59
def prefixEnd_1688202 : Nat := 4983230072969 + 3 ^ 40 * 1688202 * 2
def baseEnd_1688202 : Nat := 192635348418157585691357

theorem tailTrace_1688202 : CollatzResearch.WordTrace tailWord_1688202 prefixEnd_1688202 192635348418157585691357 := by
  unfold tailWord_1688202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393446357484987698056715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41049190286626633861484573 15393446357484987698056715)
  ·
    refine ⟨23090169536227481547085073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15393446357484987698056715 23090169536227481547085073)
    ·
      refine ⟨17317627152170611160313805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23090169536227481547085073 17317627152170611160313805)
      ·
        refine ⟨6494110182063979185117677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17317627152170611160313805 6494110182063979185117677)
        ·
          refine ⟨2435291318273992194419129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6494110182063979185117677 2435291318273992194419129)
          ·
            refine ⟨1826468488705494145814347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435291318273992194419129 1826468488705494145814347)
            ·
              refine ⟨2739702733058241218721521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826468488705494145814347 2739702733058241218721521)
              ·
                refine ⟨2054777049793680914041141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739702733058241218721521 2054777049793680914041141)
                ·
                  refine ⟨192635348418157585691357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2054777049793680914041141 192635348418157585691357)
                  ·
                    rfl

theorem cell22_1688202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_1688202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688202 prefixEnd_1688202 := by exact prefixLift 1688202
  have htrace : WordTrace (prefixWord ++ tailWord_1688202) baseStart_1688202 baseEnd_1688202 := by
    simpa [prefixWord, tailWord_1688202, baseEnd_1688202] using wordTrace_append hprefix tailTrace_1688202
  have hstable : (prefixWord ++ tailWord_1688202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688202).length < 2 ^ (prefixWord ++ tailWord_1688202).sum := by decide
  have hdescent : baseEnd_1688202 < baseStart_1688202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688243 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_1688243 : Nat := 118140960795 + 1688243 * 2 ^ 59
def prefixEnd_1688243 : Nat := 4983230072969 + 3 ^ 40 * 1688243 * 2
def baseEnd_1688243 : Nat := 577920080392362316798945

theorem tailTrace_1688243 : CollatzResearch.WordTrace tailWord_1688243 prefixEnd_1688243 577920080392362316798945 := by
  unfold tailWord_1688243
  simp only [CollatzResearch.WordTrace]
  refine ⟨61575280822791414794469383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41050187215194276529646255 61575280822791414794469383)
  ·
    refine ⟨92362921234187122191704075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61575280822791414794469383 92362921234187122191704075)
    ·
      refine ⟨138544381851280683287556113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92362921234187122191704075 138544381851280683287556113)
      ·
        refine ⟨103908286388460512465667085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138544381851280683287556113 103908286388460512465667085)
        ·
          refine ⟨38965607395672692174625157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103908286388460512465667085 38965607395672692174625157)
          ·
            refine ⟨7306051386688629782742217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38965607395672692174625157 7306051386688629782742217)
            ·
              refine ⟨5479538540016472337056663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7306051386688629782742217 5479538540016472337056663)
              ·
                refine ⟨8219307810024708505584995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479538540016472337056663 8219307810024708505584995)
                ·
                  refine ⟨12328961715037062758377493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219307810024708505584995 12328961715037062758377493)
                  ·
                    refine ⟨577920080392362316798945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12328961715037062758377493 577920080392362316798945)
                    ·
                      rfl

theorem cell22_1688243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_1688243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688243 prefixEnd_1688243 := by exact prefixLift 1688243
  have htrace : WordTrace (prefixWord ++ tailWord_1688243) baseStart_1688243 baseEnd_1688243 := by
    simpa [prefixWord, tailWord_1688243, baseEnd_1688243] using wordTrace_append hprefix tailTrace_1688243
  have hstable : (prefixWord ++ tailWord_1688243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688243).length < 2 ^ (prefixWord ++ tailWord_1688243).sum := by decide
  have hdescent : baseEnd_1688243 < baseStart_1688243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688260 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1688260 : Nat := 118140960795 + 1688260 * 2 ^ 59
def prefixEnd_1688260 : Nat := 4983230072969 + 3 ^ 40 * 1688260 * 2
def baseEnd_1688260 : Nat := 577925899839779939123893

theorem tailTrace_1688260 : CollatzResearch.WordTrace tailWord_1688260 prefixEnd_1688260 577925899839779939123893 := by
  unfold tailWord_1688260
  simp only [CollatzResearch.WordTrace]
  refine ⟨30787950431864913348919117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41050600575819884465225489 30787950431864913348919117)
  ·
    refine ⟨11545481411949342505844669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30787950431864913348919117 11545481411949342505844669)
    ·
      refine ⟨4329555529481003439691751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11545481411949342505844669 4329555529481003439691751)
      ·
        refine ⟨6494333294221505159537627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329555529481003439691751 6494333294221505159537627)
        ·
          refine ⟨9741499941332257739306441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494333294221505159537627 9741499941332257739306441)
          ·
            refine ⟨7306124955999193304479831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9741499941332257739306441 7306124955999193304479831)
            ·
              refine ⟨10959187433998789956719747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306124955999193304479831 10959187433998789956719747)
              ·
                refine ⟨16438781150998184935079621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959187433998789956719747 16438781150998184935079621)
                ·
                  refine ⟨3082271465812159675327429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16438781150998184935079621 3082271465812159675327429)
                  ·
                    refine ⟨577925899839779939123893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082271465812159675327429 577925899839779939123893)
                    ·
                      rfl

theorem cell22_1688260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1688260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688260 prefixEnd_1688260 := by exact prefixLift 1688260
  have htrace : WordTrace (prefixWord ++ tailWord_1688260) baseStart_1688260 baseEnd_1688260 := by
    simpa [prefixWord, tailWord_1688260, baseEnd_1688260] using wordTrace_append hprefix tailTrace_1688260
  have hstable : (prefixWord ++ tailWord_1688260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688260).length < 2 ^ (prefixWord ++ tailWord_1688260).sum := by decide
  have hdescent : baseEnd_1688260 < baseStart_1688260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688279 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 2, 3]
def baseStart_1688279 : Nat := 118140960795 + 1688279 * 2 ^ 59
def prefixEnd_1688279 : Nat := 4983230072969 + 3 ^ 40 * 1688279 * 2
def baseEnd_1688279 : Nat := 577932403928070222898835

theorem tailTrace_1688279 : CollatzResearch.WordTrace tailWord_1688279 prefixEnd_1688279 577932403928070222898835 := by
  unfold tailWord_1688279
  simp only [CollatzResearch.WordTrace]
  refine ⟨61576593850660992942779891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41051062567107328628519927 61576593850660992942779891)
  ·
    refine ⟨92364890775991489414169837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61576593850660992942779891 92364890775991489414169837)
    ·
      refine ⟨34636834040996808530313689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92364890775991489414169837 34636834040996808530313689)
      ·
        refine ⟨25977625530747606397735267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34636834040996808530313689 25977625530747606397735267)
        ·
          refine ⟨38966438296121409596602901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25977625530747606397735267 38966438296121409596602901)
          ·
            refine ⟨1826551795130691074840761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38966438296121409596602901 1826551795130691074840761)
            ·
              refine ⟨1369913846348018306130571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826551795130691074840761 1369913846348018306130571)
              ·
                refine ⟨2054870769522027459195857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369913846348018306130571 2054870769522027459195857)
                ·
                  refine ⟨1541153077141520594396893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054870769522027459195857 1541153077141520594396893)
                  ·
                    refine ⟨577932403928070222898835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541153077141520594396893 577932403928070222898835)
                    ·
                      rfl

theorem cell22_1688279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_1688279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688279 prefixEnd_1688279 := by exact prefixLift 1688279
  have htrace : WordTrace (prefixWord ++ tailWord_1688279) baseStart_1688279 baseEnd_1688279 := by
    simpa [prefixWord, tailWord_1688279, baseEnd_1688279] using wordTrace_append hprefix tailTrace_1688279
  have hstable : (prefixWord ++ tailWord_1688279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688279).length < 2 ^ (prefixWord ++ tailWord_1688279).sum := by decide
  have hdescent : baseEnd_1688279 < baseStart_1688279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688307 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 1, 3]
def baseStart_1688307 : Nat := 118140960795 + 1688307 * 2 ^ 59
def prefixEnd_1688307 : Nat := 4983230072969 + 3 ^ 40 * 1688307 * 2
def baseEnd_1688307 : Nat := 577941988900287483198749

theorem tailTrace_1688307 : CollatzResearch.WordTrace tailWord_1688307 prefixEnd_1688307 577941988900287483198749 := by
  unfold tailWord_1688307
  simp only [CollatzResearch.WordTrace]
  refine ⟨61577615094559553724799175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41051743396373035816532783 61577615094559553724799175)
  ·
    refine ⟨92366422641839330587198763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61577615094559553724799175 92366422641839330587198763)
    ·
      refine ⟨138549633962758995880798145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92366422641839330587198763 138549633962758995880798145)
      ·
        refine ⟨103912225472069246910598609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138549633962758995880798145 103912225472069246910598609)
        ·
          refine ⟨77934169104051935182948957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103912225472069246910598609 77934169104051935182948957)
          ·
            refine ⟨29225313414019475693605859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77934169104051935182948957 29225313414019475693605859)
            ·
              refine ⟨43837970121029213540408789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29225313414019475693605859 43837970121029213540408789)
              ·
                refine ⟨1027452424711622192353331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43837970121029213540408789 1027452424711622192353331)
                ·
                  refine ⟨1541178637067433288529997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027452424711622192353331 1541178637067433288529997)
                  ·
                    refine ⟨577941988900287483198749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541178637067433288529997 577941988900287483198749)
                    ·
                      rfl

theorem cell22_1688307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 3].length) (baseStart_1688307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688307 prefixEnd_1688307 := by exact prefixLift 1688307
  have htrace : WordTrace (prefixWord ++ tailWord_1688307) baseStart_1688307 baseEnd_1688307 := by
    simpa [prefixWord, tailWord_1688307, baseEnd_1688307] using wordTrace_append hprefix tailTrace_1688307
  have hstable : (prefixWord ++ tailWord_1688307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688307).length < 2 ^ (prefixWord ++ tailWord_1688307).sum := by decide
  have hdescent : baseEnd_1688307 < baseStart_1688307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688309 : List Nat := [1, 3, 6, 1, 2, 9]
def baseStart_1688309 : Nat := 118140960795 + 1688309 * 2 ^ 59
def prefixEnd_1688309 : Nat := 4983230072969 + 3 ^ 40 * 1688309 * 2
def baseEnd_1688309 : Nat := 7135094735076051168503

theorem tailTrace_1688309 : CollatzResearch.WordTrace tailWord_1688309 prefixEnd_1688309 7135094735076051168503 := by
  unfold tailWord_1688309
  simp only [CollatzResearch.WordTrace]
  refine ⟨61577688040552308066371981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41051792027034872044247987 61577688040552308066371981)
  ·
    refine ⟨23091633015207115524889493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61577688040552308066371981 23091633015207115524889493)
    ·
      refine ⟨1082420297587833540229195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23091633015207115524889493 1082420297587833540229195)
      ·
        refine ⟨1623630446381750310343793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082420297587833540229195 1623630446381750310343793)
        ·
          refine ⟨1217722834786312732757845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623630446381750310343793 1217722834786312732757845)
          ·
            refine ⟨7135094735076051168503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1217722834786312732757845 7135094735076051168503)
            ·
              rfl

theorem cell22_1688309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 9].length) (baseStart_1688309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688309 prefixEnd_1688309 := by exact prefixLift 1688309
  have htrace : WordTrace (prefixWord ++ tailWord_1688309) baseStart_1688309 baseEnd_1688309 := by
    simpa [prefixWord, tailWord_1688309, baseEnd_1688309] using wordTrace_append hprefix tailTrace_1688309
  have hstable : (prefixWord ++ tailWord_1688309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688309).length < 2 ^ (prefixWord ++ tailWord_1688309).sum := by decide
  have hdescent : baseEnd_1688309 < baseStart_1688309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688324 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1688324 : Nat := 118140960795 + 1688324 * 2 ^ 59
def prefixEnd_1688324 : Nat := 4983230072969 + 3 ^ 40 * 1688324 * 2
def baseEnd_1688324 : Nat := 577947808347705105523697

theorem tailTrace_1688324 : CollatzResearch.WordTrace tailWord_1688324 prefixEnd_1688324 577947808347705105523697 := by
  unfold tailWord_1688324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30789117567748982814084013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41052156756998643752112017 30789117567748982814084013)
  ·
    refine ⟨11545919087905868555281505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30789117567748982814084013 11545919087905868555281505)
    ·
      refine ⟨8659439315929401416461129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11545919087905868555281505 8659439315929401416461129)
      ·
        refine ⟨6494579486947051062345847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8659439315929401416461129 6494579486947051062345847)
        ·
          refine ⟨9741869230420576593518771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494579486947051062345847 9741869230420576593518771)
          ·
            refine ⟨14612803845630864890278157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9741869230420576593518771 14612803845630864890278157)
            ·
              refine ⟨5479801442111574333854309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14612803845630864890278157 5479801442111574333854309)
              ·
                refine ⟨1027462770395920187597683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5479801442111574333854309 1027462770395920187597683)
                ·
                  refine ⟨1541194155593880281396525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027462770395920187597683 1541194155593880281396525)
                  ·
                    refine ⟨577947808347705105523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541194155593880281396525 577947808347705105523697)
                    ·
                      rfl

theorem cell22_1688324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1688324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688324 prefixEnd_1688324 := by exact prefixLift 1688324
  have htrace : WordTrace (prefixWord ++ tailWord_1688324) baseStart_1688324 baseEnd_1688324 := by
    simpa [prefixWord, tailWord_1688324, baseEnd_1688324] using wordTrace_append hprefix tailTrace_1688324
  have hstable : (prefixWord ++ tailWord_1688324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688324).length < 2 ^ (prefixWord ++ tailWord_1688324).sum := by decide
  have hdescent : baseEnd_1688324 < baseStart_1688324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688410 : List Nat := [3, 1, 1, 2, 1, 5, 1, 8]
def baseStart_1688410 : Nat := 118140960795 + 1688410 * 2 ^ 59
def prefixEnd_1688410 : Nat := 4983230072969 + 3 ^ 40 * 1688410 * 2
def baseEnd_1688410 : Nat := 64219694211692171985937

theorem tailTrace_1688410 : CollatzResearch.WordTrace tailWord_1688410 prefixEnd_1688410 64219694211692171985937 := by
  unfold tailWord_1688410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395342953296600578949671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41054247875457601543865789 15395342953296600578949671)
  ·
    refine ⟨23093014429944900868424507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15395342953296600578949671 23093014429944900868424507)
    ·
      refine ⟨34639521644917351302636761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23093014429944900868424507 34639521644917351302636761)
      ·
        refine ⟨25979641233688013476977571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34639521644917351302636761 25979641233688013476977571)
        ·
          refine ⟨38969461850532020215466357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25979641233688013476977571 38969461850532020215466357)
          ·
            refine ⟨3653387048487376895199971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38969461850532020215466357 3653387048487376895199971)
            ·
              refine ⟨5480080572731065342799957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653387048487376895199971 5480080572731065342799957)
              ·
                refine ⟨64219694211692171985937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5480080572731065342799957 64219694211692171985937)
                ·
                  rfl

theorem cell22_1688410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_1688410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688410 prefixEnd_1688410 := by exact prefixLift 1688410
  have htrace : WordTrace (prefixWord ++ tailWord_1688410) baseStart_1688410 baseEnd_1688410 := by
    simpa [prefixWord, tailWord_1688410, baseEnd_1688410] using wordTrace_append hprefix tailTrace_1688410
  have hstable : (prefixWord ++ tailWord_1688410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688410).length < 2 ^ (prefixWord ++ tailWord_1688410).sum := by decide
  have hdescent : baseEnd_1688410 < baseStart_1688410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688412 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1688412 : Nat := 118140960795 + 1688412 * 2 ^ 59
def prefixEnd_1688412 : Nat := 4983230072969 + 3 ^ 40 * 1688412 * 2
def baseEnd_1688412 : Nat := 577977932546102209323427

theorem tailTrace_1688412 : CollatzResearch.WordTrace tailWord_1688412 prefixEnd_1688412 577977932546102209323427 := by
  unfold tailWord_1688412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30790722379589578328685745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41054296506119437771580993 30790722379589578328685745)
  ·
    refine ⟨23093041784692183746514309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30790722379589578328685745 23093041784692183746514309)
    ·
      refine ⟨4329945334629784452471433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23093041784692183746514309 4329945334629784452471433)
      ·
        refine ⟨3247459000972338339353575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4329945334629784452471433 3247459000972338339353575)
        ·
          refine ⟨4871188501458507509030363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247459000972338339353575 4871188501458507509030363)
          ·
            refine ⟨7306782752187761263545545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871188501458507509030363 7306782752187761263545545)
            ·
              refine ⟨5480087064140820947659159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7306782752187761263545545 5480087064140820947659159)
              ·
                refine ⟨8220130596211231421488739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480087064140820947659159 8220130596211231421488739)
                ·
                  refine ⟨12330195894316847132233109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8220130596211231421488739 12330195894316847132233109)
                  ·
                    refine ⟨577977932546102209323427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12330195894316847132233109 577977932546102209323427)
                    ·
                      rfl

theorem cell22_1688412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1688412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688412 prefixEnd_1688412 := by exact prefixLift 1688412
  have htrace : WordTrace (prefixWord ++ tailWord_1688412) baseStart_1688412 baseEnd_1688412 := by
    simpa [prefixWord, tailWord_1688412, baseEnd_1688412] using wordTrace_append hprefix tailTrace_1688412
  have hstable : (prefixWord ++ tailWord_1688412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688412).length < 2 ^ (prefixWord ++ tailWord_1688412).sum := by decide
  have hdescent : baseEnd_1688412 < baseStart_1688412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688515 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_1688515 : Nat := 118140960795 + 1688515 * 2 ^ 59
def prefixEnd_1688515 : Nat := 4983230072969 + 3 ^ 40 * 1688515 * 2
def baseEnd_1688515 : Nat := 578013191551044273998111

theorem tailTrace_1688515 : CollatzResearch.WordTrace tailWord_1688515 prefixEnd_1688515 578013191551044273998111 := by
  unfold tailWord_1688515
  simp only [CollatzResearch.WordTrace]
  refine ⟨61585201477806005248370999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41056800985204003498913999 61585201477806005248370999)
  ·
    refine ⟨92377802216709007872556499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61585201477806005248370999 92377802216709007872556499)
    ·
      refine ⟨138566703325063511808834749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92377802216709007872556499 138566703325063511808834749)
      ·
        refine ⟨51962513746898816928313031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138566703325063511808834749 51962513746898816928313031)
        ·
          refine ⟨77943770620348225392469547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51962513746898816928313031 77943770620348225392469547)
          ·
            refine ⟨116915655930522338088704321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77943770620348225392469547 116915655930522338088704321)
            ·
              refine ⟨87686741947891753566528241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116915655930522338088704321 87686741947891753566528241)
              ·
                refine ⟨65765056460918815174896181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87686741947891753566528241 65765056460918815174896181)
                ·
                  refine ⟨6165474043211138922646517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65765056460918815174896181 6165474043211138922646517)
                  ·
                    refine ⟨578013191551044273998111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6165474043211138922646517 578013191551044273998111)
                    ·
                      rfl

theorem cell22_1688515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_1688515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688515 prefixEnd_1688515 := by exact prefixLift 1688515
  have htrace : WordTrace (prefixWord ++ tailWord_1688515) baseStart_1688515 baseEnd_1688515 := by
    simpa [prefixWord, tailWord_1688515, baseEnd_1688515] using wordTrace_append hprefix tailTrace_1688515
  have hstable : (prefixWord ++ tailWord_1688515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688515).length < 2 ^ (prefixWord ++ tailWord_1688515).sum := by decide
  have hdescent : baseEnd_1688515 < baseStart_1688515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688536 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_1688536 : Nat := 118140960795 + 1688536 * 2 ^ 59
def prefixEnd_1688536 : Nat := 4983230072969 + 3 ^ 40 * 1688536 * 2
def baseEnd_1688536 : Nat := 578020380280207219223047

theorem tailTrace_1688536 : CollatzResearch.WordTrace tailWord_1688536 prefixEnd_1688536 578020380280207219223047 := by
  unfold tailWord_1688536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30792983705364962917442731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41057311607153283889923641 30792983705364962917442731)
  ·
    refine ⟨46189475558047444376164097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30792983705364962917442731 46189475558047444376164097)
    ·
      refine ⟨34642106668535583282123073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46189475558047444376164097 34642106668535583282123073)
      ·
        refine ⟨25981580001401687461592305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34642106668535583282123073 25981580001401687461592305)
        ·
          refine ⟨19486185001051265596194229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25981580001401687461592305 19486185001051265596194229)
          ·
            refine ⟨1826829843848556149643209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19486185001051265596194229 1826829843848556149643209)
            ·
              refine ⟨1370122382886417112232407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826829843848556149643209 1370122382886417112232407)
              ·
                refine ⟨2055183574329625668348611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370122382886417112232407 2055183574329625668348611)
                ·
                  refine ⟨3082775361494438502522917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055183574329625668348611 3082775361494438502522917)
                  ·
                    refine ⟨578020380280207219223047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082775361494438502522917 578020380280207219223047)
                    ·
                      rfl

theorem cell22_1688536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_1688536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688536 prefixEnd_1688536 := by exact prefixLift 1688536
  have htrace : WordTrace (prefixWord ++ tailWord_1688536) baseStart_1688536 baseEnd_1688536 := by
    simpa [prefixWord, tailWord_1688536, baseEnd_1688536] using wordTrace_append hprefix tailTrace_1688536
  have hstable : (prefixWord ++ tailWord_1688536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688536).length < 2 ^ (prefixWord ++ tailWord_1688536).sum := by decide
  have hdescent : baseEnd_1688536 < baseStart_1688536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688547 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_1688547 : Nat := 118140960795 + 1688547 * 2 ^ 59
def prefixEnd_1688547 : Nat := 4983230072969 + 3 ^ 40 * 1688547 * 2
def baseEnd_1688547 : Nat := 578024145805006857198013

theorem tailTrace_1688547 : CollatzResearch.WordTrace tailWord_1688547 prefixEnd_1688547 578024145805006857198013 := by
  unfold tailWord_1688547
  simp only [CollatzResearch.WordTrace]
  refine ⟨61586368613690074713535895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41057579075793383142357263 61586368613690074713535895)
  ·
    refine ⟨92379552920535112070303843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61586368613690074713535895 92379552920535112070303843)
    ·
      refine ⟨138569329380802668105455765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92379552920535112070303843 138569329380802668105455765)
      ·
        refine ⟨6495437314725125067443239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138569329380802668105455765 6495437314725125067443239)
        ·
          refine ⟨9743155972087687601164859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495437314725125067443239 9743155972087687601164859)
          ·
            refine ⟨14614733958131531401747289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743155972087687601164859 14614733958131531401747289)
            ·
              refine ⟨10961050468598648551310467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14614733958131531401747289 10961050468598648551310467)
              ·
                refine ⟨16441575702897972826965701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961050468598648551310467 16441575702897972826965701)
                ·
                  refine ⟨3082795444293369905056069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16441575702897972826965701 3082795444293369905056069)
                  ·
                    refine ⟨578024145805006857198013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082795444293369905056069 578024145805006857198013)
                    ·
                      rfl

theorem cell22_1688547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_1688547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688547 prefixEnd_1688547 := by exact prefixLift 1688547
  have htrace : WordTrace (prefixWord ++ tailWord_1688547) baseStart_1688547 baseEnd_1688547 := by
    simpa [prefixWord, tailWord_1688547, baseEnd_1688547] using wordTrace_append hprefix tailTrace_1688547
  have hstable : (prefixWord ++ tailWord_1688547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688547).length < 2 ^ (prefixWord ++ tailWord_1688547).sum := by decide
  have hdescent : baseEnd_1688547 < baseStart_1688547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688566 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1688566 : Nat := 118140960795 + 1688566 * 2 ^ 59
def prefixEnd_1688566 : Nat := 4983230072969 + 3 ^ 40 * 1688566 * 2
def baseEnd_1688566 : Nat := 578030649893297140972955

theorem tailTrace_1688566 : CollatzResearch.WordTrace tailWord_1688566 prefixEnd_1688566 578030649893297140972955 := by
  unfold tailWord_1688566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849191350038827559904847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41058041067080827305651701 3849191350038827559904847)
  ·
    refine ⟨5773787025058241339857271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849191350038827559904847 5773787025058241339857271)
    ·
      refine ⟨8660680537587362009785907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773787025058241339857271 8660680537587362009785907)
      ·
        refine ⟨12991020806381043014678861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8660680537587362009785907 12991020806381043014678861)
        ·
          refine ⟨4871632802392891130504573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12991020806381043014678861 4871632802392891130504573)
          ·
            refine ⟨1826862300897334173939215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4871632802392891130504573 1826862300897334173939215)
            ·
              refine ⟨2740293451346001260908823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826862300897334173939215 2740293451346001260908823)
              ·
                refine ⟨4110440177019001891363235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740293451346001260908823 4110440177019001891363235)
                ·
                  refine ⟨6165660265528502837044853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110440177019001891363235 6165660265528502837044853)
                  ·
                    refine ⟨578030649893297140972955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6165660265528502837044853 578030649893297140972955)
                    ·
                      rfl

theorem cell22_1688566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1688566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688566 prefixEnd_1688566 := by exact prefixLift 1688566
  have htrace : WordTrace (prefixWord ++ tailWord_1688566) baseStart_1688566 baseEnd_1688566 := by
    simpa [prefixWord, tailWord_1688566, baseEnd_1688566] using wordTrace_append hprefix tailTrace_1688566
  have hstable : (prefixWord ++ tailWord_1688566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688566).length < 2 ^ (prefixWord ++ tailWord_1688566).sum := by decide
  have hdescent : baseEnd_1688566 < baseStart_1688566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688607 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 7]
def baseStart_1688607 : Nat := 118140960795 + 1688607 * 2 ^ 59
def prefixEnd_1688607 : Nat := 4983230072969 + 3 ^ 40 * 1688607 * 2
def baseEnd_1688607 : Nat := 192681561677062233565943

theorem tailTrace_1688607 : CollatzResearch.WordTrace tailWord_1688607 prefixEnd_1688607 192681561677062233565943 := by
  unfold tailWord_1688607
  simp only [CollatzResearch.WordTrace]
  refine ⟨61588556993472704960720075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41059037995648469973813383 61588556993472704960720075)
  ·
    refine ⟨92382835490209057441080113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61588556993472704960720075 92382835490209057441080113)
    ·
      refine ⟨69287126617656793080810085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92382835490209057441080113 69287126617656793080810085)
      ·
        refine ⟨12991336240810648702651891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69287126617656793080810085 12991336240810648702651891)
        ·
          refine ⟨19487004361215973053977837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12991336240810648702651891 19487004361215973053977837)
          ·
            refine ⟨7307626635455989895241689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19487004361215973053977837 7307626635455989895241689)
            ·
              refine ⟨5480719976591992421431267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307626635455989895241689 5480719976591992421431267)
              ·
                refine ⟨8221079964887988632146901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480719976591992421431267 8221079964887988632146901)
                ·
                  refine ⟨192681561677062233565943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8221079964887988632146901 192681561677062233565943)
                  ·
                    rfl

theorem cell22_1688607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_1688607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688607 prefixEnd_1688607 := by exact prefixLift 1688607
  have htrace : WordTrace (prefixWord ++ tailWord_1688607) baseStart_1688607 baseEnd_1688607 := by
    simpa [prefixWord, tailWord_1688607, baseEnd_1688607] using wordTrace_append hprefix tailTrace_1688607
  have hstable : (prefixWord ++ tailWord_1688607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688607).length < 2 ^ (prefixWord ++ tailWord_1688607).sum := by decide
  have hdescent : baseEnd_1688607 < baseStart_1688607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688611 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 3, 3]
def baseStart_1688611 : Nat := 118140960795 + 1688611 * 2 ^ 59
def prefixEnd_1688611 : Nat := 4983230072969 + 3 ^ 40 * 1688611 * 2
def baseEnd_1688611 : Nat := 578046054312932023597817

theorem tailTrace_1688611 : CollatzResearch.WordTrace tailWord_1688611 prefixEnd_1688611 578046054312932023597817 := by
  unfold tailWord_1688611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61588702885458213643865687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41059135256972142429243791 61588702885458213643865687)
  ·
    refine ⟨92383054328187320465798531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61588702885458213643865687 92383054328187320465798531)
    ·
      refine ⟨138574581492280980698697797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92383054328187320465798531 138574581492280980698697797)
      ·
        refine ⟨25982734029802683881005837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138574581492280980698697797 25982734029802683881005837)
        ·
          refine ⟨9743525261176006455377189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25982734029802683881005837 9743525261176006455377189)
          ·
            refine ⟨1826910986470501210383223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9743525261176006455377189 1826910986470501210383223)
            ·
              refine ⟨2740366479705751815574835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826910986470501210383223 2740366479705751815574835)
              ·
                refine ⟨4110549719558627723362253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740366479705751815574835 4110549719558627723362253)
                ·
                  refine ⟨1541456144834485396260845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4110549719558627723362253 1541456144834485396260845)
                  ·
                    refine ⟨578046054312932023597817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541456144834485396260845 578046054312932023597817)
                    ·
                      rfl

theorem cell22_1688611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].length) (baseStart_1688611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688611 prefixEnd_1688611 := by exact prefixLift 1688611
  have htrace : WordTrace (prefixWord ++ tailWord_1688611) baseStart_1688611 baseEnd_1688611 := by
    simpa [prefixWord, tailWord_1688611, baseEnd_1688611] using wordTrace_append hprefix tailTrace_1688611
  have hstable : (prefixWord ++ tailWord_1688611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688611).length < 2 ^ (prefixWord ++ tailWord_1688611).sum := by decide
  have hdescent : baseEnd_1688611 < baseStart_1688611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688662 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1688662 : Nat := 118140960795 + 1688662 * 2 ^ 59
def prefixEnd_1688662 : Nat := 4983230072969 + 3 ^ 40 * 1688662 * 2
def baseEnd_1688662 : Nat := 578063512655184890572661

theorem tailTrace_1688662 : CollatzResearch.WordTrace tailWord_1688662 prefixEnd_1688662 578063512655184890572661 := by
  unfold tailWord_1688662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849410188017090584623265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41060375338848966235981493 3849410188017090584623265)
  ·
    refine ⟨2887057641012817938467449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3849410188017090584623265 2887057641012817938467449)
    ·
      refine ⟨2165293230759613453850587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2887057641012817938467449 2165293230759613453850587)
      ·
        refine ⟨3247939846139420180775881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165293230759613453850587 3247939846139420180775881)
        ·
          refine ⟨2435954884604565135581911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247939846139420180775881 2435954884604565135581911)
          ·
            refine ⟨3653932326906847703372867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435954884604565135581911 3653932326906847703372867)
            ·
              refine ⟨5480898490360271555059301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653932326906847703372867 5480898490360271555059301)
              ·
                refine ⟨1027668466942550916573619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5480898490360271555059301 1027668466942550916573619)
                ·
                  refine ⟨1541502700413826374860429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027668466942550916573619 1541502700413826374860429)
                  ·
                    refine ⟨578063512655184890572661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541502700413826374860429 578063512655184890572661)
                    ·
                      rfl

theorem cell22_1688662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1688662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688662 prefixEnd_1688662 := by exact prefixLift 1688662
  have htrace : WordTrace (prefixWord ++ tailWord_1688662) baseStart_1688662 baseEnd_1688662 := by
    simpa [prefixWord, tailWord_1688662, baseEnd_1688662] using wordTrace_append hprefix tailTrace_1688662
  have hstable : (prefixWord ++ tailWord_1688662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688662).length < 2 ^ (prefixWord ++ tailWord_1688662).sum := by decide
  have hdescent : baseEnd_1688662 < baseStart_1688662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688684 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_1688684 : Nat := 118140960795 + 1688684 * 2 ^ 59
def prefixEnd_1688684 : Nat := 4983230072969 + 3 ^ 40 * 1688684 * 2
def baseEnd_1688684 : Nat := 578071043704784166522593

theorem tailTrace_1688684 : CollatzResearch.WordTrace tailWord_1688684 prefixEnd_1688684 578071043704784166522593 := by
  unfold tailWord_1688684
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795682707096873555636553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41060910276129164740848737 30795682707096873555636553)
  ·
    refine ⟨23096762030322655166727415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30795682707096873555636553 23096762030322655166727415)
    ·
      refine ⟨34645143045483982750091123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23096762030322655166727415 34645143045483982750091123)
      ·
        refine ⟨51967714568225974125136685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34645143045483982750091123 51967714568225974125136685)
        ·
          refine ⟨19487892963084740296926257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51967714568225974125136685 19487892963084740296926257)
          ·
            refine ⟨14615919722313555222694693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19487892963084740296926257 14615919722313555222694693)
            ·
              refine ⟨2740484947933791604255255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14615919722313555222694693 2740484947933791604255255)
              ·
                refine ⟨4110727421900687406382883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740484947933791604255255 4110727421900687406382883)
                ·
                  refine ⟨6166091132851031109574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110727421900687406382883 6166091132851031109574325)
                  ·
                    refine ⟨578071043704784166522593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6166091132851031109574325 578071043704784166522593)
                    ·
                      rfl

theorem cell22_1688684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_1688684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688684 prefixEnd_1688684 := by exact prefixLift 1688684
  have htrace : WordTrace (prefixWord ++ tailWord_1688684) baseStart_1688684 baseEnd_1688684 := by
    simpa [prefixWord, tailWord_1688684, baseEnd_1688684] using wordTrace_append hprefix tailTrace_1688684
  have hstable : (prefixWord ++ tailWord_1688684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688684).length < 2 ^ (prefixWord ++ tailWord_1688684).sum := by decide
  have hdescent : baseEnd_1688684 < baseStart_1688684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688718 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1688718 : Nat := 118140960795 + 1688718 * 2 ^ 59
def prefixEnd_1688718 : Nat := 4983230072969 + 3 ^ 40 * 1688718 * 2
def baseEnd_1688718 : Nat := 578082682599619411172489

theorem tailTrace_1688718 : CollatzResearch.WordTrace tailWord_1688718 prefixEnd_1688718 578082682599619411172489 := by
  unfold tailWord_1688718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699075687008821364751351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41061736997380380612007205 7699075687008821364751351)
  ·
    refine ⟨11548613530513232047127027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7699075687008821364751351 11548613530513232047127027)
    ·
      refine ⟨17322920295769848070690541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11548613530513232047127027 17322920295769848070690541)
      ·
        refine ⟨6496095110913693026508953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17322920295769848070690541 6496095110913693026508953)
        ·
          refine ⟨4872071333185269769881715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6496095110913693026508953 4872071333185269769881715)
          ·
            refine ⟨7308106999777904654822573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872071333185269769881715 7308106999777904654822573)
            ·
              refine ⟨2740540124916714245558465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7308106999777904654822573 2740540124916714245558465)
              ·
                refine ⟨2055405093687535684168849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740540124916714245558465 2055405093687535684168849)
                ·
                  refine ⟨1541553820265651763126637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055405093687535684168849 1541553820265651763126637)
                  ·
                    refine ⟨578082682599619411172489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541553820265651763126637 578082682599619411172489)
                    ·
                      rfl

theorem cell22_1688718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1688718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688718 prefixEnd_1688718 := by exact prefixLift 1688718
  have htrace : WordTrace (prefixWord ++ tailWord_1688718) baseStart_1688718 baseEnd_1688718 := by
    simpa [prefixWord, tailWord_1688718, baseEnd_1688718] using wordTrace_append hprefix tailTrace_1688718
  have hstable : (prefixWord ++ tailWord_1688718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688718).length < 2 ^ (prefixWord ++ tailWord_1688718).sum := by decide
  have hdescent : baseEnd_1688718 < baseStart_1688718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688735 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 2, 3]
def baseStart_1688735 : Nat := 118140960795 + 1688735 * 2 ^ 59
def prefixEnd_1688735 : Nat := 4983230072969 + 3 ^ 40 * 1688735 * 2
def baseEnd_1688735 : Nat := 578088502047037033497437

theorem tailTrace_1688735 : CollatzResearch.WordTrace tailWord_1688735 prefixEnd_1688735 578088502047037033497437 := by
  unfold tailWord_1688735
  simp only [CollatzResearch.WordTrace]
  refine ⟨61593225537008982821379659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41062150358005988547586439 61593225537008982821379659)
  ·
    refine ⟨92389838305513474232069489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61593225537008982821379659 92389838305513474232069489)
    ·
      refine ⟨69292378729135105674052117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92389838305513474232069489 69292378729135105674052117)
      ·
        refine ⟨3248080252928208078471193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69292378729135105674052117 3248080252928208078471193)
        ·
          refine ⟨2436060189696156058853395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3248080252928208078471193 2436060189696156058853395)
          ·
            refine ⟨3654090284544234088280093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436060189696156058853395 3654090284544234088280093)
            ·
              refine ⟨1370283856704087783105035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654090284544234088280093 1370283856704087783105035)
              ·
                refine ⟨2055425785056131674657553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370283856704087783105035 2055425785056131674657553)
                ·
                  refine ⟨1541569338792098755993165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055425785056131674657553 1541569338792098755993165)
                  ·
                    refine ⟨578088502047037033497437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541569338792098755993165 578088502047037033497437)
                    ·
                      rfl

theorem cell22_1688735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_1688735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688735 prefixEnd_1688735 := by exact prefixLift 1688735
  have htrace : WordTrace (prefixWord ++ tailWord_1688735) baseStart_1688735 baseEnd_1688735 := by
    simpa [prefixWord, tailWord_1688735, baseEnd_1688735] using wordTrace_append hprefix tailTrace_1688735
  have hstable : (prefixWord ++ tailWord_1688735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688735).length < 2 ^ (prefixWord ++ tailWord_1688735).sum := by decide
  have hdescent : baseEnd_1688735 < baseStart_1688735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688804 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1688804 : Nat := 118140960795 + 1688804 * 2 ^ 59
def prefixEnd_1688804 : Nat := 4983230072969 + 3 ^ 40 * 1688804 * 2
def baseEnd_1688804 : Nat := 192704040719047951174075

theorem tailTrace_1688804 : CollatzResearch.WordTrace tailWord_1688804 prefixEnd_1688804 192704040719047951174075 := by
  unfold tailWord_1688804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30797871086879503802820733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41063828115839338403760977 30797871086879503802820733)
  ·
    refine ⟨11549201657579813926057775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30797871086879503802820733 11549201657579813926057775)
    ·
      refine ⟨17323802486369720889086663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549201657579813926057775 17323802486369720889086663)
      ·
        refine ⟨25985703729554581333629995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323802486369720889086663 25985703729554581333629995)
        ·
          refine ⟨38978555594331872000444993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25985703729554581333629995 38978555594331872000444993)
          ·
            refine ⟨29233916695748904000333745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38978555594331872000444993 29233916695748904000333745)
            ·
              refine ⟨21925437521811678000250309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29233916695748904000333745 21925437521811678000250309)
              ·
                refine ⟨4111019535339689625046933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21925437521811678000250309 4111019535339689625046933)
                ·
                  refine ⟨192704040719047951174075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4111019535339689625046933 192704040719047951174075)
                  ·
                    rfl

theorem cell22_1688804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1688804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688804 prefixEnd_1688804 := by exact prefixLift 1688804
  have htrace : WordTrace (prefixWord ++ tailWord_1688804) baseStart_1688804 baseEnd_1688804 := by
    simpa [prefixWord, tailWord_1688804, baseEnd_1688804] using wordTrace_append hprefix tailTrace_1688804
  have hstable : (prefixWord ++ tailWord_1688804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688804).length < 2 ^ (prefixWord ++ tailWord_1688804).sum := by decide
  have hdescent : baseEnd_1688804 < baseStart_1688804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688819 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_1688819 : Nat := 118140960795 + 1688819 * 2 ^ 59
def prefixEnd_1688819 : Nat := 4983230072969 + 3 ^ 40 * 1688819 * 2
def baseEnd_1688819 : Nat := 578117256963688814397179

theorem tailTrace_1688819 : CollatzResearch.WordTrace tailWord_1688819 prefixEnd_1688819 578117256963688814397179 := by
  unfold tailWord_1688819
  simp only [CollatzResearch.WordTrace]
  refine ⟨61596289268704665167437511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41064192845803110111625007 61596289268704665167437511)
  ·
    refine ⟨92394433903056997751156267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61596289268704665167437511 92394433903056997751156267)
    ·
      refine ⟨138591650854585496626734401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92394433903056997751156267 138591650854585496626734401)
      ·
        refine ⟨103943738140939122470050801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138591650854585496626734401 103943738140939122470050801)
        ·
          refine ⟨77957803605704341852538101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103943738140939122470050801 77957803605704341852538101)
          ·
            refine ⟨7308544088034782048675447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77957803605704341852538101 7308544088034782048675447)
            ·
              refine ⟨10962816132052173073013171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308544088034782048675447 10962816132052173073013171)
              ·
                refine ⟨16444224198078259609519757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10962816132052173073013171 16444224198078259609519757)
                ·
                  refine ⟨6166584074279347353569909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16444224198078259609519757 6166584074279347353569909)
                  ·
                    refine ⟨578117256963688814397179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6166584074279347353569909 578117256963688814397179)
                    ·
                      rfl

theorem cell22_1688819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_1688819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688819 prefixEnd_1688819 := by exact prefixLift 1688819
  have htrace : WordTrace (prefixWord ++ tailWord_1688819) baseStart_1688819 baseEnd_1688819 := by
    simpa [prefixWord, tailWord_1688819, baseEnd_1688819] using wordTrace_append hprefix tailTrace_1688819
  have hstable : (prefixWord ++ tailWord_1688819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688819).length < 2 ^ (prefixWord ++ tailWord_1688819).sum := by decide
  have hdescent : baseEnd_1688819 < baseStart_1688819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688932 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_1688932 : Nat := 118140960795 + 1688932 * 2 ^ 59
def prefixEnd_1688932 : Nat := 4983230072969 + 3 ^ 40 * 1688932 * 2
def baseEnd_1688932 : Nat := 578155939172994186321833

theorem tailTrace_1688932 : CollatzResearch.WordTrace tailWord_1688932 prefixEnd_1688932 578155939172994186321833 := by
  unfold tailWord_1688932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30800205358647642733150525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41066940478196856977534033 30800205358647642733150525)
  ·
    refine ⟨11550077009492866024931447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30800205358647642733150525 11550077009492866024931447)
    ·
      refine ⟨17325115514239299037397171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550077009492866024931447 17325115514239299037397171)
      ·
        refine ⟨25987673271358948556095757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17325115514239299037397171 25987673271358948556095757)
        ·
          refine ⟨9745377476759605708535909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25987673271358948556095757 9745377476759605708535909)
          ·
            refine ⟨1827258276892426070350483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9745377476759605708535909 1827258276892426070350483)
            ·
              refine ⟨2740887415338639105525725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827258276892426070350483 2740887415338639105525725)
              ·
                refine ⟨1027832780751989664572147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2740887415338639105525725 1027832780751989664572147)
                ·
                  refine ⟨1541749171127984496858221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027832780751989664572147 1541749171127984496858221)
                  ·
                    refine ⟨578155939172994186321833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541749171127984496858221 578155939172994186321833)
                    ·
                      rfl

theorem cell22_1688932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_1688932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688932 prefixEnd_1688932 := by exact prefixLift 1688932
  have htrace : WordTrace (prefixWord ++ tailWord_1688932) baseStart_1688932 baseEnd_1688932 := by
    simpa [prefixWord, tailWord_1688932, baseEnd_1688932] using wordTrace_append hprefix tailTrace_1688932
  have hstable : (prefixWord ++ tailWord_1688932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688932).length < 2 ^ (prefixWord ++ tailWord_1688932).sum := by decide
  have hdescent : baseEnd_1688932 < baseStart_1688932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688949 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1688949 : Nat := 118140960795 + 1688949 * 2 ^ 59
def prefixEnd_1688949 : Nat := 4983230072969 + 3 ^ 40 * 1688949 * 2
def baseEnd_1688949 : Nat := 578161758620411808646781

theorem tailTrace_1688949 : CollatzResearch.WordTrace tailWord_1688949 prefixEnd_1688949 578161758620411808646781 := by
  unfold tailWord_1688949
  simp only [CollatzResearch.WordTrace]
  refine ⟨61601030758233697369669901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41067353838822464913113267 61601030758233697369669901)
  ·
    refine ⟨23100386534337636513626213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61601030758233697369669901 23100386534337636513626213)
    ·
      refine ⟨4331322475188306846304915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23100386534337636513626213 4331322475188306846304915)
      ·
        refine ⟨6496983712782460269457373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331322475188306846304915 6496983712782460269457373)
        ·
          refine ⟨2436368892293422601046515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6496983712782460269457373 2436368892293422601046515)
          ·
            refine ⟨3654553338440133901569773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436368892293422601046515 3654553338440133901569773)
            ·
              refine ⟨1370457501915050213088665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654553338440133901569773 1370457501915050213088665)
              ·
                refine ⟨1027843126436287659816499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370457501915050213088665 1027843126436287659816499)
                ·
                  refine ⟨1541764689654431489724749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027843126436287659816499 1541764689654431489724749)
                  ·
                    refine ⟨578161758620411808646781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541764689654431489724749 578161758620411808646781)
                    ·
                      rfl

theorem cell22_1688949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1688949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688949 prefixEnd_1688949 := by exact prefixLift 1688949
  have htrace : WordTrace (prefixWord ++ tailWord_1688949) baseStart_1688949 baseEnd_1688949 := by
    simpa [prefixWord, tailWord_1688949, baseEnd_1688949] using wordTrace_append hprefix tailTrace_1688949
  have hstable : (prefixWord ++ tailWord_1688949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688949).length < 2 ^ (prefixWord ++ tailWord_1688949).sum := by decide
  have hdescent : baseEnd_1688949 < baseStart_1688949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688962 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1688962 : Nat := 118140960795 + 1688962 * 2 ^ 59
def prefixEnd_1688962 : Nat := 4983230072969 + 3 ^ 40 * 1688962 * 2
def baseEnd_1688962 : Nat := 192722069595361369357247

theorem tailTrace_1688962 : CollatzResearch.WordTrace tailWord_1688962 prefixEnd_1688962 192722069595361369357247 := by
  unfold tailWord_1688962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400376226796650147473285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41067669938124400393262093 15400376226796650147473285)
  ·
    refine ⟨2887570542524371902651241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15400376226796650147473285 2887570542524371902651241)
    ·
      refine ⟨2165677906893278926988431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2887570542524371902651241 2165677906893278926988431)
      ·
        refine ⟨3248516860339918390482647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165677906893278926988431 3248516860339918390482647)
        ·
          refine ⟨4872775290509877585723971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248516860339918390482647 4872775290509877585723971)
          ·
            refine ⟨7309162935764816378585957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872775290509877585723971 7309162935764816378585957)
            ·
              refine ⟨1370468050455903070984867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7309162935764816378585957 1370468050455903070984867)
              ·
                refine ⟨2055702075683854606477301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370468050455903070984867 2055702075683854606477301)
                ·
                  refine ⟨192722069595361369357247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2055702075683854606477301 192722069595361369357247)
                  ·
                    rfl

theorem cell22_1688962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1688962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688962 prefixEnd_1688962 := by exact prefixLift 1688962
  have htrace : WordTrace (prefixWord ++ tailWord_1688962) baseStart_1688962 baseEnd_1688962 := by
    simpa [prefixWord, tailWord_1688962, baseEnd_1688962] using wordTrace_append hprefix tailTrace_1688962
  have hstable : (prefixWord ++ tailWord_1688962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688962).length < 2 ^ (prefixWord ++ tailWord_1688962).sum := by decide
  have hdescent : baseEnd_1688962 < baseStart_1688962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688971 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_1688971 : Nat := 118140960795 + 1688971 * 2 ^ 59
def prefixEnd_1688971 : Nat := 4983230072969 + 3 ^ 40 * 1688971 * 2
def baseEnd_1688971 : Nat := 578169289670011084596713

theorem tailTrace_1688971 : CollatzResearch.WordTrace tailWord_1688971 prefixEnd_1688971 578169289670011084596713 := by
  unfold tailWord_1688971
  simp only [CollatzResearch.WordTrace]
  refine ⟨61601833164153995126970767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41067888776102663417980511 61601833164153995126970767)
  ·
    refine ⟨92402749746230992690456151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61601833164153995126970767 92402749746230992690456151)
    ·
      refine ⟨138604124619346489035684227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92402749746230992690456151 138604124619346489035684227)
      ·
        refine ⟨207906186929019733553526341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138604124619346489035684227 207906186929019733553526341)
        ·
          refine ⟨38982410049191200041286189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207906186929019733553526341 38982410049191200041286189)
          ·
            refine ⟨14618403768446700015482321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38982410049191200041286189 14618403768446700015482321)
            ·
              refine ⟨10963802826335025011611741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14618403768446700015482321 10963802826335025011611741)
              ·
                refine ⟨4111426059875634379354403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10963802826335025011611741 4111426059875634379354403)
                ·
                  refine ⟨6167139089813451569031605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111426059875634379354403 6167139089813451569031605)
                  ·
                    refine ⟨578169289670011084596713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6167139089813451569031605 578169289670011084596713)
                    ·
                      rfl

theorem cell22_1688971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_1688971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1688971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1688971 prefixEnd_1688971 := by exact prefixLift 1688971
  have htrace : WordTrace (prefixWord ++ tailWord_1688971) baseStart_1688971 baseEnd_1688971 := by
    simpa [prefixWord, tailWord_1688971, baseEnd_1688971] using wordTrace_append hprefix tailTrace_1688971
  have hstable : (prefixWord ++ tailWord_1688971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688971).length < 2 ^ (prefixWord ++ tailWord_1688971).sum := by decide
  have hdescent : baseEnd_1688971 < baseStart_1688971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689031 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1689031 : Nat := 118140960795 + 1689031 * 2 ^ 59
def prefixEnd_1689031 : Nat := 4983230072969 + 3 ^ 40 * 1689031 * 2
def baseEnd_1689031 : Nat := 578189828896190928096529

theorem tailTrace_1689031 : CollatzResearch.WordTrace tailWord_1689031 prefixEnd_1689031 578189828896190928096529 := by
  unfold tailWord_1689031
  simp only [CollatzResearch.WordTrace]
  refine ⟨61604021543936625374154947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41069347695957750249436631 61604021543936625374154947)
  ·
    refine ⟨92406032315904938061232421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61604021543936625374154947 92406032315904938061232421)
    ·
      refine ⟨17326131059232175886481079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92406032315904938061232421 17326131059232175886481079)
      ·
        refine ⟨25989196588848263829721619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17326131059232175886481079 25989196588848263829721619)
        ·
          refine ⟨38983794883272395744582429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25989196588848263829721619 38983794883272395744582429)
          ·
            refine ⟨14618923081227148404218411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38983794883272395744582429 14618923081227148404218411)
            ·
              refine ⟨21928384621840722606327617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14618923081227148404218411 21928384621840722606327617)
              ·
                refine ⟨16446288466380541954745713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21928384621840722606327617 16446288466380541954745713)
                ·
                  refine ⟨12334716349785406466059285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16446288466380541954745713 12334716349785406466059285)
                  ·
                    refine ⟨578189828896190928096529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12334716349785406466059285 578189828896190928096529)
                    ·
                      rfl

theorem cell22_1689031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1689031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689031 prefixEnd_1689031 := by exact prefixLift 1689031
  have htrace : WordTrace (prefixWord ++ tailWord_1689031) baseStart_1689031 baseEnd_1689031 := by
    simpa [prefixWord, tailWord_1689031, baseEnd_1689031] using wordTrace_append hprefix tailTrace_1689031
  have hstable : (prefixWord ++ tailWord_1689031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689031).length < 2 ^ (prefixWord ++ tailWord_1689031).sum := by decide
  have hdescent : baseEnd_1689031 < baseStart_1689031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689063 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 7]
def baseStart_1689063 : Nat := 118140960795 + 1689063 * 2 ^ 59
def prefixEnd_1689063 : Nat := 4983230072969 + 3 ^ 40 * 1689063 * 2
def baseEnd_1689063 : Nat := 192733594383384503765477

theorem tailTrace_1689063 : CollatzResearch.WordTrace tailWord_1689063 prefixEnd_1689063 192733594383384503765477 := by
  unfold tailWord_1689063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61605188679820694839319843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41070125786547129892879895 61605188679820694839319843)
  ·
    refine ⟨92407783019731042258979765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61605188679820694839319843 92407783019731042258979765)
    ·
      refine ⟨8663229658099785211779353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92407783019731042258979765 8663229658099785211779353)
      ·
        refine ⟨6497422243574838908834515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663229658099785211779353 6497422243574838908834515)
        ·
          refine ⟨9746133365362258363251773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497422243574838908834515 9746133365362258363251773)
          ·
            refine ⟨3654800012010846886219415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9746133365362258363251773 3654800012010846886219415)
            ·
              refine ⟨5482200018016270329329123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654800012010846886219415 5482200018016270329329123)
              ·
                refine ⟨8223300027024405493993685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482200018016270329329123 8223300027024405493993685)
                ·
                  refine ⟨192733594383384503765477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8223300027024405493993685 192733594383384503765477)
                  ·
                    rfl

theorem cell22_1689063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_1689063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689063 prefixEnd_1689063 := by exact prefixLift 1689063
  have htrace : WordTrace (prefixWord ++ tailWord_1689063) baseStart_1689063 baseEnd_1689063 := by
    simpa [prefixWord, tailWord_1689063, baseEnd_1689063] using wordTrace_append hprefix tailTrace_1689063
  have hstable : (prefixWord ++ tailWord_1689063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689063).length < 2 ^ (prefixWord ++ tailWord_1689063).sum := by decide
  have hdescent : baseEnd_1689063 < baseStart_1689063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689080 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_1689080 : Nat := 118140960795 + 1689080 * 2 ^ 59
def prefixEnd_1689080 : Nat := 4983230072969 + 3 ^ 40 * 1689080 * 2
def baseEnd_1689080 : Nat := 192735534199190377873793

theorem tailTrace_1689080 : CollatzResearch.WordTrace tailWord_1689080 prefixEnd_1689080 192735534199190377873793 := by
  unfold tailWord_1689080
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802904360379553371344347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41070539147172737828459129 30802904360379553371344347)
  ·
    refine ⟨46204356540569330057016521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30802904360379553371344347 46204356540569330057016521)
    ·
      refine ⟨34653267405426997542762391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46204356540569330057016521 34653267405426997542762391)
      ·
        refine ⟨51979901108140496314143587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34653267405426997542762391 51979901108140496314143587)
        ·
          refine ⟨77969851662210744471215381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51979901108140496314143587 77969851662210744471215381)
          ·
            refine ⟨3654836796666128647088221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77969851662210744471215381 3654836796666128647088221)
            ·
              refine ⟨1370563798749798242658083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654836796666128647088221 1370563798749798242658083)
              ·
                refine ⟨2055845698124697363987125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370563798749798242658083 2055845698124697363987125)
                ·
                  refine ⟨192735534199190377873793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2055845698124697363987125 192735534199190377873793)
                  ·
                    rfl

theorem cell22_1689080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_1689080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689080 prefixEnd_1689080 := by exact prefixLift 1689080
  have htrace : WordTrace (prefixWord ++ tailWord_1689080) baseStart_1689080 baseEnd_1689080 := by
    simpa [prefixWord, tailWord_1689080, baseEnd_1689080] using wordTrace_append hprefix tailTrace_1689080
  have hstable : (prefixWord ++ tailWord_1689080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689080).length < 2 ^ (prefixWord ++ tailWord_1689080).sum := by decide
  have hdescent : baseEnd_1689080 < baseStart_1689080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689091 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 8]
def baseStart_1689091 : Nat := 118140960795 + 1689091 * 2 ^ 59
def prefixEnd_1689091 : Nat := 4983230072969 + 3 ^ 40 * 1689091 * 2
def baseEnd_1689091 : Nat := 192736789374123590532115

theorem tailTrace_1689091 : CollatzResearch.WordTrace tailWord_1689091 prefixEnd_1689091 192736789374123590532115 := by
  unfold tailWord_1689091
  simp only [CollatzResearch.WordTrace]
  refine ⟨61606209923719255621339127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41070806615812837080892751 61606209923719255621339127)
  ·
    refine ⟨92409314885578883432008691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61606209923719255621339127 92409314885578883432008691)
    ·
      refine ⟨138613972328368325148013037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92409314885578883432008691 138613972328368325148013037)
      ·
        refine ⟨51980239623138121930504889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138613972328368325148013037 51980239623138121930504889)
        ·
          refine ⟨38985179717353591447878667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51980239623138121930504889 38985179717353591447878667)
          ·
            refine ⟨58477769576030387171818001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38985179717353591447878667 58477769576030387171818001)
            ·
              refine ⟨43858327182022790378863501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58477769576030387171818001 43858327182022790378863501)
              ·
                refine ⟨16446872693258546392073813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43858327182022790378863501 16446872693258546392073813)
                ·
                  refine ⟨192736789374123590532115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16446872693258546392073813 192736789374123590532115)
                  ·
                    rfl

theorem cell22_1689091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_1689091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689091 prefixEnd_1689091 := by exact prefixLift 1689091
  have htrace : WordTrace (prefixWord ++ tailWord_1689091) baseStart_1689091 baseEnd_1689091 := by
    simpa [prefixWord, tailWord_1689091, baseEnd_1689091] using wordTrace_append hprefix tailTrace_1689091
  have hstable : (prefixWord ++ tailWord_1689091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689091).length < 2 ^ (prefixWord ++ tailWord_1689091).sum := by decide
  have hdescent : baseEnd_1689091 < baseStart_1689091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689118 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1689118 : Nat := 118140960795 + 1689118 * 2 ^ 59
def prefixEnd_1689118 : Nat := 4983230072969 + 3 ^ 40 * 1689118 * 2
def baseEnd_1689118 : Nat := 578219610774151701171263

theorem tailTrace_1689118 : CollatzResearch.WordTrace tailWord_1689118 prefixEnd_1689118 578219610774151701171263 := by
  unfold tailWord_1689118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700899336827679904071501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41071463129747626155048005 7700899336827679904071501)
  ·
    refine ⟨2887837251310379964026813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7700899336827679904071501 2887837251310379964026813)
    ·
      refine ⟨1082938969241392486510055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2887837251310379964026813 1082938969241392486510055)
      ·
        refine ⟨1624408453862088729765083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082938969241392486510055 1624408453862088729765083)
        ·
          refine ⟨2436612680793133094647625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624408453862088729765083 2436612680793133094647625)
          ·
            refine ⟨1827459510594849820985719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436612680793133094647625 1827459510594849820985719)
            ·
              refine ⟨2741189265892274731478579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827459510594849820985719 2741189265892274731478579)
              ·
                refine ⟨4111783898838412097217869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741189265892274731478579 4111783898838412097217869)
                ·
                  refine ⟨1541918962064404536456701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4111783898838412097217869 1541918962064404536456701)
                  ·
                    refine ⟨578219610774151701171263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541918962064404536456701 578219610774151701171263)
                    ·
                      rfl

theorem cell22_1689118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1689118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689118 prefixEnd_1689118 := by exact prefixLift 1689118
  have htrace : WordTrace (prefixWord ++ tailWord_1689118) baseStart_1689118 baseEnd_1689118 := by
    simpa [prefixWord, tailWord_1689118, baseEnd_1689118] using wordTrace_append hprefix tailTrace_1689118
  have hstable : (prefixWord ++ tailWord_1689118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689118).length < 2 ^ (prefixWord ++ tailWord_1689118).sum := by decide
  have hdescent : baseEnd_1689118 < baseStart_1689118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689138 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1689138 : Nat := 118140960795 + 1689138 * 2 ^ 59
def prefixEnd_1689138 : Nat := 4983230072969 + 3 ^ 40 * 1689138 * 2
def baseEnd_1689138 : Nat := 578226457182878315671201

theorem tailTrace_1689138 : CollatzResearch.WordTrace tailWord_1689138 prefixEnd_1689138 578226457182878315671201 := by
  unfold tailWord_1689138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401981038637245662075017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41071949436365988432200045 15401981038637245662075017)
  ·
    refine ⟨11551485778977934246556263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15401981038637245662075017 11551485778977934246556263)
    ·
      refine ⟨17327228668466901369834395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11551485778977934246556263 17327228668466901369834395)
      ·
        refine ⟨25990843002700352054751593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17327228668466901369834395 25990843002700352054751593)
        ·
          refine ⟨19493132252025264041063695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25990843002700352054751593 19493132252025264041063695)
          ·
            refine ⟨29239698378037896061595543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19493132252025264041063695 29239698378037896061595543)
            ·
              refine ⟨43859547567056844092393315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29239698378037896061595543 43859547567056844092393315)
              ·
                refine ⟨65789321350585266138589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43859547567056844092393315 65789321350585266138589973)
                ·
                  refine ⟨3083874438308684350246405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65789321350585266138589973 3083874438308684350246405)
                  ·
                    refine ⟨578226457182878315671201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083874438308684350246405 578226457182878315671201)
                    ·
                      rfl

theorem cell22_1689138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1689138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689138 prefixEnd_1689138 := by exact prefixLift 1689138
  have htrace : WordTrace (prefixWord ++ tailWord_1689138) baseStart_1689138 baseEnd_1689138 := by
    simpa [prefixWord, tailWord_1689138, baseEnd_1689138] using wordTrace_append hprefix tailTrace_1689138
  have hstable : (prefixWord ++ tailWord_1689138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689138).length < 2 ^ (prefixWord ++ tailWord_1689138).sum := by decide
  have hdescent : baseEnd_1689138 < baseStart_1689138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689153 : List Nat := [1, 2, 5, 1, 1, 1, 1, 10]
def baseStart_1689153 : Nat := 118140960795 + 1689153 * 2 ^ 59
def prefixEnd_1689153 : Nat := 4983230072969 + 3 ^ 40 * 1689153 * 2
def baseEnd_1689153 : Nat := 64247954665491475171795

theorem tailTrace_1689153 : CollatzResearch.WordTrace tailWord_1689153 prefixEnd_1689153 64247954665491475171795 := by
  unfold tailWord_1689153
  simp only [CollatzResearch.WordTrace]
  refine ⟨61608471249494640210096113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41072314166329760140064075 61608471249494640210096113)
  ·
    refine ⟨46206353437120980157572085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61608471249494640210096113 46206353437120980157572085)
    ·
      refine ⟨4331845634730091889772383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46206353437120980157572085 4331845634730091889772383)
      ·
        refine ⟨6497768452095137834658575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331845634730091889772383 6497768452095137834658575)
        ·
          refine ⟨9746652678142706751987863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497768452095137834658575 9746652678142706751987863)
          ·
            refine ⟨14619979017214060127981795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746652678142706751987863 14619979017214060127981795)
            ·
              refine ⟨21929968525821090191972693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619979017214060127981795 21929968525821090191972693)
              ·
                refine ⟨64247954665491475171795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21929968525821090191972693 64247954665491475171795)
                ·
                  rfl

theorem cell22_1689153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 10].length) (baseStart_1689153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689153 prefixEnd_1689153 := by exact prefixLift 1689153
  have htrace : WordTrace (prefixWord ++ tailWord_1689153) baseStart_1689153 baseEnd_1689153 := by
    simpa [prefixWord, tailWord_1689153, baseEnd_1689153] using wordTrace_append hprefix tailTrace_1689153
  have hstable : (prefixWord ++ tailWord_1689153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689153).length < 2 ^ (prefixWord ++ tailWord_1689153).sum := by decide
  have hdescent : baseEnd_1689153 < baseStart_1689153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689185 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1689185 : Nat := 118140960795 + 1689185 * 2 ^ 59
def prefixEnd_1689185 : Nat := 4983230072969 + 3 ^ 40 * 1689185 * 2
def baseEnd_1689185 : Nat := 578242546243385859746057

theorem tailTrace_1689185 : CollatzResearch.WordTrace tailWord_1689185 prefixEnd_1689185 578242546243385859746057 := by
  unfold tailWord_1689185
  simp only [CollatzResearch.WordTrace]
  refine ⟨61609638385378709675261009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41073092256919139783507339 61609638385378709675261009)
  ·
    refine ⟨46207228789034032256445757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61609638385378709675261009 46207228789034032256445757)
    ·
      refine ⟨17327710795887762096167159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46207228789034032256445757 17327710795887762096167159)
      ·
        refine ⟨25991566193831643144250739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17327710795887762096167159 25991566193831643144250739)
        ·
          refine ⟨38987349290747464716376109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25991566193831643144250739 38987349290747464716376109)
          ·
            refine ⟨14620255984030299268641041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38987349290747464716376109 14620255984030299268641041)
            ·
              refine ⟨10965191988022724451480781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14620255984030299268641041 10965191988022724451480781)
              ·
                refine ⟨4111946995508521669305293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10965191988022724451480781 4111946995508521669305293)
                ·
                  refine ⟨1541980123315695625989485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4111946995508521669305293 1541980123315695625989485)
                  ·
                    refine ⟨578242546243385859746057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541980123315695625989485 578242546243385859746057)
                    ·
                      rfl

theorem cell22_1689185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1689185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689185 prefixEnd_1689185 := by exact prefixLift 1689185
  have htrace : WordTrace (prefixWord ++ tailWord_1689185) baseStart_1689185 baseEnd_1689185 := by
    simpa [prefixWord, tailWord_1689185, baseEnd_1689185] using wordTrace_append hprefix tailTrace_1689185
  have hstable : (prefixWord ++ tailWord_1689185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689185).length < 2 ^ (prefixWord ++ tailWord_1689185).sum := by decide
  have hdescent : baseEnd_1689185 < baseStart_1689185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689202 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_1689202 : Nat := 118140960795 + 1689202 * 2 ^ 59
def prefixEnd_1689202 : Nat := 4983230072969 + 3 ^ 40 * 1689202 * 2
def baseEnd_1689202 : Nat := 578248365690803482071005

theorem tailTrace_1689202 : CollatzResearch.WordTrace tailWord_1689202 prefixEnd_1689202 578248365690803482071005 := by
  unfold tailWord_1689202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402564606579280394657465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41073505617544747719086573 15402564606579280394657465)
  ·
    refine ⟨11551923454934460295993099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15402564606579280394657465 11551923454934460295993099)
    ·
      refine ⟨17327885182401690443989649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11551923454934460295993099 17327885182401690443989649)
      ·
        refine ⟨12995913886801267832992237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17327885182401690443989649 12995913886801267832992237)
        ·
          refine ⟨4873467707550475437372089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12995913886801267832992237 4873467707550475437372089)
          ·
            refine ⟨3655100780662856578029067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873467707550475437372089 3655100780662856578029067)
            ·
              refine ⟨5482651170994284867043601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655100780662856578029067 5482651170994284867043601)
              ·
                refine ⟨4111988378245713650282701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482651170994284867043601 4111988378245713650282701)
                ·
                  refine ⟨1541995641842142618856013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4111988378245713650282701 1541995641842142618856013)
                  ·
                    refine ⟨578248365690803482071005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541995641842142618856013 578248365690803482071005)
                    ·
                      rfl

theorem cell22_1689202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_1689202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689202 prefixEnd_1689202 := by exact prefixLift 1689202
  have htrace : WordTrace (prefixWord ++ tailWord_1689202) baseStart_1689202 baseEnd_1689202 := by
    simpa [prefixWord, tailWord_1689202, baseEnd_1689202] using wordTrace_append hprefix tailTrace_1689202
  have hstable : (prefixWord ++ tailWord_1689202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689202).length < 2 ^ (prefixWord ++ tailWord_1689202).sum := by decide
  have hdescent : baseEnd_1689202 < baseStart_1689202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689230 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1689230 : Nat := 118140960795 + 1689230 * 2 ^ 59
def prefixEnd_1689230 : Nat := 4983230072969 + 3 ^ 40 * 1689230 * 2
def baseEnd_1689230 : Nat := 578257950663020742370919

theorem tailTrace_1689230 : CollatzResearch.WordTrace tailWord_1689230 prefixEnd_1689230 578257950663020742370919 := by
  unfold tailWord_1689230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701409958776960295081143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41074186446810454907099429 7701409958776960295081143)
  ·
    refine ⟨11552114938165440442621715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7701409958776960295081143 11552114938165440442621715)
    ·
      refine ⟨17328172407248160663932573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552114938165440442621715 17328172407248160663932573)
      ·
        refine ⟨6498064652718060248974715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17328172407248160663932573 6498064652718060248974715)
        ·
          refine ⟨9747096979077090373462073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498064652718060248974715 9747096979077090373462073)
          ·
            refine ⟨7310322734307817780096555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9747096979077090373462073 7310322734307817780096555)
            ·
              refine ⟨10965484101461726670144833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310322734307817780096555 10965484101461726670144833)
              ·
                refine ⟨8224113076096295002608625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965484101461726670144833 8224113076096295002608625)
                ·
                  refine ⟨6168084807072221251956469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8224113076096295002608625 6168084807072221251956469)
                  ·
                    refine ⟨578257950663020742370919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6168084807072221251956469 578257950663020742370919)
                    ·
                      rfl

theorem cell22_1689230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1689230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689230 prefixEnd_1689230 := by exact prefixLift 1689230
  have htrace : WordTrace (prefixWord ++ tailWord_1689230) baseStart_1689230 baseEnd_1689230 := by
    simpa [prefixWord, tailWord_1689230, baseEnd_1689230] using wordTrace_append hprefix tailTrace_1689230
  have hstable : (prefixWord ++ tailWord_1689230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689230).length < 2 ^ (prefixWord ++ tailWord_1689230).sum := by decide
  have hdescent : baseEnd_1689230 < baseStart_1689230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689294 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_1689294 : Nat := 118140960795 + 1689294 * 2 ^ 59
def prefixEnd_1689294 : Nat := 4983230072969 + 3 ^ 40 * 1689294 * 2
def baseEnd_1689294 : Nat := 192759953056981969590241

theorem tailTrace_1689294 : CollatzResearch.WordTrace tailWord_1689294 prefixEnd_1689294 192759953056981969590241 := by
  unfold tailWord_1689294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701701742747977661372367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41075742627989214193985957 7701701742747977661372367)
  ·
    refine ⟨11552552614121966492058551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7701701742747977661372367 11552552614121966492058551)
    ·
      refine ⟨17328828921182949738087827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552552614121966492058551 17328828921182949738087827)
      ·
        refine ⟨25993243381774424607131741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17328828921182949738087827 25993243381774424607131741)
        ·
          refine ⟨9747466268165409227674403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25993243381774424607131741 9747466268165409227674403)
          ·
            refine ⟨14621199402248113841511605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747466268165409227674403 14621199402248113841511605)
            ·
              refine ⟨1370737443960760672641713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14621199402248113841511605 1370737443960760672641713)
              ·
                refine ⟨1028053082970570504481285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370737443960760672641713 1028053082970570504481285)
                ·
                  refine ⟨192759953056981969590241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028053082970570504481285 192759953056981969590241)
                  ·
                    rfl

theorem cell22_1689294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_1689294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689294 prefixEnd_1689294 := by exact prefixLift 1689294
  have htrace : WordTrace (prefixWord ++ tailWord_1689294) baseStart_1689294 baseEnd_1689294 := by
    simpa [prefixWord, tailWord_1689294, baseEnd_1689294] using wordTrace_append hprefix tailTrace_1689294
  have hstable : (prefixWord ++ tailWord_1689294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689294).length < 2 ^ (prefixWord ++ tailWord_1689294).sum := by decide
  have hdescent : baseEnd_1689294 < baseStart_1689294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689305 : List Nat := [1, 2, 1, 2, 3, 4, 2, 7]
def baseStart_1689305 : Nat := 118140960795 + 1689305 * 2 ^ 59
def prefixEnd_1689305 : Nat := 4983230072969 + 3 ^ 40 * 1689305 * 2
def baseEnd_1689305 : Nat := 64253736077305060749521

theorem tailTrace_1689305 : CollatzResearch.WordTrace tailWord_1689305 prefixEnd_1689305 64253736077305060749521 := by
  unfold tailWord_1689305
  simp only [CollatzResearch.WordTrace]
  refine ⟨61614015144943970169629369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41076010096629313446419579 61614015144943970169629369)
  ·
    refine ⟨46210511358707977627222027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61614015144943970169629369 46210511358707977627222027)
    ·
      refine ⟨69315767038061966440833041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46210511358707977627222027 69315767038061966440833041)
      ·
        refine ⟨51986825278546474830624781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69315767038061966440833041 51986825278546474830624781)
        ·
          refine ⟨19495059479454928061484293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51986825278546474830624781 19495059479454928061484293)
          ·
            refine ⟨3655323652397799011528305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19495059479454928061484293 3655323652397799011528305)
            ·
              refine ⟨2741492739298349258646229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655323652397799011528305 2741492739298349258646229)
              ·
                refine ⟨64253736077305060749521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2741492739298349258646229 64253736077305060749521)
                ·
                  rfl

theorem cell22_1689305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 7].length) (baseStart_1689305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689305 prefixEnd_1689305 := by exact prefixLift 1689305
  have htrace : WordTrace (prefixWord ++ tailWord_1689305) baseStart_1689305 baseEnd_1689305 := by
    simpa [prefixWord, tailWord_1689305, baseEnd_1689305] using wordTrace_append hprefix tailTrace_1689305
  have hstable : (prefixWord ++ tailWord_1689305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689305).length < 2 ^ (prefixWord ++ tailWord_1689305).sum := by decide
  have hdescent : baseEnd_1689305 < baseStart_1689305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689365 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1689365 : Nat := 118140960795 + 1689365 * 2 ^ 59
def prefixEnd_1689365 : Nat := 4983230072969 + 3 ^ 40 * 1689365 * 2
def baseEnd_1689365 : Nat := 578304163921925390245505

theorem tailTrace_1689365 : CollatzResearch.WordTrace tailWord_1689365 prefixEnd_1689365 578304163921925390245505 := by
  unfold tailWord_1689365
  simp only [CollatzResearch.WordTrace]
  refine ⟨61616203524726600416813549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41077469016484400277875699 61616203524726600416813549)
  ·
    refine ⟨23106076321772475156305081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61616203524726600416813549 23106076321772475156305081)
    ·
      refine ⟨17329557241329356367228811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23106076321772475156305081 17329557241329356367228811)
      ·
        refine ⟨25994335861994034550843217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17329557241329356367228811 25994335861994034550843217)
        ·
          refine ⟨19495751896495525913132413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25994335861994034550843217 19495751896495525913132413)
          ·
            refine ⟨7310906961185822217424655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19495751896495525913132413 7310906961185822217424655)
            ·
              refine ⟨10966360441778733326136983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310906961185822217424655 10966360441778733326136983)
              ·
                refine ⟨16449540662668099989205475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10966360441778733326136983 16449540662668099989205475)
                ·
                  refine ⟨24674310994002149983808213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16449540662668099989205475 24674310994002149983808213)
                  ·
                    refine ⟨578304163921925390245505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24674310994002149983808213 578304163921925390245505)
                    ·
                      rfl

theorem cell22_1689365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1689365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689365 prefixEnd_1689365 := by exact prefixLift 1689365
  have htrace : WordTrace (prefixWord ++ tailWord_1689365) baseStart_1689365 baseEnd_1689365 := by
    simpa [prefixWord, tailWord_1689365, baseEnd_1689365] using wordTrace_append hprefix tailTrace_1689365
  have hstable : (prefixWord ++ tailWord_1689365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689365).length < 2 ^ (prefixWord ++ tailWord_1689365).sum := by decide
  have hdescent : baseEnd_1689365 < baseStart_1689365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689367 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 5]
def baseStart_1689367 : Nat := 118140960795 + 1689367 * 2 ^ 59
def prefixEnd_1689367 : Nat := 4983230072969 + 3 ^ 40 * 1689367 * 2
def baseEnd_1689367 : Nat := 192768282854266017231833

theorem tailTrace_1689367 : CollatzResearch.WordTrace tailWord_1689367 prefixEnd_1689367 192768282854266017231833 := by
  unfold tailWord_1689367
  simp only [CollatzResearch.WordTrace]
  refine ⟨61616276470719354758386355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41077517647146236505590903 61616276470719354758386355)
  ·
    refine ⟨92424414706079032137579533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61616276470719354758386355 92424414706079032137579533)
    ·
      refine ⟨34659155514779637051592325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92424414706079032137579533 34659155514779637051592325)
      ·
        refine ⟨6498591659021181947173561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34659155514779637051592325 6498591659021181947173561)
        ·
          refine ⟨4873943744265886460380171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6498591659021181947173561 4873943744265886460380171)
          ·
            refine ⟨7310915616398829690570257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873943744265886460380171 7310915616398829690570257)
            ·
              refine ⟨5483186712299122267927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310915616398829690570257 5483186712299122267927693)
              ·
                refine ⟨2056195017112170850472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5483186712299122267927693 2056195017112170850472885)
                ·
                  refine ⟨192768282854266017231833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056195017112170850472885 192768282854266017231833)
                  ·
                    rfl

theorem cell22_1689367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].length) (baseStart_1689367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689367 prefixEnd_1689367 := by exact prefixLift 1689367
  have htrace : WordTrace (prefixWord ++ tailWord_1689367) baseStart_1689367 baseEnd_1689367 := by
    simpa [prefixWord, tailWord_1689367, baseEnd_1689367] using wordTrace_append hprefix tailTrace_1689367
  have hstable : (prefixWord ++ tailWord_1689367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689367).length < 2 ^ (prefixWord ++ tailWord_1689367).sum := by decide
  have hdescent : baseEnd_1689367 < baseStart_1689367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689401 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 5]
def baseStart_1689401 : Nat := 118140960795 + 1689401 * 2 ^ 59
def prefixEnd_1689401 : Nat := 4983230072969 + 3 ^ 40 * 1689401 * 2
def baseEnd_1689401 : Nat := 192772162485877765448465

theorem tailTrace_1689401 : CollatzResearch.WordTrace tailWord_1689401 prefixEnd_1689401 192772162485877765448465 := by
  unfold tailWord_1689401
  simp only [CollatzResearch.WordTrace]
  refine ⟨61617516552596178565124057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41078344368397452376749371 61617516552596178565124057)
  ·
    refine ⟨46213137414447133923843043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61617516552596178565124057 46213137414447133923843043)
    ·
      refine ⟨69319706121670700885764565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46213137414447133923843043 69319706121670700885764565)
      ·
        refine ⟨1624680612226657052010107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69319706121670700885764565 1624680612226657052010107)
        ·
          refine ⟨2437020918339985578015161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624680612226657052010107 2437020918339985578015161)
          ·
            refine ⟨1827765688754989183511371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437020918339985578015161 1827765688754989183511371)
            ·
              refine ⟨2741648533132483775267057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827765688754989183511371 2741648533132483775267057)
              ·
                refine ⟨2056236399849362831450293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741648533132483775267057 2056236399849362831450293)
                ·
                  refine ⟨192772162485877765448465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056236399849362831450293 192772162485877765448465)
                  ·
                    rfl

theorem cell22_1689401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_1689401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689401 prefixEnd_1689401 := by exact prefixLift 1689401
  have htrace : WordTrace (prefixWord ++ tailWord_1689401) baseStart_1689401 baseEnd_1689401 := by
    simpa [prefixWord, tailWord_1689401, baseEnd_1689401] using wordTrace_append hprefix tailTrace_1689401
  have hstable : (prefixWord ++ tailWord_1689401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689401).length < 2 ^ (prefixWord ++ tailWord_1689401).sum := by decide
  have hdescent : baseEnd_1689401 < baseStart_1689401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689534 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1689534 : Nat := 118140960795 + 1689534 * 2 ^ 59
def prefixEnd_1689534 : Nat := 4983230072969 + 3 ^ 40 * 1689534 * 2
def baseEnd_1689534 : Nat := 578362016075665282769987

theorem tailTrace_1689534 : CollatzResearch.WordTrace tailWord_1689534 prefixEnd_1689534 578362016075665282769987 := by
  unfold tailWord_1689534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702795932639292784964457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41081578307409561519810437 7702795932639292784964457)
  ·
    refine ⟨5777096949479469588723343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7702795932639292784964457 5777096949479469588723343)
    ·
      refine ⟨8665645424219204383085015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777096949479469588723343 8665645424219204383085015)
      ·
        refine ⟨12998468136328806574627523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8665645424219204383085015 12998468136328806574627523)
        ·
          refine ⟨19497702204493209861941285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12998468136328806574627523 19497702204493209861941285)
          ·
            refine ⟨3655819163342476849113991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19497702204493209861941285 3655819163342476849113991)
            ·
              refine ⟨5483728745013715273670987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655819163342476849113991 5483728745013715273670987)
              ·
                refine ⟨8225593117520572910506481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483728745013715273670987 8225593117520572910506481)
                ·
                  refine ⟨6169194838140429682879861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8225593117520572910506481 6169194838140429682879861)
                  ·
                    refine ⟨578362016075665282769987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6169194838140429682879861 578362016075665282769987)
                    ·
                      rfl

theorem cell22_1689534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1689534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689534 prefixEnd_1689534 := by exact prefixLift 1689534
  have htrace : WordTrace (prefixWord ++ tailWord_1689534) baseStart_1689534 baseEnd_1689534 := by
    simpa [prefixWord, tailWord_1689534, baseEnd_1689534] using wordTrace_append hprefix tailTrace_1689534
  have hstable : (prefixWord ++ tailWord_1689534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689534).length < 2 ^ (prefixWord ++ tailWord_1689534).sum := by decide
  have hdescent : baseEnd_1689534 < baseStart_1689534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689547 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 6]
def baseStart_1689547 : Nat := 118140960795 + 1689547 * 2 ^ 59
def prefixEnd_1689547 : Nat := 4983230072969 + 3 ^ 40 * 1689547 * 2
def baseEnd_1689547 : Nat := 192788822080445860731649

theorem tailTrace_1689547 : CollatzResearch.WordTrace tailWord_1689547 prefixEnd_1689547 192788822080445860731649 := by
  unfold tailWord_1689547
  simp only [CollatzResearch.WordTrace]
  refine ⟨61622841610067245499938895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41081894406711496999959263 61622841610067245499938895)
  ·
    refine ⟨92434262415100868249908343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61622841610067245499938895 92434262415100868249908343)
    ·
      refine ⟨138651393622651302374862515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92434262415100868249908343 138651393622651302374862515)
      ·
        refine ⟨207977090433976953562293773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138651393622651302374862515 207977090433976953562293773)
        ·
          refine ⟨77991408912741357585860165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207977090433976953562293773 77991408912741357585860165)
          ·
            refine ⟨14623389171139004547348781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77991408912741357585860165 14623389171139004547348781)
            ·
              refine ⟨5483770939177126705255793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14623389171139004547348781 5483770939177126705255793)
              ·
                refine ⟨4112828204382845028941845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483770939177126705255793 4112828204382845028941845)
                ·
                  refine ⟨192788822080445860731649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4112828204382845028941845 192788822080445860731649)
                  ·
                    rfl

theorem cell22_1689547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_1689547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689547 prefixEnd_1689547 := by exact prefixLift 1689547
  have htrace : WordTrace (prefixWord ++ tailWord_1689547) baseStart_1689547 baseEnd_1689547 := by
    simpa [prefixWord, tailWord_1689547, baseEnd_1689547] using wordTrace_append hprefix tailTrace_1689547
  have hstable : (prefixWord ++ tailWord_1689547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689547).length < 2 ^ (prefixWord ++ tailWord_1689547).sum := by decide
  have hdescent : baseEnd_1689547 < baseStart_1689547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689570 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1689570 : Nat := 118140960795 + 1689570 * 2 ^ 59
def prefixEnd_1689570 : Nat := 4983230072969 + 3 ^ 40 * 1689570 * 2
def baseEnd_1689570 : Nat := 192791446537124396289959

theorem tailTrace_1689570 : CollatzResearch.WordTrace tailWord_1689570 prefixEnd_1689570 192791446537124396289959 := by
  unfold tailWord_1689570
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405920122245980107006541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41082453659322613618684109 15405920122245980107006541)
  ·
    refine ⟨5777220045842242540127453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15405920122245980107006541 5777220045842242540127453)
    ·
      refine ⟨2166457517190840952547795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5777220045842242540127453 2166457517190840952547795)
      ·
        refine ⟨3249686275786261428821693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166457517190840952547795 3249686275786261428821693)
        ·
          refine ⟨1218632353419848035808135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249686275786261428821693 1218632353419848035808135)
          ·
            refine ⟨1827948530129772053712203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218632353419848035808135 1827948530129772053712203)
            ·
              refine ⟨2741922795194658080568305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827948530129772053712203 2741922795194658080568305)
              ·
                refine ⟨2056442096395993560426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741922795194658080568305 2056442096395993560426229)
                ·
                  refine ⟨192791446537124396289959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056442096395993560426229 192791446537124396289959)
                  ·
                    rfl

theorem cell22_1689570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1689570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689570 prefixEnd_1689570 := by exact prefixLift 1689570
  have htrace : WordTrace (prefixWord ++ tailWord_1689570) baseStart_1689570 baseEnd_1689570 := by
    simpa [prefixWord, tailWord_1689570, baseEnd_1689570] using wordTrace_append hprefix tailTrace_1689570
  have hstable : (prefixWord ++ tailWord_1689570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689570).length < 2 ^ (prefixWord ++ tailWord_1689570).sum := by decide
  have hdescent : baseEnd_1689570 < baseStart_1689570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689692 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1689692 : Nat := 118140960795 + 1689692 * 2 ^ 59
def prefixEnd_1689692 : Nat := 4983230072969 + 3 ^ 40 * 1689692 * 2
def baseEnd_1689692 : Nat := 578416102704605537319503

theorem tailTrace_1689692 : CollatzResearch.WordTrace tailWord_1689692 prefixEnd_1689692 578416102704605537319503 := by
  unfold tailWord_1689692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30814065097270967631983665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41085420129694623509311553 30814065097270967631983665)
  ·
    refine ⟨23110548822953225723987749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30814065097270967631983665 23110548822953225723987749)
    ·
      refine ⟨4333227904303729823247703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23110548822953225723987749 4333227904303729823247703)
      ·
        refine ⟨6499841856455594734871555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333227904303729823247703 6499841856455594734871555)
        ·
          refine ⟨9749762784683392102307333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499841856455594734871555 9749762784683392102307333)
          ·
            refine ⟨1828080522128136019182625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9749762784683392102307333 1828080522128136019182625)
            ·
              refine ⟨1371060391596102014386969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828080522128136019182625 1371060391596102014386969)
              ·
                refine ⟨1028295293697076510790227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371060391596102014386969 1028295293697076510790227)
                ·
                  refine ⟨1542442940545614766185341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028295293697076510790227 1542442940545614766185341)
                  ·
                    refine ⟨578416102704605537319503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542442940545614766185341 578416102704605537319503)
                    ·
                      rfl

theorem cell22_1689692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1689692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689692 prefixEnd_1689692 := by exact prefixLift 1689692
  have htrace : WordTrace (prefixWord ++ tailWord_1689692) baseStart_1689692 baseEnd_1689692 := by
    simpa [prefixWord, tailWord_1689692, baseEnd_1689692] using wordTrace_append hprefix tailTrace_1689692
  have hstable : (prefixWord ++ tailWord_1689692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689692).length < 2 ^ (prefixWord ++ tailWord_1689692).sum := by decide
  have hdescent : baseEnd_1689692 < baseStart_1689692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689733 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1689733 : Nat := 118140960795 + 1689733 * 2 ^ 59
def prefixEnd_1689733 : Nat := 4983230072969 + 3 ^ 40 * 1689733 * 2
def baseEnd_1689733 : Nat := 192810045947498365681459

theorem tailTrace_1689733 : CollatzResearch.WordTrace tailWord_1689733 prefixEnd_1689733 192810045947498365681459 := by
  unfold tailWord_1689733
  simp only [CollatzResearch.WordTrace]
  refine ⟨61629625587393399266209853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41086417058262266177473235 61629625587393399266209853)
  ·
    refine ⟨23111109595272524724828695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61629625587393399266209853 23111109595272524724828695)
    ·
      refine ⟨34666664392908787087243043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23111109595272524724828695 34666664392908787087243043)
      ·
        refine ⟨51999996589363180630864565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34666664392908787087243043 51999996589363180630864565)
        ·
          refine ⟨4874999680252798184143553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51999996589363180630864565 4874999680252798184143553)
          ·
            refine ⟨3656249760189598638107665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4874999680252798184143553 3656249760189598638107665)
            ·
              refine ⟨2742187320142198978580749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656249760189598638107665 2742187320142198978580749)
              ·
                refine ⟨1028320245053324616967781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742187320142198978580749 1028320245053324616967781)
                ·
                  refine ⟨192810045947498365681459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028320245053324616967781 192810045947498365681459)
                  ·
                    rfl

theorem cell22_1689733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1689733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689733 prefixEnd_1689733 := by exact prefixLift 1689733
  have htrace : WordTrace (prefixWord ++ tailWord_1689733) baseStart_1689733 baseEnd_1689733 := by
    simpa [prefixWord, tailWord_1689733, baseEnd_1689733] using wordTrace_append hprefix tailTrace_1689733
  have hstable : (prefixWord ++ tailWord_1689733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689733).length < 2 ^ (prefixWord ++ tailWord_1689733).sum := by decide
  have hdescent : baseEnd_1689733 < baseStart_1689733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689746 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1689746 : Nat := 118140960795 + 1689746 * 2 ^ 59
def prefixEnd_1689746 : Nat := 4983230072969 + 3 ^ 40 * 1689746 * 2
def baseEnd_1689746 : Nat := 578434588008167396469337

theorem tailTrace_1689746 : CollatzResearch.WordTrace tailWord_1689746 prefixEnd_1689746 578434588008167396469337 := by
  unfold tailWord_1689746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407524934086575621608273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41086733157564201657622061 15407524934086575621608273)
  ·
    refine ⟨11555643700564931716206205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15407524934086575621608273 11555643700564931716206205)
    ·
      refine ⟨4333366387711849393577327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11555643700564931716206205 4333366387711849393577327)
      ·
        refine ⟨6500049581567774090365991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333366387711849393577327 6500049581567774090365991)
        ·
          refine ⟨9750074372351661135548987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500049581567774090365991 9750074372351661135548987)
          ·
            refine ⟨14625111558527491703323481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9750074372351661135548987 14625111558527491703323481)
            ·
              refine ⟨10968833668895618777492611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14625111558527491703323481 10968833668895618777492611)
              ·
                refine ⟨16453250503343428166238917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968833668895618777492611 16453250503343428166238917)
                ·
                  refine ⟨3084984469376892781169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16453250503343428166238917 3084984469376892781169797)
                  ·
                    refine ⟨578434588008167396469337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084984469376892781169797 578434588008167396469337)
                    ·
                      rfl

theorem cell22_1689746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1689746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689746 prefixEnd_1689746 := by exact prefixLift 1689746
  have htrace : WordTrace (prefixWord ++ tailWord_1689746) baseStart_1689746 baseEnd_1689746 := by
    simpa [prefixWord, tailWord_1689746, baseEnd_1689746] using wordTrace_append hprefix tailTrace_1689746
  have hstable : (prefixWord ++ tailWord_1689746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689746).length < 2 ^ (prefixWord ++ tailWord_1689746).sum := by decide
  have hdescent : baseEnd_1689746 < baseStart_1689746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689806 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1689806 : Nat := 118140960795 + 1689806 * 2 ^ 59
def prefixEnd_1689806 : Nat := 4983230072969 + 3 ^ 40 * 1689806 * 2
def baseEnd_1689806 : Nat := 192818375744782413323051

theorem tailTrace_1689806 : CollatzResearch.WordTrace tailWord_1689806 prefixEnd_1689806 192818375744782413323051 := by
  unfold tailWord_1689806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704036014516116591702159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41088192077419288489078181 7704036014516116591702159)
  ·
    refine ⟨11556054021774174887553239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7704036014516116591702159 11556054021774174887553239)
    ·
      refine ⟨17334081032661262331329859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11556054021774174887553239 17334081032661262331329859)
      ·
        refine ⟨26001121548991893496994789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17334081032661262331329859 26001121548991893496994789)
        ·
          refine ⟨4875210290435980030686523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26001121548991893496994789 4875210290435980030686523)
          ·
            refine ⟨7312815435653970046029785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875210290435980030686523 7312815435653970046029785)
            ·
              refine ⟨5484611576740477534522339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312815435653970046029785 5484611576740477534522339)
              ·
                refine ⟨8226917365110716301783509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484611576740477534522339 8226917365110716301783509)
                ·
                  refine ⟨192818375744782413323051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8226917365110716301783509 192818375744782413323051)
                  ·
                    rfl

theorem cell22_1689806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1689806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689806 prefixEnd_1689806 := by exact prefixLift 1689806
  have htrace : WordTrace (prefixWord ++ tailWord_1689806) baseStart_1689806 baseEnd_1689806 := by
    simpa [prefixWord, tailWord_1689806, baseEnd_1689806] using wordTrace_append hprefix tailTrace_1689806
  have hstable : (prefixWord ++ tailWord_1689806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689806).length < 2 ^ (prefixWord ++ tailWord_1689806).sum := by decide
  have hdescent : baseEnd_1689806 < baseStart_1689806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689810 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1689810 : Nat := 118140960795 + 1689810 * 2 ^ 59
def prefixEnd_1689810 : Nat := 4983230072969 + 3 ^ 40 * 1689810 * 2
def baseEnd_1689810 : Nat := 578456496516092562869141

theorem tailTrace_1689810 : CollatzResearch.WordTrace tailWord_1689810 prefixEnd_1689810 578456496516092562869141 := by
  unfold tailWord_1689810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408108502028610354190721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41088289338742960944508589 15408108502028610354190721)
  ·
    refine ⟨11556081376521457765643041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15408108502028610354190721 11556081376521457765643041)
    ·
      refine ⟨8667061032391093324232281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11556081376521457765643041 8667061032391093324232281)
      ·
        refine ⟨6500295774293319993174211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8667061032391093324232281 6500295774293319993174211)
        ·
          refine ⟨9750443661439979989761317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500295774293319993174211 9750443661439979989761317)
          ·
            refine ⟨1828208186519996248080247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9750443661439979989761317 1828208186519996248080247)
            ·
              refine ⟨2742312279779994372120371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828208186519996248080247 2742312279779994372120371)
              ·
                refine ⟨4113468419669991558180557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742312279779994372120371 4113468419669991558180557)
                ·
                  refine ⟨1542550657376246834317709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4113468419669991558180557 1542550657376246834317709)
                  ·
                    refine ⟨578456496516092562869141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542550657376246834317709 578456496516092562869141)
                    ·
                      rfl

theorem cell22_1689810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1689810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689810 prefixEnd_1689810 := by exact prefixLift 1689810
  have htrace : WordTrace (prefixWord ++ tailWord_1689810) baseStart_1689810 baseEnd_1689810 := by
    simpa [prefixWord, tailWord_1689810, baseEnd_1689810] using wordTrace_append hprefix tailTrace_1689810
  have hstable : (prefixWord ++ tailWord_1689810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689810).length < 2 ^ (prefixWord ++ tailWord_1689810).sum := by decide
  have hdescent : baseEnd_1689810 < baseStart_1689810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689836 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_1689836 : Nat := 118140960795 + 1689836 * 2 ^ 59
def prefixEnd_1689836 : Nat := 4983230072969 + 3 ^ 40 * 1689836 * 2
def baseEnd_1689836 : Nat := 578465396847437161719061

theorem tailTrace_1689836 : CollatzResearch.WordTrace tailWord_1689836 prefixEnd_1689836 578465396847437161719061 := by
  unfold tailWord_1689836
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816691153010123928604681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41088921537346831904806241 30816691153010123928604681)
  ·
    refine ⟨23112518364757592946453511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30816691153010123928604681 23112518364757592946453511)
    ·
      refine ⟨34668777547136389419680267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112518364757592946453511 34668777547136389419680267)
      ·
        refine ⟨52003166320704584129520401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34668777547136389419680267 52003166320704584129520401)
        ·
          refine ⟨39002374740528438097140301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52003166320704584129520401 39002374740528438097140301)
          ·
            refine ⟨14625890527698164286427613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39002374740528438097140301 14625890527698164286427613)
            ·
              refine ⟨5484708947886811607410355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14625890527698164286427613 5484708947886811607410355)
              ·
                refine ⟨8227063421830217411115533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484708947886811607410355 8227063421830217411115533)
                ·
                  refine ⟨3085148783186331529168325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8227063421830217411115533 3085148783186331529168325)
                  ·
                    refine ⟨578465396847437161719061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085148783186331529168325 578465396847437161719061)
                    ·
                      rfl

theorem cell22_1689836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_1689836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689836 prefixEnd_1689836 := by exact prefixLift 1689836
  have htrace : WordTrace (prefixWord ++ tailWord_1689836) baseStart_1689836 baseEnd_1689836 := by
    simpa [prefixWord, tailWord_1689836, baseEnd_1689836] using wordTrace_append hprefix tailTrace_1689836
  have hstable : (prefixWord ++ tailWord_1689836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689836).length < 2 ^ (prefixWord ++ tailWord_1689836).sum := by decide
  have hdescent : baseEnd_1689836 < baseStart_1689836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689868 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_1689868 : Nat := 118140960795 + 1689868 * 2 ^ 59
def prefixEnd_1689868 : Nat := 4983230072969 + 3 ^ 40 * 1689868 * 2
def baseEnd_1689868 : Nat := 192825450367133248306321

theorem tailTrace_1689868 : CollatzResearch.WordTrace tailWord_1689868 prefixEnd_1689868 192825450367133248306321 := by
  unfold tailWord_1689868
  simp only [CollatzResearch.WordTrace]
  refine ⟨30817274720952158661187129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41089699627936211548249505 30817274720952158661187129)
  ·
    refine ⟨23112956040714118995890347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30817274720952158661187129 23112956040714118995890347)
    ·
      refine ⟨34669434061071178493835521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112956040714118995890347 34669434061071178493835521)
      ·
        refine ⟨26002075545803383870376641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34669434061071178493835521 26002075545803383870376641)
        ·
          refine ⟨19501556659352537902782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26002075545803383870376641 19501556659352537902782481)
          ·
            refine ⟨14626167494514403427086861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19501556659352537902782481 14626167494514403427086861)
            ·
              refine ⟨5484812810442901285157573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14626167494514403427086861 5484812810442901285157573)
              ·
                refine ⟨1028402401958043990967045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5484812810442901285157573 1028402401958043990967045)
                ·
                  refine ⟨192825450367133248306321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028402401958043990967045 192825450367133248306321)
                  ·
                    rfl

theorem cell22_1689868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_1689868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689868 prefixEnd_1689868 := by exact prefixLift 1689868
  have htrace : WordTrace (prefixWord ++ tailWord_1689868) baseStart_1689868 baseEnd_1689868 := by
    simpa [prefixWord, tailWord_1689868, baseEnd_1689868] using wordTrace_append hprefix tailTrace_1689868
  have hstable : (prefixWord ++ tailWord_1689868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689868).length < 2 ^ (prefixWord ++ tailWord_1689868).sum := by decide
  have hdescent : baseEnd_1689868 < baseStart_1689868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689883 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 2, 3]
def baseStart_1689883 : Nat := 118140960795 + 1689883 * 2 ^ 59
def prefixEnd_1689883 : Nat := 4983230072969 + 3 ^ 40 * 1689883 * 2
def baseEnd_1689883 : Nat := 578481485907944705793917

theorem tailTrace_1689883 : CollatzResearch.WordTrace tailWord_1689883 prefixEnd_1689883 578481485907944705793917 := by
  unfold tailWord_1689883
  simp only [CollatzResearch.WordTrace]
  refine ⟨61635096536849974884170303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41090064357899983256113535 61635096536849974884170303)
  ·
    refine ⟨92452644805274962326255455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61635096536849974884170303 92452644805274962326255455)
    ·
      refine ⟨138678967207912443489383183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92452644805274962326255455 138678967207912443489383183)
      ·
        refine ⟨208018450811868665234074775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138678967207912443489383183 208018450811868665234074775)
        ·
          refine ⟨312027676217802997851112163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208018450811868665234074775 312027676217802997851112163)
          ·
            refine ⟨468041514326704496776668245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312027676217802997851112163 468041514326704496776668245)
            ·
              refine ⟨5484861496016068321601581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 468041514326704496776668245 5484861496016068321601581)
              ·
                refine ⟨2056823061006025620600593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5484861496016068321601581 2056823061006025620600593)
                ·
                  refine ⟨1542617295754519215450445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056823061006025620600593 1542617295754519215450445)
                  ·
                    refine ⟨578481485907944705793917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542617295754519215450445 578481485907944705793917)
                    ·
                      rfl

theorem cell22_1689883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].length) (baseStart_1689883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689883 prefixEnd_1689883 := by exact prefixLift 1689883
  have htrace : WordTrace (prefixWord ++ tailWord_1689883) baseStart_1689883 baseEnd_1689883 := by
    simpa [prefixWord, tailWord_1689883, baseEnd_1689883] using wordTrace_append hprefix tailTrace_1689883
  have hstable : (prefixWord ++ tailWord_1689883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689883).length < 2 ^ (prefixWord ++ tailWord_1689883).sum := by decide
  have hdescent : baseEnd_1689883 < baseStart_1689883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689928 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_1689928 : Nat := 118140960795 + 1689928 * 2 ^ 59
def prefixEnd_1689928 : Nat := 4983230072969 + 3 ^ 40 * 1689928 * 2
def baseEnd_1689928 : Nat := 578496890327579588418779

theorem tailTrace_1689928 : CollatzResearch.WordTrace tailWord_1689928 prefixEnd_1689928 578496890327579588418779 := by
  unfold tailWord_1689928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30818368910843473784779219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41091158547791298379705625 30818368910843473784779219)
  ·
    refine ⟨46227553366265210677168829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30818368910843473784779219 46227553366265210677168829)
    ·
      refine ⟨17335332512349454003938311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46227553366265210677168829 17335332512349454003938311)
      ·
        refine ⟨26002998768524181005907467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335332512349454003938311 26002998768524181005907467)
        ·
          refine ⟨39004498152786271508861201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26002998768524181005907467 39004498152786271508861201)
          ·
            refine ⟨29253373614589703631645901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39004498152786271508861201 29253373614589703631645901)
            ·
              refine ⟨10970015105471138861867213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29253373614589703631645901 10970015105471138861867213)
              ·
                refine ⟨4113755664551677073200205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10970015105471138861867213 4113755664551677073200205)
                ·
                  refine ⟨1542658374206878902450077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4113755664551677073200205 1542658374206878902450077)
                  ·
                    refine ⟨578496890327579588418779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542658374206878902450077 578496890327579588418779)
                    ·
                      rfl

theorem cell22_1689928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_1689928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689928 prefixEnd_1689928 := by exact prefixLift 1689928
  have htrace : WordTrace (prefixWord ++ tailWord_1689928) baseStart_1689928 baseEnd_1689928 := by
    simpa [prefixWord, tailWord_1689928, baseEnd_1689928] using wordTrace_append hprefix tailTrace_1689928
  have hstable : (prefixWord ++ tailWord_1689928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689928).length < 2 ^ (prefixWord ++ tailWord_1689928).sum := by decide
  have hdescent : baseEnd_1689928 < baseStart_1689928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689988 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1689988 : Nat := 118140960795 + 1689988 * 2 ^ 59
def prefixEnd_1689988 : Nat := 4983230072969 + 3 ^ 40 * 1689988 * 2
def baseEnd_1689988 : Nat := 578517429553759431918595

theorem tailTrace_1689988 : CollatzResearch.WordTrace tailWord_1689988 prefixEnd_1689988 578517429553759431918595 := by
  unfold tailWord_1689988
  simp only [CollatzResearch.WordTrace]
  refine ⟨30819463100734788908371309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41092617467646385211161745 30819463100734788908371309)
  ·
    refine ⟨11557298662775545840639241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30819463100734788908371309 11557298662775545840639241)
    ·
      refine ⟨8667973997081659380479431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11557298662775545840639241 8667973997081659380479431)
      ·
        refine ⟨13001960995622489070719147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667973997081659380479431 13001960995622489070719147)
        ·
          refine ⟨19502941493433733606078721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001960995622489070719147 19502941493433733606078721)
          ·
            refine ⟨14627206120075300204559041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19502941493433733606078721 14627206120075300204559041)
            ·
              refine ⟨10970404590056475153419281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14627206120075300204559041 10970404590056475153419281)
              ·
                refine ⟨8227803442542356365064461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10970404590056475153419281 8227803442542356365064461)
                ·
                  refine ⟨3085426290953383636899173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8227803442542356365064461 3085426290953383636899173)
                  ·
                    refine ⟨578517429553759431918595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085426290953383636899173 578517429553759431918595)
                    ·
                      rfl

theorem cell22_1689988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1689988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1689988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1689988 prefixEnd_1689988 := by exact prefixLift 1689988
  have htrace : WordTrace (prefixWord ++ tailWord_1689988) baseStart_1689988 baseEnd_1689988 := by
    simpa [prefixWord, tailWord_1689988, baseEnd_1689988] using wordTrace_append hprefix tailTrace_1689988
  have hstable : (prefixWord ++ tailWord_1689988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689988).length < 2 ^ (prefixWord ++ tailWord_1689988).sum := by decide
  have hdescent : baseEnd_1689988 < baseStart_1689988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690037 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 4]
def baseStart_1690037 : Nat := 118140960795 + 1690037 * 2 ^ 59
def prefixEnd_1690037 : Nat := 4983230072969 + 3 ^ 40 * 1690037 * 2
def baseEnd_1690037 : Nat := 192844734418379879147815

theorem tailTrace_1690037 : CollatzResearch.WordTrace tailWord_1690037 prefixEnd_1690037 192844734418379879147815 := by
  unfold tailWord_1690037
  simp only [CollatzResearch.WordTrace]
  refine ⟨61640713378292059185276365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41093808918861372790184243 61640713378292059185276365)
  ·
    refine ⟨23115267516859522194478637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61640713378292059185276365 23115267516859522194478637)
    ·
      refine ⟨8668225318822320822929489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23115267516859522194478637 8668225318822320822929489)
      ·
        refine ⟨6501168989116740617197117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8668225318822320822929489 6501168989116740617197117)
        ·
          refine ⟨2437938370918777731448919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6501168989116740617197117 2437938370918777731448919)
          ·
            refine ⟨3656907556378166597173379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437938370918777731448919 3656907556378166597173379)
            ·
              refine ⟨5485361334567249895760069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656907556378166597173379 5485361334567249895760069)
              ·
                refine ⟨1028505250231359355455013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5485361334567249895760069 1028505250231359355455013)
                ·
                  refine ⟨192844734418379879147815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028505250231359355455013 192844734418379879147815)
                  ·
                    rfl

theorem cell22_1690037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_1690037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690037 prefixEnd_1690037 := by exact prefixLift 1690037
  have htrace : WordTrace (prefixWord ++ tailWord_1690037) baseStart_1690037 baseEnd_1690037 := by
    simpa [prefixWord, tailWord_1690037, baseEnd_1690037] using wordTrace_append hprefix tailTrace_1690037
  have hstable : (prefixWord ++ tailWord_1690037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690037).length < 2 ^ (prefixWord ++ tailWord_1690037).sum := by decide
  have hdescent : baseEnd_1690037 < baseStart_1690037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690052 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1690052 : Nat := 118140960795 + 1690052 * 2 ^ 59
def prefixEnd_1690052 : Nat := 4983230072969 + 3 ^ 40 * 1690052 * 2
def baseEnd_1690052 : Nat := 578539338061684598318399

theorem tailTrace_1690052 : CollatzResearch.WordTrace tailWord_1690052 prefixEnd_1690052 578539338061684598318399 := by
  unfold tailWord_1690052
  simp only [CollatzResearch.WordTrace]
  refine ⟨30820630236618858373536205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41094173648825144498048273 30820630236618858373536205)
  ·
    refine ⟨11557736338732071890076077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30820630236618858373536205 11557736338732071890076077)
    ·
      refine ⟨4334151127024526958778529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11557736338732071890076077 4334151127024526958778529)
      ·
        refine ⟨3250613345268395219083897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4334151127024526958778529 3250613345268395219083897)
        ·
          refine ⟨2437960008951296414312923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3250613345268395219083897 2437960008951296414312923)
          ·
            refine ⟨3656940013426944621469385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437960008951296414312923 3656940013426944621469385)
            ·
              refine ⟨2742705010070208466102039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656940013426944621469385 2742705010070208466102039)
              ·
                refine ⟨4114057515105312699153059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742705010070208466102039 4114057515105312699153059)
                ·
                  refine ⟨6171086272657969048729589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114057515105312699153059 6171086272657969048729589)
                  ·
                    refine ⟨578539338061684598318399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6171086272657969048729589 578539338061684598318399)
                    ·
                      rfl

theorem cell22_1690052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1690052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690052 prefixEnd_1690052 := by exact prefixLift 1690052
  have htrace : WordTrace (prefixWord ++ tailWord_1690052) baseStart_1690052 baseEnd_1690052 := by
    simpa [prefixWord, tailWord_1690052, baseEnd_1690052] using wordTrace_append hprefix tailTrace_1690052
  have hstable : (prefixWord ++ tailWord_1690052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690052).length < 2 ^ (prefixWord ++ tailWord_1690052).sum := by decide
  have hdescent : baseEnd_1690052 < baseStart_1690052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690082 : List Nat := [3, 3, 3, 2, 1, 1, 9]
def baseStart_1690082 : Nat := 118140960795 + 1690082 * 2 ^ 59
def prefixEnd_1690082 : Nat := 4983230072969 + 3 ^ 40 * 1690082 * 2
def baseEnd_1690082 : Nat := 21427763247213871113641

theorem tailTrace_1690082 : CollatzResearch.WordTrace tailWord_1690082 prefixEnd_1690082 21427763247213871113641 := by
  unfold tailWord_1690082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410588665782257967666125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41094903108752687913776333 15410588665782257967666125)
  ·
    refine ⟨5778970749668346737874797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15410588665782257967666125 5778970749668346737874797)
    ·
      refine ⟨2167114031125630026703049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5778970749668346737874797 2167114031125630026703049)
      ·
        refine ⟨1625335523344222520027287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167114031125630026703049 1625335523344222520027287)
        ·
          refine ⟨2438003285016333780040931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625335523344222520027287 2438003285016333780040931)
          ·
            refine ⟨3657004927524500670061397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438003285016333780040931 3657004927524500670061397)
            ·
              refine ⟨21427763247213871113641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3657004927524500670061397 21427763247213871113641)
              ·
                rfl

theorem cell22_1690082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 9].length) (baseStart_1690082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690082 prefixEnd_1690082 := by exact prefixLift 1690082
  have htrace : WordTrace (prefixWord ++ tailWord_1690082) baseStart_1690082 baseEnd_1690082 := by
    simpa [prefixWord, tailWord_1690082, baseEnd_1690082] using wordTrace_append hprefix tailTrace_1690082
  have hstable : (prefixWord ++ tailWord_1690082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690082).length < 2 ^ (prefixWord ++ tailWord_1690082).sum := by decide
  have hdescent : baseEnd_1690082 < baseStart_1690082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690097 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_1690097 : Nat := 118140960795 + 1690097 * 2 ^ 59
def prefixEnd_1690097 : Nat := 4983230072969 + 3 ^ 40 * 1690097 * 2
def baseEnd_1690097 : Nat := 578554742481319480943261

theorem tailTrace_1690097 : CollatzResearch.WordTrace tailWord_1690097 prefixEnd_1690097 578554742481319480943261 := by
  unfold tailWord_1690097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61642901758074689432460545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41095267838716459621640363 61642901758074689432460545)
  ·
    refine ⟨46232176318556017074345409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61642901758074689432460545 46232176318556017074345409)
    ·
      refine ⟨34674132238917012805759057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46232176318556017074345409 34674132238917012805759057)
      ·
        refine ⟨26005599179187759604319293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34674132238917012805759057 26005599179187759604319293)
        ·
          refine ⟨9752099692195409851619735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26005599179187759604319293 9752099692195409851619735)
          ·
            refine ⟨14628149538293114777429603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752099692195409851619735 14628149538293114777429603)
            ·
              refine ⟨21942224307439672166144405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628149538293114777429603 21942224307439672166144405)
              ·
                refine ⟨1028541764411234632788019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21942224307439672166144405 1028541764411234632788019)
                ·
                  refine ⟨1542812646616851949182029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028541764411234632788019 1542812646616851949182029)
                  ·
                    refine ⟨578554742481319480943261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542812646616851949182029 578554742481319480943261)
                    ·
                      rfl

theorem cell22_1690097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_1690097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690097 prefixEnd_1690097 := by exact prefixLift 1690097
  have htrace : WordTrace (prefixWord ++ tailWord_1690097) baseStart_1690097 baseEnd_1690097 := by
    simpa [prefixWord, tailWord_1690097, baseEnd_1690097] using wordTrace_append hprefix tailTrace_1690097
  have hstable : (prefixWord ++ tailWord_1690097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690097).length < 2 ^ (prefixWord ++ tailWord_1690097).sum := by decide
  have hdescent : baseEnd_1690097 < baseStart_1690097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690138 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1690138 : Nat := 118140960795 + 1690138 * 2 ^ 59
def prefixEnd_1690138 : Nat := 4983230072969 + 3 ^ 40 * 1690138 * 2
def baseEnd_1690138 : Nat := 192856259206403013556045

theorem tailTrace_1690138 : CollatzResearch.WordTrace tailWord_1690138 prefixEnd_1690138 192856259206403013556045 := by
  unfold tailWord_1690138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411099287731538358675767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41096264767284102289802045 15411099287731538358675767)
  ·
    refine ⟨23116648931597307538013651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15411099287731538358675767 23116648931597307538013651)
    ·
      refine ⟨34674973397395961307020477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116648931597307538013651 34674973397395961307020477)
      ·
        refine ⟨13003115024023485490132679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34674973397395961307020477 13003115024023485490132679)
        ·
          refine ⟨19504672536035228235199019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13003115024023485490132679 19504672536035228235199019)
          ·
            refine ⟨29257008804052842352798529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504672536035228235199019 29257008804052842352798529)
            ·
              refine ⟨21942756603039631764598897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29257008804052842352798529 21942756603039631764598897)
              ·
                refine ⟨16457067452279723823449173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21942756603039631764598897 16457067452279723823449173)
                ·
                  refine ⟨192856259206403013556045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16457067452279723823449173 192856259206403013556045)
                  ·
                    rfl

theorem cell22_1690138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1690138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690138 prefixEnd_1690138 := by exact prefixLift 1690138
  have htrace : WordTrace (prefixWord ++ tailWord_1690138) baseStart_1690138 baseEnd_1690138 := by
    simpa [prefixWord, tailWord_1690138, baseEnd_1690138] using wordTrace_append hprefix tailTrace_1690138
  have hstable : (prefixWord ++ tailWord_1690138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690138).length < 2 ^ (prefixWord ++ tailWord_1690138).sum := by decide
  have hdescent : baseEnd_1690138 < baseStart_1690138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690148 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1690148 : Nat := 118140960795 + 1690148 * 2 ^ 59
def prefixEnd_1690148 : Nat := 4983230072969 + 3 ^ 40 * 1690148 * 2
def baseEnd_1690148 : Nat := 578572200823572347918105

theorem tailTrace_1690148 : CollatzResearch.WordTrace tailWord_1690148 prefixEnd_1690148 578572200823572347918105 := by
  unfold tailWord_1690148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822380940444962571283549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41096507920593283428378065 30822380940444962571283549)
  ·
    refine ⟨11558392852666860964231331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30822380940444962571283549 11558392852666860964231331)
    ·
      refine ⟨17337589279000291446346997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11558392852666860964231331 17337589279000291446346997)
      ·
        refine ⟨1625398994906277323095031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17337589279000291446346997 1625398994906277323095031)
        ·
          refine ⟨2438098492359415984642547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625398994906277323095031 2438098492359415984642547)
          ·
            refine ⟨3657147738539123976963821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438098492359415984642547 3657147738539123976963821)
            ·
              refine ⟨1371430401952171491361433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3657147738539123976963821 1371430401952171491361433)
              ·
                refine ⟨1028572801464128618521075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371430401952171491361433 1028572801464128618521075)
                ·
                  refine ⟨1542859202196192927781613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028572801464128618521075 1542859202196192927781613)
                  ·
                    refine ⟨578572200823572347918105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542859202196192927781613 578572200823572347918105)
                    ·
                      rfl

theorem cell22_1690148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1690148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690148 prefixEnd_1690148 := by exact prefixLift 1690148
  have htrace : WordTrace (prefixWord ++ tailWord_1690148) baseStart_1690148 baseEnd_1690148 := by
    simpa [prefixWord, tailWord_1690148, baseEnd_1690148] using wordTrace_append hprefix tailTrace_1690148
  have hstable : (prefixWord ++ tailWord_1690148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690148).length < 2 ^ (prefixWord ++ tailWord_1690148).sum := by decide
  have hdescent : baseEnd_1690148 < baseStart_1690148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690155 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 4]
def baseStart_1690155 : Nat := 118140960795 + 1690155 * 2 ^ 59
def prefixEnd_1690155 : Nat := 4983230072969 + 3 ^ 40 * 1690155 * 2
def baseEnd_1690155 : Nat := 192858199022208887664361

theorem tailTrace_1690155 : CollatzResearch.WordTrace tailWord_1690155 prefixEnd_1690155 192858199022208887664361 := by
  unfold tailWord_1690155
  simp only [CollatzResearch.WordTrace]
  refine ⟨61645017191864565338071919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41096678127909710225381279 61645017191864565338071919)
  ·
    refine ⟨92467525787796848007107879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61645017191864565338071919 92467525787796848007107879)
    ·
      refine ⟨138701288681695272010661819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92467525787796848007107879 138701288681695272010661819)
      ·
        refine ⟨208051933022542908015992729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138701288681695272010661819 208051933022542908015992729)
        ·
          refine ⟨156038949766907181011994547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208051933022542908015992729 156038949766907181011994547)
          ·
            refine ⟨234058424650360771517991821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156038949766907181011994547 234058424650360771517991821)
            ·
              refine ⟨87771909243885289319246933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234058424650360771517991821 87771909243885289319246933)
              ·
                refine ⟨1028577061451780734209925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87771909243885289319246933 1028577061451780734209925)
                ·
                  refine ⟨192858199022208887664361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1028577061451780734209925 192858199022208887664361)
                  ·
                    rfl

theorem cell22_1690155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 4].length) (baseStart_1690155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690155 prefixEnd_1690155 := by exact prefixLift 1690155
  have htrace : WordTrace (prefixWord ++ tailWord_1690155) baseStart_1690155 baseEnd_1690155 := by
    simpa [prefixWord, tailWord_1690155, baseEnd_1690155] using wordTrace_append hprefix tailTrace_1690155
  have hstable : (prefixWord ++ tailWord_1690155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690155).length < 2 ^ (prefixWord ++ tailWord_1690155).sum := by decide
  have hdescent : baseEnd_1690155 < baseStart_1690155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690174 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1690174 : Nat := 118140960795 + 1690174 * 2 ^ 59
def prefixEnd_1690174 : Nat := 4983230072969 + 3 ^ 40 * 1690174 * 2
def baseEnd_1690174 : Nat := 578581101154916946768025

theorem tailTrace_1690174 : CollatzResearch.WordTrace tailWord_1690174 prefixEnd_1690174 578581101154916946768025 := by
  unfold tailWord_1690174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705713772349466447876697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41097140119197154388675717 7705713772349466447876697)
  ·
    refine ⟨5779285329262099835907523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7705713772349466447876697 5779285329262099835907523)
    ·
      refine ⟨8668927993893149753861285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779285329262099835907523 8668927993893149753861285)
      ·
        refine ⟨1625423998854965578848991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8668927993893149753861285 1625423998854965578848991)
        ·
          refine ⟨2438135998282448368273487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625423998854965578848991 2438135998282448368273487)
          ·
            refine ⟨3657203997423672552410231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438135998282448368273487 3657203997423672552410231)
            ·
              refine ⟨5485805996135508828615347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657203997423672552410231 5485805996135508828615347)
              ·
                refine ⟨8228708994203263242923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485805996135508828615347 8228708994203263242923021)
                ·
                  refine ⟨3085765872826223716096133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8228708994203263242923021 3085765872826223716096133)
                  ·
                    refine ⟨578581101154916946768025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085765872826223716096133 578581101154916946768025)
                    ·
                      rfl

theorem cell22_1690174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1690174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690174 prefixEnd_1690174 := by exact prefixLift 1690174
  have htrace : WordTrace (prefixWord ++ tailWord_1690174) baseStart_1690174 baseEnd_1690174 := by
    simpa [prefixWord, tailWord_1690174, baseEnd_1690174] using wordTrace_append hprefix tailTrace_1690174
  have hstable : (prefixWord ++ tailWord_1690174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690174).length < 2 ^ (prefixWord ++ tailWord_1690174).sum := by decide
  have hdescent : baseEnd_1690174 < baseStart_1690174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690242 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1690242 : Nat := 118140960795 + 1690242 * 2 ^ 59
def prefixEnd_1690242 : Nat := 4983230072969 + 3 ^ 40 * 1690242 * 2
def baseEnd_1690242 : Nat := 578604378944587436067817

theorem tailTrace_1690242 : CollatzResearch.WordTrace tailWord_1690242 prefixEnd_1690242 578604378944587436067817 := by
  unfold tailWord_1690242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412047585637344799122245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41098793561699586130992653 15412047585637344799122245)
  ·
    refine ⟨2889758922307002149835421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15412047585637344799122245 2889758922307002149835421)
    ·
      refine ⟨1083659595865125806188283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2889758922307002149835421 1083659595865125806188283)
      ·
        refine ⟨1625489393797688709282425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083659595865125806188283 1625489393797688709282425)
        ·
          refine ⟨1219117045348266531961819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625489393797688709282425 1219117045348266531961819)
          ·
            refine ⟨1828675568022399797942729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219117045348266531961819 1828675568022399797942729)
            ·
              refine ⟨1371506676016799848457047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828675568022399797942729 1371506676016799848457047)
              ·
                refine ⟨2057260014025199772685571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371506676016799848457047 2057260014025199772685571)
                ·
                  refine ⟨3085890021037799659028357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057260014025199772685571 3085890021037799659028357)
                  ·
                    refine ⟨578604378944587436067817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085890021037799659028357 578604378944587436067817)
                    ·
                      rfl

theorem cell22_1690242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1690242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690242 prefixEnd_1690242 := by exact prefixLift 1690242
  have htrace : WordTrace (prefixWord ++ tailWord_1690242) baseStart_1690242 baseEnd_1690242 := by
    simpa [prefixWord, tailWord_1690242, baseEnd_1690242] using wordTrace_append hprefix tailTrace_1690242
  have hstable : (prefixWord ++ tailWord_1690242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690242).length < 2 ^ (prefixWord ++ tailWord_1690242).sum := by decide
  have hdescent : baseEnd_1690242 < baseStart_1690242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690266 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1690266 : Nat := 118140960795 + 1690266 * 2 ^ 59
def prefixEnd_1690266 : Nat := 4983230072969 + 3 ^ 40 * 1690266 * 2
def baseEnd_1690266 : Nat := 578612594635059373467743

theorem tailTrace_1690266 : CollatzResearch.WordTrace tailWord_1690266 prefixEnd_1690266 578612594635059373467743 := by
  unfold tailWord_1690266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412266423615607823840663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41099377129641620863575101 15412266423615607823840663)
  ·
    refine ⟨23118399635423411735760995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412266423615607823840663 23118399635423411735760995)
    ·
      refine ⟨34677599453135117603641493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23118399635423411735760995 34677599453135117603641493)
      ·
        refine ⟨1625512474365708637670695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34677599453135117603641493 1625512474365708637670695)
        ·
          refine ⟨2438268711548562956506043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625512474365708637670695 2438268711548562956506043)
          ·
            refine ⟨3657403067322844434759065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438268711548562956506043 3657403067322844434759065)
            ·
              refine ⟨2743052300492133326069299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657403067322844434759065 2743052300492133326069299)
              ·
                refine ⟨4114578450738199989103949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743052300492133326069299 4114578450738199989103949)
                ·
                  refine ⟨1542966919026824995913981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4114578450738199989103949 1542966919026824995913981)
                  ·
                    refine ⟨578612594635059373467743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542966919026824995913981 578612594635059373467743)
                    ·
                      rfl

theorem cell22_1690266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1690266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690266 prefixEnd_1690266 := by exact prefixLift 1690266
  have htrace : WordTrace (prefixWord ++ tailWord_1690266) baseStart_1690266 baseEnd_1690266 := by
    simpa [prefixWord, tailWord_1690266, baseEnd_1690266] using wordTrace_append hprefix tailTrace_1690266
  have hstable : (prefixWord ++ tailWord_1690266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690266).length < 2 ^ (prefixWord ++ tailWord_1690266).sum := by decide
  have hdescent : baseEnd_1690266 < baseStart_1690266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690275 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_1690275 : Nat := 118140960795 + 1690275 * 2 ^ 59
def prefixEnd_1690275 : Nat := 4983230072969 + 3 ^ 40 * 1690275 * 2
def baseEnd_1690275 : Nat := 578615675518986349992715

theorem tailTrace_1690275 : CollatzResearch.WordTrace tailWord_1690275 prefixEnd_1690275 578615675518986349992715 := by
  unfold tailWord_1690275
  simp only [CollatzResearch.WordTrace]
  refine ⟨61649393951429825832440279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41099595967619883888293519 61649393951429825832440279)
  ·
    refine ⟨92474090927144738748660419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61649393951429825832440279 92474090927144738748660419)
    ·
      refine ⟨138711136390717108122990629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92474090927144738748660419 138711136390717108122990629)
      ·
        refine ⟨26008338073259457773060743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138711136390717108122990629 26008338073259457773060743)
        ·
          refine ⟨39012507109889186659591115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26008338073259457773060743 39012507109889186659591115)
          ·
            refine ⟨58518760664833779989386673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39012507109889186659591115 58518760664833779989386673)
            ·
              refine ⟨43889070498625334992040005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58518760664833779989386673 43889070498625334992040005)
              ·
                refine ⟨8229200718492250311007501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43889070498625334992040005 8229200718492250311007501)
                ·
                  refine ⟨3085950269434593866627813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8229200718492250311007501 3085950269434593866627813)
                  ·
                    refine ⟨578615675518986349992715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085950269434593866627813 578615675518986349992715)
                    ·
                      rfl

theorem cell22_1690275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_1690275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690275 prefixEnd_1690275 := by exact prefixLift 1690275
  have htrace : WordTrace (prefixWord ++ tailWord_1690275) baseStart_1690275 baseEnd_1690275 := by
    simpa [prefixWord, tailWord_1690275, baseEnd_1690275] using wordTrace_append hprefix tailTrace_1690275
  have hstable : (prefixWord ++ tailWord_1690275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690275).length < 2 ^ (prefixWord ++ tailWord_1690275).sum := by decide
  have hdescent : baseEnd_1690275 < baseStart_1690275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690335 : List Nat := [1, 1, 2, 3, 2, 3, 1, 9]
def baseStart_1690335 : Nat := 118140960795 + 1690335 * 2 ^ 59
def prefixEnd_1690335 : Nat := 4983230072969 + 3 ^ 40 * 1690335 * 2
def baseEnd_1690335 : Nat := 64292912749462910388059

theorem tailTrace_1690335 : CollatzResearch.WordTrace tailWord_1690335 prefixEnd_1690335 64292912749462910388059 := by
  unfold tailWord_1690335
  simp only [CollatzResearch.WordTrace]
  refine ⟨61651582331212456079624459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41101054887474970719749639 61651582331212456079624459)
  ·
    refine ⟨92477373496818684119436689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61651582331212456079624459 92477373496818684119436689)
    ·
      refine ⟨69358030122614013089577517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92477373496818684119436689 69358030122614013089577517)
      ·
        refine ⟨26009261295980254908591569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69358030122614013089577517 26009261295980254908591569)
        ·
          refine ⟨19506945971985191181443677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26009261295980254908591569 19506945971985191181443677)
          ·
            refine ⟨7315104739494446693041379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19506945971985191181443677 7315104739494446693041379)
            ·
              refine ⟨10972657109241670039562069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315104739494446693041379 10972657109241670039562069)
              ·
                refine ⟨64292912749462910388059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10972657109241670039562069 64292912749462910388059)
                ·
                  rfl

theorem cell22_1690335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 9].length) (baseStart_1690335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690335 prefixEnd_1690335 := by exact prefixLift 1690335
  have htrace : WordTrace (prefixWord ++ tailWord_1690335) baseStart_1690335 baseEnd_1690335 := by
    simpa [prefixWord, tailWord_1690335, baseEnd_1690335] using wordTrace_append hprefix tailTrace_1690335
  have hstable : (prefixWord ++ tailWord_1690335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690335).length < 2 ^ (prefixWord ++ tailWord_1690335).sum := by decide
  have hdescent : baseEnd_1690335 < baseStart_1690335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690354 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1690354 : Nat := 118140960795 + 1690354 * 2 ^ 59
def prefixEnd_1690354 : Nat := 4983230072969 + 3 ^ 40 * 1690354 * 2
def baseEnd_1690354 : Nat := 578642718833456477267473

theorem tailTrace_1690354 : CollatzResearch.WordTrace tailWord_1690354 prefixEnd_1690354 578642718833456477267473 := by
  unfold tailWord_1690354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413068829535905581141529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41101516878762414883044077 15413068829535905581141529)
  ·
    refine ⟨11559801622151929185856147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15413068829535905581141529 11559801622151929185856147)
    ·
      refine ⟨17339702433227893778784221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559801622151929185856147 17339702433227893778784221)
      ·
        refine ⟨6502388412460460167044083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17339702433227893778784221 6502388412460460167044083)
        ·
          refine ⟨9753582618690690250566125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502388412460460167044083 9753582618690690250566125)
          ·
            refine ⟨3657593482009008843962297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9753582618690690250566125 3657593482009008843962297)
            ·
              refine ⟨2743195111506756632971723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657593482009008843962297 2743195111506756632971723)
              ·
                refine ⟨4114792667260134949457585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743195111506756632971723 4114792667260134949457585)
                ·
                  refine ⟨3086094500445101212093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4114792667260134949457585 3086094500445101212093189)
                  ·
                    refine ⟨578642718833456477267473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086094500445101212093189 578642718833456477267473)
                    ·
                      rfl

theorem cell22_1690354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1690354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690354 prefixEnd_1690354 := by exact prefixLift 1690354
  have htrace : WordTrace (prefixWord ++ tailWord_1690354) baseStart_1690354 baseEnd_1690354 := by
    simpa [prefixWord, tailWord_1690354, baseEnd_1690354] using wordTrace_append hprefix tailTrace_1690354
  have hstable : (prefixWord ++ tailWord_1690354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690354).length < 2 ^ (prefixWord ++ tailWord_1690354).sum := by decide
  have hdescent : baseEnd_1690354 < baseStart_1690354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690386 : List Nat := [3, 2, 4, 1, 2, 2, 1, 7]
def baseStart_1690386 : Nat := 118140960795 + 1690386 * 2 ^ 59
def prefixEnd_1690386 : Nat := 4983230072969 + 3 ^ 40 * 1690386 * 2
def baseEnd_1690386 : Nat := 64294852565268784496375

theorem tailTrace_1690386 : CollatzResearch.WordTrace tailWord_1690386 prefixEnd_1690386 64294852565268784496375 := by
  unfold tailWord_1690386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413360613506922947432753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41102294969351794526487341 15413360613506922947432753)
  ·
    refine ⟨11560020460130192210574565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15413360613506922947432753 11560020460130192210574565)
    ·
      refine ⟨2167503836274411039482731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11560020460130192210574565 2167503836274411039482731)
      ·
        refine ⟨3251255754411616559224097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167503836274411039482731 3251255754411616559224097)
        ·
          refine ⟨2438441815808712419418073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251255754411616559224097 2438441815808712419418073)
          ·
            refine ⟨1828831361856534314563555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438441815808712419418073 1828831361856534314563555)
            ·
              refine ⟨2743247042784801471845333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828831361856534314563555 2743247042784801471845333)
              ·
                refine ⟨64294852565268784496375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2743247042784801471845333 64294852565268784496375)
                ·
                  rfl

theorem cell22_1690386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_1690386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690386 prefixEnd_1690386 := by exact prefixLift 1690386
  have htrace : WordTrace (prefixWord ++ tailWord_1690386) baseStart_1690386 baseEnd_1690386 := by
    simpa [prefixWord, tailWord_1690386, baseEnd_1690386] using wordTrace_append hprefix tailTrace_1690386
  have hstable : (prefixWord ++ tailWord_1690386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690386).length < 2 ^ (prefixWord ++ tailWord_1690386).sum := by decide
  have hdescent : baseEnd_1690386 < baseStart_1690386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690489 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1690489 : Nat := 118140960795 + 1690489 * 2 ^ 59
def prefixEnd_1690489 : Nat := 4983230072969 + 3 ^ 40 * 1690489 * 2
def baseEnd_1690489 : Nat := 578688932092361125142059

theorem tailTrace_1690489 : CollatzResearch.WordTrace tailWord_1690489 prefixEnd_1690489 578688932092361125142059 := by
  unfold tailWord_1690489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61657199172654540380730521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41104799448436360253820347 61657199172654540380730521)
  ·
    refine ⟨46242899379490905285547891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61657199172654540380730521 46242899379490905285547891)
    ·
      refine ⟨69364349069236357928321837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46242899379490905285547891 69364349069236357928321837)
      ·
        refine ⟨26011630900963634223120689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69364349069236357928321837 26011630900963634223120689)
        ·
          refine ⟨19508723175722725667340517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26011630900963634223120689 19508723175722725667340517)
          ·
            refine ⟨3657885595448011062626347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19508723175722725667340517 3657885595448011062626347)
            ·
              refine ⟨5486828393172016593939521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657885595448011062626347 5486828393172016593939521)
              ·
                refine ⟨4115121294879012445454641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486828393172016593939521 4115121294879012445454641)
                ·
                  refine ⟨3086340971159259334090981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4115121294879012445454641 3086340971159259334090981)
                  ·
                    refine ⟨578688932092361125142059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086340971159259334090981 578688932092361125142059)
                    ·
                      rfl

theorem cell22_1690489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1690489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690489 prefixEnd_1690489 := by exact prefixLift 1690489
  have htrace : WordTrace (prefixWord ++ tailWord_1690489) baseStart_1690489 baseEnd_1690489 := by
    simpa [prefixWord, tailWord_1690489, baseEnd_1690489] using wordTrace_append hprefix tailTrace_1690489
  have hstable : (prefixWord ++ tailWord_1690489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690489).length < 2 ^ (prefixWord ++ tailWord_1690489).sum := by decide
  have hdescent : baseEnd_1690489 < baseStart_1690489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690504 : List Nat := [2, 1, 3, 3, 2, 2, 2, 7]
def baseStart_1690504 : Nat := 118140960795 + 1690504 * 2 ^ 59
def prefixEnd_1690504 : Nat := 4983230072969 + 3 ^ 40 * 1690504 * 2
def baseEnd_1690504 : Nat := 64299340766545120668557

theorem tailTrace_1690504 : CollatzResearch.WordTrace tailWord_1690504 prefixEnd_1690504 64299340766545120668557 := by
  unfold tailWord_1690504
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828873133800098971263283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41105164178400131961684377 30828873133800098971263283)
  ·
    refine ⟨46243309700700148456894925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30828873133800098971263283 46243309700700148456894925)
    ·
      refine ⟨17341241137762555671335597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46243309700700148456894925 17341241137762555671335597)
      ·
        refine ⟨6502965426660958376750849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17341241137762555671335597 6502965426660958376750849)
        ·
          refine ⟨4877224069995718782563137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6502965426660958376750849 4877224069995718782563137)
          ·
            refine ⟨3657918052496789086922353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877224069995718782563137 3657918052496789086922353)
            ·
              refine ⟨2743438539372591815191765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657918052496789086922353 2743438539372591815191765)
              ·
                refine ⟨64299340766545120668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2743438539372591815191765 64299340766545120668557)
                ·
                  rfl

theorem cell22_1690504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_1690504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690504 prefixEnd_1690504 := by exact prefixLift 1690504
  have htrace : WordTrace (prefixWord ++ tailWord_1690504) baseStart_1690504 baseEnd_1690504 := by
    simpa [prefixWord, tailWord_1690504, baseEnd_1690504] using wordTrace_append hprefix tailTrace_1690504
  have hstable : (prefixWord ++ tailWord_1690504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690504).length < 2 ^ (prefixWord ++ tailWord_1690504).sum := by decide
  have hdescent : baseEnd_1690504 < baseStart_1690504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690519 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1690519 : Nat := 118140960795 + 1690519 * 2 ^ 59
def prefixEnd_1690519 : Nat := 4983230072969 + 3 ^ 40 * 1690519 * 2
def baseEnd_1690519 : Nat := 578699201705451046891967

theorem tailTrace_1690519 : CollatzResearch.WordTrace tailWord_1690519 prefixEnd_1690519 578699201705451046891967 := by
  unfold tailWord_1690519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61658293362545855504322611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41105528908363903669548407 61658293362545855504322611)
  ·
    refine ⟨92487440043818783256483917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61658293362545855504322611 92487440043818783256483917)
    ·
      refine ⟨34682790016432043721181469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92487440043818783256483917 34682790016432043721181469)
      ·
        refine ⟨13006046256162016395443051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34682790016432043721181469 13006046256162016395443051)
        ·
          refine ⟨19509069384243024593164577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006046256162016395443051 19509069384243024593164577)
          ·
            refine ⟨14631802038182268444873433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19509069384243024593164577 14631802038182268444873433)
            ·
              refine ⟨10973851528636701333655075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14631802038182268444873433 10973851528636701333655075)
              ·
                refine ⟨16460777292955052000482613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10973851528636701333655075 16460777292955052000482613)
                ·
                  refine ⟨1543197871214536125045245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16460777292955052000482613 1543197871214536125045245)
                  ·
                    refine ⟨578699201705451046891967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543197871214536125045245 578699201705451046891967)
                    ·
                      rfl

theorem cell22_1690519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1690519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690519 prefixEnd_1690519 := by exact prefixLift 1690519
  have htrace : WordTrace (prefixWord ++ tailWord_1690519) baseStart_1690519 baseEnd_1690519 := by
    simpa [prefixWord, tailWord_1690519, baseEnd_1690519] using wordTrace_append hprefix tailTrace_1690519
  have hstable : (prefixWord ++ tailWord_1690519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690519).length < 2 ^ (prefixWord ++ tailWord_1690519).sum := by decide
  have hdescent : baseEnd_1690519 < baseStart_1690519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690553 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_1690553 : Nat := 118140960795 + 1690553 * 2 ^ 59
def prefixEnd_1690553 : Nat := 4983230072969 + 3 ^ 40 * 1690553 * 2
def baseEnd_1690553 : Nat := 578710840600286291541863

theorem tailTrace_1690553 : CollatzResearch.WordTrace tailWord_1690553 prefixEnd_1690553 578710840600286291541863 := by
  unfold tailWord_1690553
  simp only [CollatzResearch.WordTrace]
  refine ⟨61659533444422679311060313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41106355629615119540706875 61659533444422679311060313)
  ·
    refine ⟨46244650083317009483295235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61659533444422679311060313 46244650083317009483295235)
    ·
      refine ⟨69366975124975514224942853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46244650083317009483295235 69366975124975514224942853)
      ·
        refine ⟨13006307835932908917176785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69366975124975514224942853 13006307835932908917176785)
        ·
          refine ⟨9754730876949681687882589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006307835932908917176785 9754730876949681687882589)
          ·
            refine ⟨3658024078856130632955971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9754730876949681687882589 3658024078856130632955971)
            ·
              refine ⟨5487036118284195949433957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658024078856130632955971 5487036118284195949433957)
              ·
                refine ⟨1028819272178286740518867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5487036118284195949433957 1028819272178286740518867)
                ·
                  refine ⟨1543228908267430110778301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028819272178286740518867 1543228908267430110778301)
                  ·
                    refine ⟨578710840600286291541863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543228908267430110778301 578710840600286291541863)
                    ·
                      rfl

theorem cell22_1690553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_1690553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690553 prefixEnd_1690553 := by exact prefixLift 1690553
  have htrace : WordTrace (prefixWord ++ tailWord_1690553) baseStart_1690553 baseEnd_1690553 := by
    simpa [prefixWord, tailWord_1690553, baseEnd_1690553] using wordTrace_append hprefix tailTrace_1690553
  have hstable : (prefixWord ++ tailWord_1690553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690553).length < 2 ^ (prefixWord ++ tailWord_1690553).sum := by decide
  have hdescent : baseEnd_1690553 < baseStart_1690553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690716 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1690716 : Nat := 118140960795 + 1690716 * 2 ^ 59
def prefixEnd_1690716 : Nat := 4983230072969 + 3 ^ 40 * 1690716 * 2
def baseEnd_1690716 : Nat := 578766638831408199716363

theorem tailTrace_1690716 : CollatzResearch.WordTrace tailWord_1690716 prefixEnd_1690716 578766638831408199716363 := by
  unfold tailWord_1690716
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832739271416079074622001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41110319028554772099496001 30832739271416079074622001)
  ·
    refine ⟨23124554453562059305966501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30832739271416079074622001 23124554453562059305966501)
    ·
      refine ⟨4335853960042886119868719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23124554453562059305966501 4335853960042886119868719)
      ·
        refine ⟨6503780940064329179803079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335853960042886119868719 6503780940064329179803079)
        ·
          refine ⟨9755671410096493769704619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503780940064329179803079 9755671410096493769704619)
          ·
            refine ⟨14633507115144740654556929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755671410096493769704619 14633507115144740654556929)
            ·
              refine ⟨10975130336358555490917697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14633507115144740654556929 10975130336358555490917697)
              ·
                refine ⟨8231347752268916618188273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10975130336358555490917697 8231347752268916618188273)
                ·
                  refine ⟨6173510814201687463641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231347752268916618188273 6173510814201687463641205)
                  ·
                    refine ⟨578766638831408199716363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6173510814201687463641205 578766638831408199716363)
                    ·
                      rfl

theorem cell22_1690716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1690716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690716 prefixEnd_1690716 := by exact prefixLift 1690716
  have htrace : WordTrace (prefixWord ++ tailWord_1690716) baseStart_1690716 baseEnd_1690716 := by
    simpa [prefixWord, tailWord_1690716, baseEnd_1690716] using wordTrace_append hprefix tailTrace_1690716
  have hstable : (prefixWord ++ tailWord_1690716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690716).length < 2 ^ (prefixWord ++ tailWord_1690716).sum := by decide
  have hdescent : baseEnd_1690716 < baseStart_1690716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690722 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1690722 : Nat := 118140960795 + 1690722 * 2 ^ 59
def prefixEnd_1690722 : Nat := 4983230072969 + 3 ^ 40 * 1690722 * 2
def baseEnd_1690722 : Nat := 578768692754026184066345

theorem tailTrace_1690722 : CollatzResearch.WordTrace tailWord_1690722 prefixEnd_1690722 578768692754026184066345 := by
  unfold tailWord_1690722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416424345202605293490605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41110464920540280782641613 15416424345202605293490605)
  ·
    refine ⟨5781159129450976985058977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15416424345202605293490605 5781159129450976985058977)
    ·
      refine ⟨4335869347088232738794233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5781159129450976985058977 4335869347088232738794233)
      ·
        refine ⟨3251902010316174554095675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4335869347088232738794233 3251902010316174554095675)
        ·
          refine ⟨4877853015474261831143513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251902010316174554095675 4877853015474261831143513)
          ·
            refine ⟨3658389761605696373357635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877853015474261831143513 3658389761605696373357635)
            ·
              refine ⟨5487584642408544560036453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658389761605696373357635 5487584642408544560036453)
              ·
                refine ⟨1028922120451602105006835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5487584642408544560036453 1028922120451602105006835)
                ·
                  refine ⟨1543383180677403157510253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028922120451602105006835 1543383180677403157510253)
                  ·
                    refine ⟨578768692754026184066345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543383180677403157510253 578768692754026184066345)
                    ·
                      rfl

theorem cell22_1690722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1690722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690722 prefixEnd_1690722 := by exact prefixLift 1690722
  have htrace : WordTrace (prefixWord ++ tailWord_1690722) baseStart_1690722 baseEnd_1690722 := by
    simpa [prefixWord, tailWord_1690722, baseEnd_1690722] using wordTrace_append hprefix tailTrace_1690722
  have hstable : (prefixWord ++ tailWord_1690722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690722).length < 2 ^ (prefixWord ++ tailWord_1690722).sum := by decide
  have hdescent : baseEnd_1690722 < baseStart_1690722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690761 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_1690761 : Nat := 118140960795 + 1690761 * 2 ^ 59
def prefixEnd_1690761 : Nat := 4983230072969 + 3 ^ 40 * 1690761 * 2
def baseEnd_1690761 : Nat := 578782043251043082341225

theorem tailTrace_1690761 : CollatzResearch.WordTrace tailWord_1690761 prefixEnd_1690761 578782043251043082341225 := by
  unfold tailWord_1690761
  simp only [CollatzResearch.WordTrace]
  refine ⟨61667119827669130834632137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41111413218446087223088091 61667119827669130834632137)
  ·
    refine ⟨46250339870751848125974103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61667119827669130834632137 46250339870751848125974103)
    ·
      refine ⟨69375509806127772188961155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46250339870751848125974103 69375509806127772188961155)
      ·
        refine ⟨104063264709191658283441733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69375509806127772188961155 104063264709191658283441733)
        ·
          refine ⟨19511862132973435928145325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104063264709191658283441733 19511862132973435928145325)
          ·
            refine ⟨7316948299865038473054497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19511862132973435928145325 7316948299865038473054497)
            ·
              refine ⟨5487711224898778854790873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316948299865038473054497 5487711224898778854790873)
              ·
                refine ⟨4115783418674084141093155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487711224898778854790873 4115783418674084141093155)
                ·
                  refine ⟨6173675128011126211639733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115783418674084141093155 6173675128011126211639733)
                  ·
                    refine ⟨578782043251043082341225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6173675128011126211639733 578782043251043082341225)
                    ·
                      rfl

theorem cell22_1690761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_1690761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690761 prefixEnd_1690761 := by exact prefixLift 1690761
  have htrace : WordTrace (prefixWord ++ tailWord_1690761) baseStart_1690761 baseEnd_1690761 := by
    simpa [prefixWord, tailWord_1690761, baseEnd_1690761] using wordTrace_append hprefix tailTrace_1690761
  have hstable : (prefixWord ++ tailWord_1690761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690761).length < 2 ^ (prefixWord ++ tailWord_1690761).sum := by decide
  have hdescent : baseEnd_1690761 < baseStart_1690761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690913 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1690913 : Nat := 118140960795 + 1690913 * 2 ^ 59
def prefixEnd_1690913 : Nat := 4983230072969 + 3 ^ 40 * 1690913 * 2
def baseEnd_1690913 : Nat := 578834075957365352540759

theorem tailTrace_1690913 : CollatzResearch.WordTrace tailWord_1690913 prefixEnd_1690913 578834075957365352540759 := by
  unfold tailWord_1690913
  simp only [CollatzResearch.WordTrace]
  refine ⟨61672663723118460794165393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41115109148745640529443595 61672663723118460794165393)
  ·
    refine ⟨46254497792338845595624045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61672663723118460794165393 46254497792338845595624045)
    ·
      refine ⟨17345436672127067098359017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46254497792338845595624045 17345436672127067098359017)
      ·
        refine ⟨13009077504095300323769263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17345436672127067098359017 13009077504095300323769263)
        ·
          refine ⟨19513616256142950485653895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009077504095300323769263 19513616256142950485653895)
          ·
            refine ⟨29270424384214425728480843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19513616256142950485653895 29270424384214425728480843)
            ·
              refine ⟨43905636576321638592721265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29270424384214425728480843 43905636576321638592721265)
              ·
                refine ⟨32929227432241228944540949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43905636576321638592721265 32929227432241228944540949)
                ·
                  refine ⟨1543557535886307606775357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32929227432241228944540949 1543557535886307606775357)
                  ·
                    refine ⟨578834075957365352540759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543557535886307606775357 578834075957365352540759)
                    ·
                      rfl

theorem cell22_1690913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1690913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690913 prefixEnd_1690913 := by exact prefixLift 1690913
  have htrace : WordTrace (prefixWord ++ tailWord_1690913) baseStart_1690913 baseEnd_1690913 := by
    simpa [prefixWord, tailWord_1690913, baseEnd_1690913] using wordTrace_append hprefix tailTrace_1690913
  have hstable : (prefixWord ++ tailWord_1690913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690913).length < 2 ^ (prefixWord ++ tailWord_1690913).sum := by decide
  have hdescent : baseEnd_1690913 < baseStart_1690913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690932 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1690932 : Nat := 118140960795 + 1690932 * 2 ^ 59
def prefixEnd_1690932 : Nat := 4983230072969 + 3 ^ 40 * 1690932 * 2
def baseEnd_1690932 : Nat := 192946860015218545438567

theorem tailTrace_1690932 : CollatzResearch.WordTrace tailWord_1690932 prefixEnd_1690932 192946860015218545438567 := by
  unfold tailWord_1690932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30836678355024813519553525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41115571140033084692738033 30836678355024813519553525)
  ·
    refine ⟨2890938595783576267458143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30836678355024813519553525 2890938595783576267458143)
    ·
      refine ⟨4336407893675364401187215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890938595783576267458143 4336407893675364401187215)
      ·
        refine ⟨6504611840513046601780823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336407893675364401187215 6504611840513046601780823)
        ·
          refine ⟨9756917760769569902671235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6504611840513046601780823 9756917760769569902671235)
          ·
            refine ⟨14635376641154354854006853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9756917760769569902671235 14635376641154354854006853)
            ·
              refine ⟨2744133120216441535126285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14635376641154354854006853 2744133120216441535126285)
              ·
                refine ⟨1029049920081165575672357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744133120216441535126285 1029049920081165575672357)
                ·
                  refine ⟨192946860015218545438567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029049920081165575672357 192946860015218545438567)
                  ·
                    rfl

theorem cell22_1690932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1690932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690932 prefixEnd_1690932 := by exact prefixLift 1690932
  have htrace : WordTrace (prefixWord ++ tailWord_1690932) baseStart_1690932 baseEnd_1690932 := by
    simpa [prefixWord, tailWord_1690932, baseEnd_1690932] using wordTrace_append hprefix tailTrace_1690932
  have hstable : (prefixWord ++ tailWord_1690932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690932).length < 2 ^ (prefixWord ++ tailWord_1690932).sum := by decide
  have hdescent : baseEnd_1690932 < baseStart_1690932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690934 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1690934 : Nat := 118140960795 + 1690934 * 2 ^ 59
def prefixEnd_1690934 : Nat := 4983230072969 + 3 ^ 40 * 1690934 * 2
def baseEnd_1690934 : Nat := 578841264686528297765695

theorem tailTrace_1690934 : CollatzResearch.WordTrace tailWord_1690934 prefixEnd_1690934 578841264686528297765695 := by
  unfold tailWord_1690934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854589353502648836292491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41115619770694920920453237 3854589353502648836292491)
  ·
    refine ⟨5781884030253973254438737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854589353502648836292491 5781884030253973254438737)
    ·
      refine ⟨4336413022690479940829053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5781884030253973254438737 4336413022690479940829053)
      ·
        refine ⟨1626154883508929977810895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4336413022690479940829053 1626154883508929977810895)
        ·
          refine ⟨2439232325263394966716343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626154883508929977810895 2439232325263394966716343)
          ·
            refine ⟨3658848487895092450074515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439232325263394966716343 3658848487895092450074515)
            ·
              refine ⟨5488272731842638675111773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658848487895092450074515 5488272731842638675111773)
              ·
                refine ⟨2058102274440989503166915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488272731842638675111773 2058102274440989503166915)
                ·
                  refine ⟨3087153411661484254750373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058102274440989503166915 3087153411661484254750373)
                  ·
                    refine ⟨578841264686528297765695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087153411661484254750373 578841264686528297765695)
                    ·
                      rfl

theorem cell22_1690934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1690934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690934 prefixEnd_1690934 := by exact prefixLift 1690934
  have htrace : WordTrace (prefixWord ++ tailWord_1690934) baseStart_1690934 baseEnd_1690934 := by
    simpa [prefixWord, tailWord_1690934, baseEnd_1690934] using wordTrace_append hprefix tailTrace_1690934
  have hstable : (prefixWord ++ tailWord_1690934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690934).length < 2 ^ (prefixWord ++ tailWord_1690934).sum := by decide
  have hdescent : baseEnd_1690934 < baseStart_1690934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690988 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1690988 : Nat := 118140960795 + 1690988 * 2 ^ 59
def prefixEnd_1690988 : Nat := 4983230072969 + 3 ^ 40 * 1690988 * 2
def baseEnd_1690988 : Nat := 192953249996696718971843

theorem tailTrace_1690988 : CollatzResearch.WordTrace tailWord_1690988 prefixEnd_1690988 192953249996696718971843 := by
  unfold tailWord_1690988
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837699598923374301572809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41116932798564499068763745 30837699598923374301572809)
  ·
    refine ⟨23128274699192530726179607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30837699598923374301572809 23128274699192530726179607)
    ·
      refine ⟨34692412048788796089269411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23128274699192530726179607 34692412048788796089269411)
      ·
        refine ⟨52038618073183194133904117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692412048788796089269411 52038618073183194133904117)
        ·
          refine ⟨4878620444360924450053511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52038618073183194133904117 4878620444360924450053511)
          ·
            refine ⟨7317930666541386675080267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878620444360924450053511 7317930666541386675080267)
            ·
              refine ⟨10976895999812080012620401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317930666541386675080267 10976895999812080012620401)
              ·
                refine ⟨8232671999859060009465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10976895999812080012620401 8232671999859060009465301)
                ·
                  refine ⟨192953249996696718971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8232671999859060009465301 192953249996696718971843)
                  ·
                    rfl

theorem cell22_1690988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1690988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1690988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1690988 prefixEnd_1690988 := by exact prefixLift 1690988
  have htrace : WordTrace (prefixWord ++ tailWord_1690988) baseStart_1690988 baseEnd_1690988 := by
    simpa [prefixWord, tailWord_1690988, baseEnd_1690988] using wordTrace_append hprefix tailTrace_1690988
  have hstable : (prefixWord ++ tailWord_1690988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690988).length < 2 ^ (prefixWord ++ tailWord_1690988).sum := by decide
  have hdescent : baseEnd_1690988 < baseStart_1690988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691009 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1691009 : Nat := 118140960795 + 1691009 * 2 ^ 59
def prefixEnd_1691009 : Nat := 4983230072969 + 3 ^ 40 * 1691009 * 2
def baseEnd_1691009 : Nat := 578866938719253102140465

theorem tailTrace_1691009 : CollatzResearch.WordTrace tailWord_1691009 prefixEnd_1691009 578866938719253102140465 := by
  unfold tailWord_1691009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61676165130770669189660081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41117443420513779459773387 61676165130770669189660081)
  ·
    refine ⟨46257123848078001892245061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61676165130770669189660081 46257123848078001892245061)
    ·
      refine ⟨8673210721514625354795949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46257123848078001892245061 8673210721514625354795949)
      ·
        refine ⟨3252454020567984508048481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8673210721514625354795949 3252454020567984508048481)
        ·
          refine ⟨2439340515425988381036361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252454020567984508048481 2439340515425988381036361)
          ·
            refine ⟨1829505386569491285777271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439340515425988381036361 1829505386569491285777271)
            ·
              refine ⟨2744258079854236928665907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829505386569491285777271 2744258079854236928665907)
              ·
                refine ⟨4116387119781355392998861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744258079854236928665907 4116387119781355392998861)
                ·
                  refine ⟨1543645169918008272374573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4116387119781355392998861 1543645169918008272374573)
                  ·
                    refine ⟨578866938719253102140465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543645169918008272374573 578866938719253102140465)
                    ·
                      rfl

theorem cell22_1691009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1691009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691009 prefixEnd_1691009 := by exact prefixLift 1691009
  have htrace : WordTrace (prefixWord ++ tailWord_1691009) baseStart_1691009 baseEnd_1691009 := by
    simpa [prefixWord, tailWord_1691009, baseEnd_1691009] using wordTrace_append hprefix tailTrace_1691009
  have hstable : (prefixWord ++ tailWord_1691009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691009).length < 2 ^ (prefixWord ++ tailWord_1691009).sum := by decide
  have hdescent : baseEnd_1691009 < baseStart_1691009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691022 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_1691022 : Nat := 118140960795 + 1691022 * 2 ^ 59
def prefixEnd_1691022 : Nat := 4983230072969 + 3 ^ 40 * 1691022 * 2
def baseEnd_1691022 : Nat := 192957129628308467188475

theorem tailTrace_1691022 : CollatzResearch.WordTrace tailWord_1691022 prefixEnd_1691022 192957129628308467188475 := by
  unfold tailWord_1691022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709579909965446551235415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41117759519815714939922213 7709579909965446551235415)
  ·
    refine ⟨11564369864948169826853123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709579909965446551235415 11564369864948169826853123)
    ·
      refine ⟨17346554797422254740279685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564369864948169826853123 17346554797422254740279685)
      ·
        refine ⟨3252479024516672763802441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17346554797422254740279685 3252479024516672763802441)
        ·
          refine ⟨2439359268387504572851831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252479024516672763802441 2439359268387504572851831)
          ·
            refine ⟨3659038902581256859277747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439359268387504572851831 3659038902581256859277747)
            ·
              refine ⟨5488558353871885288916621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659038902581256859277747 5488558353871885288916621)
              ·
                refine ⟨2058209382701956983343733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488558353871885288916621 2058209382701956983343733)
                ·
                  refine ⟨192957129628308467188475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058209382701956983343733 192957129628308467188475)
                  ·
                    rfl

theorem cell22_1691022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_1691022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691022 prefixEnd_1691022 := by exact prefixLift 1691022
  have htrace : WordTrace (prefixWord ++ tailWord_1691022) baseStart_1691022 baseEnd_1691022 := by
    simpa [prefixWord, tailWord_1691022, baseEnd_1691022] using wordTrace_append hprefix tailTrace_1691022
  have hstable : (prefixWord ++ tailWord_1691022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691022).length < 2 ^ (prefixWord ++ tailWord_1691022).sum := by decide
  have hdescent : baseEnd_1691022 < baseStart_1691022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691082 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1691082 : Nat := 118140960795 + 1691082 * 2 ^ 59
def prefixEnd_1691082 : Nat := 4983230072969 + 3 ^ 40 * 1691082 * 2
def baseEnd_1691082 : Nat := 578891928111105245065241

theorem tailTrace_1691082 : CollatzResearch.WordTrace tailWord_1691082 prefixEnd_1691082 578891928111105245065241 := by
  unfold tailWord_1691082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419706914876550664266875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41119218439670801771378333 15419706914876550664266875)
  ·
    refine ⟨23129560372314825996400313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15419706914876550664266875 23129560372314825996400313)
    ·
      refine ⟨17347170279236119497300235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23129560372314825996400313 17347170279236119497300235)
      ·
        refine ⟨26020755418854179245950353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347170279236119497300235 26020755418854179245950353)
        ·
          refine ⟨19515566564140634434462765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26020755418854179245950353 19515566564140634434462765)
          ·
            refine ⟨7318337461552737912923537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19515566564140634434462765 7318337461552737912923537)
            ·
              refine ⟨5488753096164553434692653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318337461552737912923537 5488753096164553434692653)
              ·
                refine ⟨2058282411061707538009745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488753096164553434692653 2058282411061707538009745)
                ·
                  refine ⟨1543711808296280653507309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058282411061707538009745 1543711808296280653507309)
                  ·
                    refine ⟨578891928111105245065241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543711808296280653507309 578891928111105245065241)
                    ·
                      rfl

theorem cell22_1691082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1691082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691082 prefixEnd_1691082 := by exact prefixLift 1691082
  have htrace : WordTrace (prefixWord ++ tailWord_1691082) baseStart_1691082 baseEnd_1691082 := by
    simpa [prefixWord, tailWord_1691082, baseEnd_1691082] using wordTrace_append hprefix tailTrace_1691082
  have hstable : (prefixWord ++ tailWord_1691082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691082).length < 2 ^ (prefixWord ++ tailWord_1691082).sum := by decide
  have hdescent : baseEnd_1691082 < baseStart_1691082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691097 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_1691097 : Nat := 118140960795 + 1691097 * 2 ^ 59
def prefixEnd_1691097 : Nat := 4983230072969 + 3 ^ 40 * 1691097 * 2
def baseEnd_1691097 : Nat := 578897062917650205940195

theorem tailTrace_1691097 : CollatzResearch.WordTrace tailWord_1691097 prefixEnd_1691097 578897062917650205940195 := by
  unfold tailWord_1691097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679374754451860218863545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41119583169634573479242363 61679374754451860218863545)
  ·
    refine ⟨46259531065838895164147659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61679374754451860218863545 46259531065838895164147659)
    ·
      refine ⟨69389296598758342746221489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46259531065838895164147659 69389296598758342746221489)
      ·
        refine ⟨52041972449068757059666117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69389296598758342746221489 52041972449068757059666117)
        ·
          refine ⟨9757869834200391948687397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52041972449068757059666117 9757869834200391948687397)
          ·
            refine ⟨1829600593912573490378887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9757869834200391948687397 1829600593912573490378887)
            ·
              refine ⟨2744400890868860235568331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829600593912573490378887 2744400890868860235568331)
              ·
                refine ⟨4116601336303290353352497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744400890868860235568331 4116601336303290353352497)
                ·
                  refine ⟨3087451002227467765014373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116601336303290353352497 3087451002227467765014373)
                  ·
                    refine ⟨578897062917650205940195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087451002227467765014373 578897062917650205940195)
                    ·
                      rfl

theorem cell22_1691097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_1691097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691097 prefixEnd_1691097 := by exact prefixLift 1691097
  have htrace : WordTrace (prefixWord ++ tailWord_1691097) baseStart_1691097 baseEnd_1691097 := by
    simpa [prefixWord, tailWord_1691097, baseEnd_1691097] using wordTrace_append hprefix tailTrace_1691097
  have hstable : (prefixWord ++ tailWord_1691097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691097).length < 2 ^ (prefixWord ++ tailWord_1691097).sum := by decide
  have hdescent : baseEnd_1691097 < baseStart_1691097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691200 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_1691200 : Nat := 118140960795 + 1691200 * 2 ^ 59
def prefixEnd_1691200 : Nat := 4983230072969 + 3 ^ 40 * 1691200 * 2
def baseEnd_1691200 : Nat := 578932321922592270614879

theorem tailTrace_1691200 : CollatzResearch.WordTrace tailWord_1691200 prefixEnd_1691200 578932321922592270614879 := by
  unfold tailWord_1691200
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841565736539354404931527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41122087648719139206575369 30841565736539354404931527)
  ·
    refine ⟨46262348604809031607397291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841565736539354404931527 46262348604809031607397291)
    ·
      refine ⟨69393522907213547411095937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46262348604809031607397291 69393522907213547411095937)
      ·
        refine ⟨52045142180410160558321953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69393522907213547411095937 52045142180410160558321953)
        ·
          refine ⟨39033856635307620418741465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52045142180410160558321953 39033856635307620418741465)
          ·
            refine ⟨29275392476480715314056099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39033856635307620418741465 29275392476480715314056099)
            ·
              refine ⟨43913088714721072971084149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29275392476480715314056099 43913088714721072971084149)
              ·
                refine ⟨4116852067005100591039139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43913088714721072971084149 4116852067005100591039139)
                ·
                  refine ⟨6175278100507650886558709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116852067005100591039139 6175278100507650886558709)
                  ·
                    refine ⟨578932321922592270614879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6175278100507650886558709 578932321922592270614879)
                    ·
                      rfl

theorem cell22_1691200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_1691200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691200 prefixEnd_1691200 := by exact prefixLift 1691200
  have htrace : WordTrace (prefixWord ++ tailWord_1691200) baseStart_1691200 baseEnd_1691200 := by
    simpa [prefixWord, tailWord_1691200, baseEnd_1691200] using wordTrace_append hprefix tailTrace_1691200
  have hstable : (prefixWord ++ tailWord_1691200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691200).length < 2 ^ (prefixWord ++ tailWord_1691200).sum := by decide
  have hdescent : baseEnd_1691200 < baseStart_1691200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691236 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1691236 : Nat := 118140960795 + 1691236 * 2 ^ 59
def prefixEnd_1691236 : Nat := 4983230072969 + 3 ^ 40 * 1691236 * 2
def baseEnd_1691236 : Nat := 192981548486100058904923

theorem tailTrace_1691236 : CollatzResearch.WordTrace tailWord_1691236 prefixEnd_1691236 192981548486100058904923 := by
  unfold tailWord_1691236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842222250474143479086781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41122963000632191305449041 30842222250474143479086781)
  ·
    refine ⟨11565833343927803804657543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30842222250474143479086781 11565833343927803804657543)
    ·
      refine ⟨17348750015891705706986315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11565833343927803804657543 17348750015891705706986315)
      ·
        refine ⟨26023125023837558560479473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348750015891705706986315 26023125023837558560479473)
        ·
          refine ⟨19517343767878168920359605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26023125023837558560479473 19517343767878168920359605)
          ·
            refine ⟨1829750978238578336283713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19517343767878168920359605 1829750978238578336283713)
            ·
              refine ⟨1372313233678933752212785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829750978238578336283713 1372313233678933752212785)
              ·
                refine ⟨1029234925259200314159589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372313233678933752212785 1029234925259200314159589)
                ·
                  refine ⟨192981548486100058904923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029234925259200314159589 192981548486100058904923)
                  ·
                    rfl

theorem cell22_1691236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1691236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691236 prefixEnd_1691236 := by exact prefixLift 1691236
  have htrace : WordTrace (prefixWord ++ tailWord_1691236) baseStart_1691236 baseEnd_1691236 := by
    simpa [prefixWord, tailWord_1691236, baseEnd_1691236] using wordTrace_append hprefix tailTrace_1691236
  have hstable : (prefixWord ++ tailWord_1691236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691236).length < 2 ^ (prefixWord ++ tailWord_1691236).sum := by decide
  have hdescent : baseEnd_1691236 < baseStart_1691236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691260 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1691260 : Nat := 118140960795 + 1691260 * 2 ^ 59
def prefixEnd_1691260 : Nat := 4983230072969 + 3 ^ 40 * 1691260 * 2
def baseEnd_1691260 : Nat := 578952861148772114114695

theorem tailTrace_1691260 : CollatzResearch.WordTrace tailWord_1691260 prefixEnd_1691260 578952861148772114114695 := by
  unfold tailWord_1691260
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842659926430669528523617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41123546568574226038031489 30842659926430669528523617)
  ·
    refine ⟨23131994944823002146392713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30842659926430669528523617 23131994944823002146392713)
    ·
      refine ⟨17348996208617251609794535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23131994944823002146392713 17348996208617251609794535)
      ·
        refine ⟨26023494312925877414691803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348996208617251609794535 26023494312925877414691803)
        ·
          refine ⟨39035241469388816122037705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26023494312925877414691803 39035241469388816122037705)
          ·
            refine ⟨29276431102041612091528279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39035241469388816122037705 29276431102041612091528279)
            ·
              refine ⟨43914646653062418137292419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29276431102041612091528279 43914646653062418137292419)
              ·
                refine ⟨65871969979593627205938629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43914646653062418137292419 65871969979593627205938629)
                ·
                  refine ⟨12350994371173805101113493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65871969979593627205938629 12350994371173805101113493)
                  ·
                    refine ⟨578952861148772114114695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12350994371173805101113493 578952861148772114114695)
                    ·
                      rfl

theorem cell22_1691260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1691260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691260 prefixEnd_1691260 := by exact prefixLift 1691260
  have htrace : WordTrace (prefixWord ++ tailWord_1691260) baseStart_1691260 baseEnd_1691260 := by
    simpa [prefixWord, tailWord_1691260, baseEnd_1691260] using wordTrace_append hprefix tailTrace_1691260
  have hstable : (prefixWord ++ tailWord_1691260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691260).length < 2 ^ (prefixWord ++ tailWord_1691260).sum := by decide
  have hdescent : baseEnd_1691260 < baseStart_1691260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691275 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 7]
def baseStart_1691275 : Nat := 118140960795 + 1691275 * 2 ^ 59
def prefixEnd_1691275 : Nat := 4983230072969 + 3 ^ 40 * 1691275 * 2
def baseEnd_1691275 : Nat := 192985998651772358329883

theorem tailTrace_1691275 : CollatzResearch.WordTrace tailWord_1691275 prefixEnd_1691275 192985998651772358329883 := by
  unfold tailWord_1691275
  simp only [CollatzResearch.WordTrace]
  refine ⟨61685866947806996618843279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41123911298537997745895519 61685866947806996618843279)
  ·
    refine ⟨92528800421710494928264919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61685866947806996618843279 92528800421710494928264919)
    ·
      refine ⟨138793200632565742392397379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92528800421710494928264919 138793200632565742392397379)
      ·
        refine ⟨208189800948848613588596069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138793200632565742392397379 208189800948848613588596069)
        ·
          refine ⟨39035587677909115047861763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208189800948848613588596069 39035587677909115047861763)
          ·
            refine ⟨58553381516863672571792645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39035587677909115047861763 58553381516863672571792645)
            ·
              refine ⟨10978759034411938607211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58553381516863672571792645 10978759034411938607211121)
              ·
                refine ⟨8234069275808953955408341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978759034411938607211121 8234069275808953955408341)
                ·
                  refine ⟨192985998651772358329883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8234069275808953955408341 192985998651772358329883)
                  ·
                    rfl

theorem cell22_1691275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_1691275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691275 prefixEnd_1691275 := by exact prefixLift 1691275
  have htrace : WordTrace (prefixWord ++ tailWord_1691275) baseStart_1691275 baseEnd_1691275 := by
    simpa [prefixWord, tailWord_1691275, baseEnd_1691275] using wordTrace_append hprefix tailTrace_1691275
  have hstable : (prefixWord ++ tailWord_1691275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691275).length < 2 ^ (prefixWord ++ tailWord_1691275).sum := by decide
  have hdescent : baseEnd_1691275 < baseStart_1691275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691296 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_1691296 : Nat := 118140960795 + 1691296 * 2 ^ 59
def prefixEnd_1691296 : Nat := 4983230072969 + 3 ^ 40 * 1691296 * 2
def baseEnd_1691296 : Nat := 578965184684480020214585

theorem tailTrace_1691296 : CollatzResearch.WordTrace tailWord_1691296 prefixEnd_1691296 578965184684480020214585 := by
  unfold tailWord_1691296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30843316440365458602678871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41124421920487278136905161 30843316440365458602678871)
  ·
    refine ⟨46264974660548187904018307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30843316440365458602678871 46264974660548187904018307)
    ·
      refine ⟨69397461990822281856027461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46264974660548187904018307 69397461990822281856027461)
      ·
        refine ⟨13012024123279177848005149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69397461990822281856027461 13012024123279177848005149)
        ·
          refine ⟨4879509046229691693001931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13012024123279177848005149 4879509046229691693001931)
          ·
            refine ⟨7319263569344537539502897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879509046229691693001931 7319263569344537539502897)
            ·
              refine ⟨5489447677008403154627173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7319263569344537539502897 5489447677008403154627173)
              ·
                refine ⟨1029271439439075591492595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5489447677008403154627173 1029271439439075591492595)
                ·
                  refine ⟨1543907159158613387238893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029271439439075591492595 1543907159158613387238893)
                  ·
                    refine ⟨578965184684480020214585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1543907159158613387238893 578965184684480020214585)
                    ·
                      rfl

theorem cell22_1691296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_1691296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691296 prefixEnd_1691296 := by exact prefixLift 1691296
  have htrace : WordTrace (prefixWord ++ tailWord_1691296) baseStart_1691296 baseEnd_1691296 := by
    simpa [prefixWord, tailWord_1691296, baseEnd_1691296] using wordTrace_append hprefix tailTrace_1691296
  have hstable : (prefixWord ++ tailWord_1691296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691296).length < 2 ^ (prefixWord ++ tailWord_1691296).sum := by decide
  have hdescent : baseEnd_1691296 < baseStart_1691296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691354 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1691354 : Nat := 118140960795 + 1691354 * 2 ^ 59
def prefixEnd_1691354 : Nat := 4983230072969 + 3 ^ 40 * 1691354 * 2
def baseEnd_1691354 : Nat := 192995013089929067421469

theorem tailTrace_1691354 : CollatzResearch.WordTrace tailWord_1691354 prefixEnd_1691354 192995013089929067421469 := by
  unfold tailWord_1691354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422187078630198277742279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41125832209680528740646077 15422187078630198277742279)
  ·
    refine ⟨23133280617945297416613419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15422187078630198277742279 23133280617945297416613419)
    ·
      refine ⟨34699920926917946124920129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23133280617945297416613419 34699920926917946124920129)
      ·
        refine ⟨26024940695188459593690097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34699920926917946124920129 26024940695188459593690097)
        ·
          refine ⟨19518705521391344695267573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26024940695188459593690097 19518705521391344695267573)
          ·
            refine ⟨1829878642630438565181335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19518705521391344695267573 1829878642630438565181335)
            ·
              refine ⟨2744817963945657847772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829878642630438565181335 2744817963945657847772003)
              ·
                refine ⟨4117226945918486771658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744817963945657847772003 4117226945918486771658005)
                ·
                  refine ⟨192995013089929067421469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4117226945918486771658005 192995013089929067421469)
                  ·
                    rfl

theorem cell22_1691354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1691354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691354 prefixEnd_1691354 := by exact prefixLift 1691354
  have htrace : WordTrace (prefixWord ++ tailWord_1691354) baseStart_1691354 baseEnd_1691354 := by
    simpa [prefixWord, tailWord_1691354, baseEnd_1691354] using wordTrace_append hprefix tailTrace_1691354
  have hstable : (prefixWord ++ tailWord_1691354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691354).length < 2 ^ (prefixWord ++ tailWord_1691354).sum := by decide
  have hdescent : baseEnd_1691354 < baseStart_1691354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691398 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1691398 : Nat := 118140960795 + 1691398 * 2 ^ 59
def prefixEnd_1691398 : Nat := 4983230072969 + 3 ^ 40 * 1691398 * 2
def baseEnd_1691398 : Nat := 579000101368985754164273

theorem tailTrace_1691398 : CollatzResearch.WordTrace tailWord_1691398 prefixEnd_1691398 579000101368985754164273 := by
  unfold tailWord_1691398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927823535198793394549089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41126902084240925750380565 1927823535198793394549089)
  ·
    refine ⟨1445867651399095045911817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1927823535198793394549089 1445867651399095045911817)
    ·
      refine ⟨1084400738549321284433863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1445867651399095045911817 1084400738549321284433863)
      ·
        refine ⟨1626601107823981926650795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084400738549321284433863 1626601107823981926650795)
        ·
          refine ⟨2439901661735972889976193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626601107823981926650795 2439901661735972889976193)
          ·
            refine ⟨1829926246301979667482145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439901661735972889976193 1829926246301979667482145)
            ·
              refine ⟨1372444684726484750611609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829926246301979667482145 1372444684726484750611609)
              ·
                refine ⟨1029333513544863562958707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372444684726484750611609 1029333513544863562958707)
                ·
                  refine ⟨1544000270317295344438061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029333513544863562958707 1544000270317295344438061)
                  ·
                    refine ⟨579000101368985754164273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544000270317295344438061 579000101368985754164273)
                    ·
                      rfl

theorem cell22_1691398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1691398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691398 prefixEnd_1691398 := by exact prefixLift 1691398
  have htrace : WordTrace (prefixWord ++ tailWord_1691398) baseStart_1691398 baseEnd_1691398 := by
    simpa [prefixWord, tailWord_1691398, baseEnd_1691398] using wordTrace_append hprefix tailTrace_1691398
  have hstable : (prefixWord ++ tailWord_1691398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691398).length < 2 ^ (prefixWord ++ tailWord_1691398).sum := by decide
  have hdescent : baseEnd_1691398 < baseStart_1691398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691399 : List Nat := [1, 1, 4, 4, 3, 9]
def baseStart_1691399 : Nat := 118140960795 + 1691399 * 2 ^ 59
def prefixEnd_1691399 : Nat := 4983230072969 + 3 ^ 40 * 1691399 * 2
def baseEnd_1691399 : Nat := 7148153625795334381349

theorem tailTrace_1691399 : CollatzResearch.WordTrace tailWord_1691399 prefixEnd_1691399 7148153625795334381349 := by
  unfold tailWord_1691399
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690389599357765796357251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41126926399571843864238167 61690389599357765796357251)
  ·
    refine ⟨92535584399036648694535877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61690389599357765796357251 92535584399036648694535877)
    ·
      refine ⟨17350422074819371630225477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92535584399036648694535877 17350422074819371630225477)
      ·
        refine ⟨3253204139028632180667277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17350422074819371630225477 3253204139028632180667277)
        ·
          refine ⟨1219951552135737067750229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3253204139028632180667277 1219951552135737067750229)
          ·
            refine ⟨7148153625795334381349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1219951552135737067750229 7148153625795334381349)
            ·
              rfl

theorem cell22_1691399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 9].length) (baseStart_1691399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691399 prefixEnd_1691399 := by exact prefixLift 1691399
  have htrace : WordTrace (prefixWord ++ tailWord_1691399) baseStart_1691399 baseEnd_1691399 := by
    simpa [prefixWord, tailWord_1691399, baseEnd_1691399] using wordTrace_append hprefix tailTrace_1691399
  have hstable : (prefixWord ++ tailWord_1691399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691399).length < 2 ^ (prefixWord ++ tailWord_1691399).sum := by decide
  have hdescent : baseEnd_1691399 < baseStart_1691399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691448 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_1691448 : Nat := 118140960795 + 1691448 * 2 ^ 59
def prefixEnd_1691448 : Nat := 4983230072969 + 3 ^ 40 * 1691448 * 2
def baseEnd_1691448 : Nat := 579017217390802290414119

theorem tailTrace_1691448 : CollatzResearch.WordTrace tailWord_1691448 prefixEnd_1691448 579017217390802290414119 := by
  unfold tailWord_1691448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30846088388090123582445499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41128117850786831443260665 30846088388090123582445499)
  ·
    refine ⟨46269132582135185373668249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30846088388090123582445499 46269132582135185373668249)
    ·
      refine ⟨34701849436601389030251187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46269132582135185373668249 34701849436601389030251187)
      ·
        refine ⟨52052774154902083545376781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34701849436601389030251187 52052774154902083545376781)
        ·
          refine ⟨19519790308088281329516293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52052774154902083545376781 19519790308088281329516293)
          ·
            refine ⟨3659960682766552749284305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19519790308088281329516293 3659960682766552749284305)
            ·
              refine ⟨2744970512074914561963229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659960682766552749284305 2744970512074914561963229)
              ·
                refine ⟨1029363942028092960736211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744970512074914561963229 1029363942028092960736211)
                ·
                  refine ⟨1544045913042139441104317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029363942028092960736211 1544045913042139441104317)
                  ·
                    refine ⟨579017217390802290414119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544045913042139441104317 579017217390802290414119)
                    ·
                      rfl

theorem cell22_1691448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_1691448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691448 prefixEnd_1691448 := by exact prefixLift 1691448
  have htrace : WordTrace (prefixWord ++ tailWord_1691448) baseStart_1691448 baseEnd_1691448 := by
    simpa [prefixWord, tailWord_1691448, baseEnd_1691448] using wordTrace_append hprefix tailTrace_1691448
  have hstable : (prefixWord ++ tailWord_1691448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691448).length < 2 ^ (prefixWord ++ tailWord_1691448).sum := by decide
  have hdescent : baseEnd_1691448 < baseStart_1691448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691523 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 4]
def baseStart_1691523 : Nat := 118140960795 + 1691523 * 2 ^ 59
def prefixEnd_1691523 : Nat := 4983230072969 + 3 ^ 40 * 1691523 * 2
def baseEnd_1691523 : Nat := 193014297141175698262963

theorem tailTrace_1691523 : CollatzResearch.WordTrace tailWord_1691523 prefixEnd_1691523 193014297141175698262963 := by
  unfold tailWord_1691523
  simp only [CollatzResearch.WordTrace]
  refine ⟨61694912250908534973871223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41129941500605689982580815 61694912250908534973871223)
  ·
    refine ⟨92542368376362802460806835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61694912250908534973871223 92542368376362802460806835)
    ·
      refine ⟨138813552564544203691210253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92542368376362802460806835 138813552564544203691210253)
      ·
        refine ⟨52055082211704076384203845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138813552564544203691210253 52055082211704076384203845)
        ·
          refine ⟨9760327914694514322038221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52055082211704076384203845 9760327914694514322038221)
          ·
            refine ⟨3660122968010442870764333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9760327914694514322038221 3660122968010442870764333)
            ·
              refine ⟨1372546113003916076536625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3660122968010442870764333 1372546113003916076536625)
              ·
                refine ⟨1029409584752937057402469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372546113003916076536625 1029409584752937057402469)
                ·
                  refine ⟨193014297141175698262963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029409584752937057402469 193014297141175698262963)
                  ·
                    rfl

theorem cell22_1691523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 4].length) (baseStart_1691523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691523 prefixEnd_1691523 := by exact prefixLift 1691523
  have htrace : WordTrace (prefixWord ++ tailWord_1691523) baseStart_1691523 baseEnd_1691523 := by
    simpa [prefixWord, tailWord_1691523, baseEnd_1691523] using wordTrace_append hprefix tailTrace_1691523
  have hstable : (prefixWord ++ tailWord_1691523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691523).length < 2 ^ (prefixWord ++ tailWord_1691523).sum := by decide
  have hdescent : baseEnd_1691523 < baseStart_1691523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691553 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1691553 : Nat := 118140960795 + 1691553 * 2 ^ 59
def prefixEnd_1691553 : Nat := 4983230072969 + 3 ^ 40 * 1691553 * 2
def baseEnd_1691553 : Nat := 579053161036617016538797

theorem tailTrace_1691553 : CollatzResearch.WordTrace tailWord_1691553 prefixEnd_1691553 579053161036617016538797 := by
  unfold tailWord_1691553
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696006440799850097463313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41130670960533233398308875 61696006440799850097463313)
  ·
    refine ⟨46272004830599887573097485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61696006440799850097463313 46272004830599887573097485)
    ·
      refine ⟨17352001811474957839911557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46272004830599887573097485 17352001811474957839911557)
      ·
        refine ⟨3253500339651554594983417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17352001811474957839911557 3253500339651554594983417)
        ·
          refine ⟨2440125254738665946237563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253500339651554594983417 2440125254738665946237563)
          ·
            refine ⟨3660187882107998919356345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440125254738665946237563 3660187882107998919356345)
            ·
              refine ⟨2745140911580999189517259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660187882107998919356345 2745140911580999189517259)
              ·
                refine ⟨4117711367371498784275889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745140911580999189517259 4117711367371498784275889)
                ·
                  refine ⟨3088283525528624088206917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117711367371498784275889 3088283525528624088206917)
                  ·
                    refine ⟨579053161036617016538797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088283525528624088206917 579053161036617016538797)
                    ·
                      rfl

theorem cell22_1691553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1691553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691553 prefixEnd_1691553 := by exact prefixLift 1691553
  have htrace : WordTrace (prefixWord ++ tailWord_1691553) baseStart_1691553 baseEnd_1691553 := by
    simpa [prefixWord, tailWord_1691553, baseEnd_1691553] using wordTrace_append hprefix tailTrace_1691553
  have hstable : (prefixWord ++ tailWord_1691553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691553).length < 2 ^ (prefixWord ++ tailWord_1691553).sum := by decide
  have hdescent : baseEnd_1691553 < baseStart_1691553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691572 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1691572 : Nat := 118140960795 + 1691572 * 2 ^ 59
def prefixEnd_1691572 : Nat := 4983230072969 + 3 ^ 40 * 1691572 * 2
def baseEnd_1691572 : Nat := 579059665124907300313739

theorem tailTrace_1691572 : CollatzResearch.WordTrace tailWord_1691572 prefixEnd_1691572 579059665124907300313739 := by
  unfold tailWord_1691572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848349713865508171202485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41131132951820677561603313 30848349713865508171202485)
  ·
    refine ⟨2892032785674891391050233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30848349713865508171202485 2892032785674891391050233)
    ·
      refine ⟨2169024589256168543287675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2892032785674891391050233 2169024589256168543287675)
      ·
        refine ⟨3253536883884252814931513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169024589256168543287675 3253536883884252814931513)
        ·
          refine ⟨2440152662913189611198635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253536883884252814931513 2440152662913189611198635)
          ·
            refine ⟨3660228994369784416797953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440152662913189611198635 3660228994369784416797953)
            ·
              refine ⟨2745171745777338312598465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660228994369784416797953 2745171745777338312598465)
              ·
                refine ⟨2058878809333003734448849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745171745777338312598465 2058878809333003734448849)
                ·
                  refine ⟨1544159106999752800836637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058878809333003734448849 1544159106999752800836637)
                  ·
                    refine ⟨579059665124907300313739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544159106999752800836637 579059665124907300313739)
                    ·
                      rfl

theorem cell22_1691572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1691572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691572 prefixEnd_1691572 := by exact prefixLift 1691572
  have htrace : WordTrace (prefixWord ++ tailWord_1691572) baseStart_1691572 baseEnd_1691572 := by
    simpa [prefixWord, tailWord_1691572, baseEnd_1691572] using wordTrace_append hprefix tailTrace_1691572
  have hstable : (prefixWord ++ tailWord_1691572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691572).length < 2 ^ (prefixWord ++ tailWord_1691572).sum := by decide
  have hdescent : baseEnd_1691572 < baseStart_1691572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691579 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 5]
def baseStart_1691579 : Nat := 118140960795 + 1691579 * 2 ^ 59
def prefixEnd_1691579 : Nat := 4983230072969 + 3 ^ 40 * 1691579 * 2
def baseEnd_1691579 : Nat := 193020687122653871796239

theorem tailTrace_1691579 : CollatzResearch.WordTrace tailWord_1691579 prefixEnd_1691579 193020687122653871796239 := by
  unfold tailWord_1691579
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696954738705656537909791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41131303159137104358606527 61696954738705656537909791)
  ·
    refine ⟨92545432108058484806864687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61696954738705656537909791 92545432108058484806864687)
    ·
      refine ⟨138818148162087727210297031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92545432108058484806864687 138818148162087727210297031)
      ·
        refine ⟨208227222243131590815445547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138818148162087727210297031 208227222243131590815445547)
        ·
          refine ⟨312340833364697386223168321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208227222243131590815445547 312340833364697386223168321)
          ·
            refine ⟨234255625023523039667376241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312340833364697386223168321 234255625023523039667376241)
            ·
              refine ⟨175691718767642279750532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234255625023523039667376241 175691718767642279750532181)
              ·
                refine ⟨2058887329308307965826549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 175691718767642279750532181 2058887329308307965826549)
                ·
                  refine ⟨193020687122653871796239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058887329308307965826549 193020687122653871796239)
                  ·
                    rfl

theorem cell22_1691579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].length) (baseStart_1691579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691579 prefixEnd_1691579 := by exact prefixLift 1691579
  have htrace : WordTrace (prefixWord ++ tailWord_1691579) baseStart_1691579 baseEnd_1691579 := by
    simpa [prefixWord, tailWord_1691579, baseEnd_1691579] using wordTrace_append hprefix tailTrace_1691579
  have hstable : (prefixWord ++ tailWord_1691579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691579).length < 2 ^ (prefixWord ++ tailWord_1691579).sum := by decide
  have hdescent : baseEnd_1691579 < baseStart_1691579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691583 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 1, 3]
def baseStart_1691583 : Nat := 118140960795 + 1691583 * 2 ^ 59
def prefixEnd_1691583 : Nat := 4983230072969 + 3 ^ 40 * 1691583 * 2
def baseEnd_1691583 : Nat := 579063430649706938288705

theorem tailTrace_1691583 : CollatzResearch.WordTrace tailWord_1691583 prefixEnd_1691583 579063430649706938288705 := by
  unfold tailWord_1691583
  simp only [CollatzResearch.WordTrace]
  refine ⟨61697100630691165221055403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41131400420460776814036935 61697100630691165221055403)
  ·
    refine ⟨92545650946036747831583105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61697100630691165221055403 92545650946036747831583105)
    ·
      refine ⟨69409238209527560873687329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92545650946036747831583105 69409238209527560873687329)
      ·
        refine ⟨52056928657145670655265497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69409238209527560873687329 52056928657145670655265497)
        ·
          refine ⟨39042696492859252991449123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52056928657145670655265497 39042696492859252991449123)
          ·
            refine ⟨58564044739288879487173685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39042696492859252991449123 58564044739288879487173685)
            ·
              refine ⟨5490379194308332451922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58564044739288879487173685 5490379194308332451922533)
              ·
                refine ⟨1029446098932812334735475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5490379194308332451922533 1029446098932812334735475)
                ·
                  refine ⟨1544169148399218502103213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029446098932812334735475 1544169148399218502103213)
                  ·
                    refine ⟨579063430649706938288705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544169148399218502103213 579063430649706938288705)
                    ·
                      rfl

theorem cell22_1691583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_1691583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691583 prefixEnd_1691583 := by exact prefixLift 1691583
  have htrace : WordTrace (prefixWord ++ tailWord_1691583) baseStart_1691583 baseEnd_1691583 := by
    simpa [prefixWord, tailWord_1691583, baseEnd_1691583] using wordTrace_append hprefix tailTrace_1691583
  have hstable : (prefixWord ++ tailWord_1691583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691583).length < 2 ^ (prefixWord ++ tailWord_1691583).sum := by decide
  have hdescent : baseEnd_1691583 < baseStart_1691583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691594 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1691594 : Nat := 118140960795 + 1691594 * 2 ^ 59
def prefixEnd_1691594 : Nat := 4983230072969 + 3 ^ 40 * 1691594 * 2
def baseEnd_1691594 : Nat := 579067196174506576263671

theorem tailTrace_1691594 : CollatzResearch.WordTrace tailWord_1691594 prefixEnd_1691594 579067196174506576263671 := by
  unfold tailWord_1691594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424375458412828524926459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41131667889100876066470557 15424375458412828524926459)
  ·
    refine ⟨23136563187619242787389689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15424375458412828524926459 23136563187619242787389689)
    ·
      refine ⟨17352422390714432090542267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23136563187619242787389689 17352422390714432090542267)
      ·
        refine ⟨26028633586071648135813401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17352422390714432090542267 26028633586071648135813401)
        ·
          refine ⟨19521475189553736101860051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26028633586071648135813401 19521475189553736101860051)
          ·
            refine ⟨29282212784330604152790077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19521475189553736101860051 29282212784330604152790077)
            ·
              refine ⟨10980829794123976557296279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29282212784330604152790077 10980829794123976557296279)
              ·
                refine ⟨16471244691185964835944419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10980829794123976557296279 16471244691185964835944419)
                ·
                  refine ⟨24706867036778947253916629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16471244691185964835944419 24706867036778947253916629)
                  ·
                    refine ⟨579067196174506576263671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24706867036778947253916629 579067196174506576263671)
                    ·
                      rfl

theorem cell22_1691594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1691594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691594 prefixEnd_1691594 := by exact prefixLift 1691594
  have htrace : WordTrace (prefixWord ++ tailWord_1691594) baseStart_1691594 baseEnd_1691594 := by
    simpa [prefixWord, tailWord_1691594, baseEnd_1691594] using wordTrace_append hprefix tailTrace_1691594
  have hstable : (prefixWord ++ tailWord_1691594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691594).length < 2 ^ (prefixWord ++ tailWord_1691594).sum := by decide
  have hdescent : baseEnd_1691594 < baseStart_1691594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691596 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1691596 : Nat := 118140960795 + 1691596 * 2 ^ 59
def prefixEnd_1691596 : Nat := 4983230072969 + 3 ^ 40 * 1691596 * 2
def baseEnd_1691596 : Nat := 193022626938459745904555

theorem tailTrace_1691596 : CollatzResearch.WordTrace tailWord_1691596 prefixEnd_1691596 193022626938459745904555 := by
  unfold tailWord_1691596
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848787389822034220639321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41131716519762712294185761 30848787389822034220639321)
  ·
    refine ⟨23136590542366525665479491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30848787389822034220639321 23136590542366525665479491)
    ·
      refine ⟨34704885813549788498219237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23136590542366525665479491 34704885813549788498219237)
      ·
        refine ⟨6507166090040585343416107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34704885813549788498219237 6507166090040585343416107)
        ·
          refine ⟨9760749135060878015124161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507166090040585343416107 9760749135060878015124161)
          ·
            refine ⟨7320561851295658511343121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760749135060878015124161 7320561851295658511343121)
            ·
              refine ⟨5490421388471743883507341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320561851295658511343121 5490421388471743883507341)
              ·
                refine ⟨2058908020676903956315253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5490421388471743883507341 2058908020676903956315253)
                ·
                  refine ⟨193022626938459745904555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058908020676903956315253 193022626938459745904555)
                  ·
                    rfl

theorem cell22_1691596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1691596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691596 prefixEnd_1691596 := by exact prefixLift 1691596
  have htrace : WordTrace (prefixWord ++ tailWord_1691596) baseStart_1691596 baseEnd_1691596 := by
    simpa [prefixWord, tailWord_1691596, baseEnd_1691596] using wordTrace_append hprefix tailTrace_1691596
  have hstable : (prefixWord ++ tailWord_1691596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691596).length < 2 ^ (prefixWord ++ tailWord_1691596).sum := by decide
  have hdescent : baseEnd_1691596 < baseStart_1691596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691624 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_1691624 : Nat := 118140960795 + 1691624 * 2 ^ 59
def prefixEnd_1691624 : Nat := 4983230072969 + 3 ^ 40 * 1691624 * 2
def baseEnd_1691624 : Nat := 193025821929198832671193

theorem tailTrace_1691624 : CollatzResearch.WordTrace tailWord_1691624 prefixEnd_1691624 193025821929198832671193 := by
  unfold tailWord_1691624
  simp only [CollatzResearch.WordTrace]
  refine ⟨30849298011771314611648963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41132397349028419482198617 30849298011771314611648963)
  ·
    refine ⟨46273947017656971917473445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30849298011771314611648963 46273947017656971917473445)
    ·
      refine ⟨8676365065810682234526271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46273947017656971917473445 8676365065810682234526271)
      ·
        refine ⟨13014547598716023351789407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8676365065810682234526271 13014547598716023351789407)
        ·
          refine ⟨19521821398074035027684111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13014547598716023351789407 19521821398074035027684111)
          ·
            refine ⟨29282732097111052541526167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19521821398074035027684111 29282732097111052541526167)
            ·
              refine ⟨43924098145666578812289251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29282732097111052541526167 43924098145666578812289251)
              ·
                refine ⟨65886147218499868218433877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43924098145666578812289251 65886147218499868218433877)
                ·
                  refine ⟨193025821929198832671193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65886147218499868218433877 193025821929198832671193)
                  ·
                    rfl

theorem cell22_1691624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_1691624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691624 prefixEnd_1691624 := by exact prefixLift 1691624
  have htrace : WordTrace (prefixWord ++ tailWord_1691624) baseStart_1691624 baseEnd_1691624 := by
    simpa [prefixWord, tailWord_1691624, baseEnd_1691624] using wordTrace_append hprefix tailTrace_1691624
  have hstable : (prefixWord ++ tailWord_1691624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691624).length < 2 ^ (prefixWord ++ tailWord_1691624).sum := by decide
  have hdescent : baseEnd_1691624 < baseStart_1691624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691641 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 6]
def baseStart_1691641 : Nat := 118140960795 + 1691641 * 2 ^ 59
def prefixEnd_1691641 : Nat := 4983230072969 + 3 ^ 40 * 1691641 * 2
def baseEnd_1691641 : Nat := 193027761745004706779509

theorem tailTrace_1691641 : CollatzResearch.WordTrace tailWord_1691641 prefixEnd_1691641 193027761745004706779509 := by
  unfold tailWord_1691641
  simp only [CollatzResearch.WordTrace]
  refine ⟨61699216064481041126666777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41132810709654027417777851 61699216064481041126666777)
  ·
    refine ⟨46274412048360780845000083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61699216064481041126666777 46274412048360780845000083)
    ·
      refine ⟨69411618072541171267500125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46274412048360780845000083 69411618072541171267500125)
      ·
        refine ⟨26029356777202939225312547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69411618072541171267500125 26029356777202939225312547)
        ·
          refine ⟨39044035165804408837968821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26029356777202939225312547 39044035165804408837968821)
          ·
            refine ⟨3660378296794163328559577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39044035165804408837968821 3660378296794163328559577)
            ·
              refine ⟨2745283722595622496419683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660378296794163328559577 2745283722595622496419683)
              ·
                refine ⟨4117925583893433744629525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745283722595622496419683 4117925583893433744629525)
                ·
                  refine ⟨193027761745004706779509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4117925583893433744629525 193027761745004706779509)
                  ·
                    rfl

theorem cell22_1691641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_1691641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691641 prefixEnd_1691641 := by exact prefixLift 1691641
  have htrace : WordTrace (prefixWord ++ tailWord_1691641) baseStart_1691641 baseEnd_1691641 := by
    simpa [prefixWord, tailWord_1691641, baseEnd_1691641] using wordTrace_append hprefix tailTrace_1691641
  have hstable : (prefixWord ++ tailWord_1691641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691641).length < 2 ^ (prefixWord ++ tailWord_1691641).sum := by decide
  have hdescent : baseEnd_1691641 < baseStart_1691641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691761 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1691761 : Nat := 118140960795 + 1691761 * 2 ^ 59
def prefixEnd_1691761 : Nat := 4983230072969 + 3 ^ 40 * 1691761 * 2
def baseEnd_1691761 : Nat := 579124363687373807338159

theorem tailTrace_1691761 : CollatzResearch.WordTrace tailWord_1691761 prefixEnd_1691761 579124363687373807338159 := by
  unfold tailWord_1691761
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703592824046301621035137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41135728549364201080690091 61703592824046301621035137)
  ·
    refine ⟨46277694618034726215776353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61703592824046301621035137 46277694618034726215776353)
    ·
      refine ⟨34708270963526044661832265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46277694618034726215776353 34708270963526044661832265)
      ·
        refine ⟨26031203222644533496374199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34708270963526044661832265 26031203222644533496374199)
        ·
          refine ⟨39046804833966800244561299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26031203222644533496374199 39046804833966800244561299)
          ·
            refine ⟨58570207250950200366841949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39046804833966800244561299 58570207250950200366841949)
            ·
              refine ⟨21963827719106325137565731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58570207250950200366841949 21963827719106325137565731)
              ·
                refine ⟨32945741578659487706348597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21963827719106325137565731 32945741578659487706348597)
                ·
                  refine ⟨3088663272999326972470181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32945741578659487706348597 3088663272999326972470181)
                  ·
                    refine ⟨579124363687373807338159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3088663272999326972470181 579124363687373807338159)
                    ·
                      rfl

theorem cell22_1691761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1691761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691761 prefixEnd_1691761 := by exact prefixLift 1691761
  have htrace : WordTrace (prefixWord ++ tailWord_1691761) baseStart_1691761 baseEnd_1691761 := by
    simpa [prefixWord, tailWord_1691761, baseEnd_1691761] using wordTrace_append hprefix tailTrace_1691761
  have hstable : (prefixWord ++ tailWord_1691761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691761).length < 2 ^ (prefixWord ++ tailWord_1691761).sum := by decide
  have hdescent : baseEnd_1691761 < baseStart_1691761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691810 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1691810 : Nat := 118140960795 + 1691810 * 2 ^ 59
def prefixEnd_1691810 : Nat := 4983230072969 + 3 ^ 40 * 1691810 * 2
def baseEnd_1691810 : Nat := 193047045796251337621003

theorem tailTrace_1691810 : CollatzResearch.WordTrace tailWord_1691810 prefixEnd_1691810 193047045796251337621003 := by
  unfold tailWord_1691810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426345000217195747392221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41136920000579188659712589 15426345000217195747392221)
  ·
    refine ⟨5784879375081448405272083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15426345000217195747392221 5784879375081448405272083)
    ·
      refine ⟨8677319062622172607908125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5784879375081448405272083 8677319062622172607908125)
      ·
        refine ⟨3253994648483314727965547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8677319062622172607908125 3253994648483314727965547)
        ·
          refine ⟨4880991972724972091948321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253994648483314727965547 4880991972724972091948321)
          ·
            refine ⟨3660743979543729068961241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880991972724972091948321 3660743979543729068961241)
            ·
              refine ⟨2745557984657796801720931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660743979543729068961241 2745557984657796801720931)
              ·
                refine ⟨4118336976986695202581397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745557984657796801720931 4118336976986695202581397)
                ·
                  refine ⟨193047045796251337621003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4118336976986695202581397 193047045796251337621003)
                  ·
                    rfl

theorem cell22_1691810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1691810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691810 prefixEnd_1691810 := by exact prefixLift 1691810
  have htrace : WordTrace (prefixWord ++ tailWord_1691810) baseStart_1691810 baseEnd_1691810 := by
    simpa [prefixWord, tailWord_1691810, baseEnd_1691810] using wordTrace_append hprefix tailTrace_1691810
  have hstable : (prefixWord ++ tailWord_1691810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691810).length < 2 ^ (prefixWord ++ tailWord_1691810).sum := by decide
  have hdescent : baseEnd_1691810 < baseStart_1691810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691883 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 5]
def baseStart_1691883 : Nat := 118140960795 + 1691883 * 2 ^ 59
def prefixEnd_1691883 : Nat := 4983230072969 + 3 ^ 40 * 1691883 * 2
def baseEnd_1691883 : Nat := 193055375593535385262595

theorem tailTrace_1691883 : CollatzResearch.WordTrace tailWord_1691883 prefixEnd_1691883 193055375593535385262595 := by
  unfold tailWord_1691883
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708042529604316456976303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41138695019736210971317535 61708042529604316456976303)
  ·
    refine ⟨92562063794406474685464455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61708042529604316456976303 92562063794406474685464455)
    ·
      refine ⟨138843095691609712028196683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92562063794406474685464455 138843095691609712028196683)
      ·
        refine ⟨208264643537414568042295025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138843095691609712028196683 208264643537414568042295025)
        ·
          refine ⟨156198482653060926031721269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208264643537414568042295025 156198482653060926031721269)
          ·
            refine ⟨14643607748724461815473869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156198482653060926031721269 14643607748724461815473869)
            ·
              refine ⟨5491352905771673180802701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643607748724461815473869 5491352905771673180802701)
              ·
                refine ⟨2059257339664377442801013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5491352905771673180802701 2059257339664377442801013)
                ·
                  refine ⟨193055375593535385262595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059257339664377442801013 193055375593535385262595)
                  ·
                    rfl

theorem cell22_1691883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].length) (baseStart_1691883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691883 prefixEnd_1691883 := by exact prefixLift 1691883
  have htrace : WordTrace (prefixWord ++ tailWord_1691883) baseStart_1691883 baseEnd_1691883 := by
    simpa [prefixWord, tailWord_1691883, baseEnd_1691883] using wordTrace_append hprefix tailTrace_1691883
  have hstable : (prefixWord ++ tailWord_1691883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691883).length < 2 ^ (prefixWord ++ tailWord_1691883).sum := by decide
  have hdescent : baseEnd_1691883 < baseStart_1691883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691928 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_1691928 : Nat := 118140960795 + 1691928 * 2 ^ 59
def prefixEnd_1691928 : Nat := 4983230072969 + 3 ^ 40 * 1691928 * 2
def baseEnd_1691928 : Nat := 193060510400080346137549

theorem tailTrace_1691928 : CollatzResearch.WordTrace tailWord_1691928 prefixEnd_1691928 193060510400080346137549 := by
  unfold tailWord_1691928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854841907220644571182219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41139789209627526094909625 30854841907220644571182219)
  ·
    refine ⟨46282262860830966856773329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30854841907220644571182219 46282262860830966856773329)
    ·
      refine ⟨34711697145623225142579997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46282262860830966856773329 34711697145623225142579997)
      ·
        refine ⟨13016886429608709428467499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34711697145623225142579997 13016886429608709428467499)
        ·
          refine ⟨19525329644413064142701249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016886429608709428467499 19525329644413064142701249)
          ·
            refine ⟨14643997233309798107025937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19525329644413064142701249 14643997233309798107025937)
            ·
              refine ⟨10982997924982348580269453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643997233309798107025937 10982997924982348580269453)
              ·
                refine ⟨4118624221868380717601045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10982997924982348580269453 4118624221868380717601045)
                ·
                  refine ⟨193060510400080346137549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4118624221868380717601045 193060510400080346137549)
                  ·
                    rfl

theorem cell22_1691928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_1691928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691928 prefixEnd_1691928 := by exact prefixLift 1691928
  have htrace : WordTrace (prefixWord ++ tailWord_1691928) baseStart_1691928 baseEnd_1691928 := by
    simpa [prefixWord, tailWord_1691928, baseEnd_1691928] using wordTrace_append hprefix tailTrace_1691928
  have hstable : (prefixWord ++ tailWord_1691928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691928).length < 2 ^ (prefixWord ++ tailWord_1691928).sum := by decide
  have hdescent : baseEnd_1691928 < baseStart_1691928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691962 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1691962 : Nat := 118140960795 + 1691962 * 2 ^ 59
def prefixEnd_1691962 : Nat := 4983230072969 + 3 ^ 40 * 1691962 * 2
def baseEnd_1691962 : Nat := 193064390031692094354181

theorem tailTrace_1691962 : CollatzResearch.WordTrace tailWord_1691962 prefixEnd_1691962 193064390031692094354181 := by
  unfold tailWord_1691962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427730974079528237275535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41140615930878741966068093 15427730974079528237275535)
  ·
    refine ⟨23141596461119292355913303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15427730974079528237275535 23141596461119292355913303)
    ·
      refine ⟨34712394691678938533869955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23141596461119292355913303 34712394691678938533869955)
      ·
        refine ⟨52068592037518407800804933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34712394691678938533869955 52068592037518407800804933)
        ·
          refine ⟨9762861007034701462650925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52068592037518407800804933 9762861007034701462650925)
          ·
            refine ⟨3661072877638013048494097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9762861007034701462650925 3661072877638013048494097)
            ·
              refine ⟨2745804658228509786370573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661072877638013048494097 2745804658228509786370573)
              ·
                refine ⟨1029676746835691169888965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745804658228509786370573 1029676746835691169888965)
                ·
                  refine ⟨193064390031692094354181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029676746835691169888965 193064390031692094354181)
                  ·
                    rfl

theorem cell22_1691962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1691962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1691962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1691962 prefixEnd_1691962 := by exact prefixLift 1691962
  have htrace : WordTrace (prefixWord ++ tailWord_1691962) baseStart_1691962 baseEnd_1691962 := by
    simpa [prefixWord, tailWord_1691962, baseEnd_1691962] using wordTrace_append hprefix tailTrace_1691962
  have hstable : (prefixWord ++ tailWord_1691962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691962).length < 2 ^ (prefixWord ++ tailWord_1691962).sum := by decide
  have hdescent : baseEnd_1691962 < baseStart_1691962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692007 : List Nat := [1, 1, 5, 1, 3, 3, 2, 6]
def baseStart_1692007 : Nat := 118140960795 + 1692007 * 2 ^ 59
def prefixEnd_1692007 : Nat := 4983230072969 + 3 ^ 40 * 1692007 * 2
def baseEnd_1692007 : Nat := 64356508279412351743045

theorem tailTrace_1692007 : CollatzResearch.WordTrace tailWord_1692007 prefixEnd_1692007 64356508279412351743045 := by
  unfold tailWord_1692007
  simp only [CollatzResearch.WordTrace]
  refine ⟨61712565181155085634490275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41141710120770057089660183 61712565181155085634490275)
  ·
    refine ⟨92568847771732628451735413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61712565181155085634490275 92568847771732628451735413)
    ·
      refine ⟨8678329478599933917350195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92568847771732628451735413 8678329478599933917350195)
      ·
        refine ⟨13017494217899900876025293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678329478599933917350195 13017494217899900876025293)
        ·
          refine ⟨4881560331712462828509485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13017494217899900876025293 4881560331712462828509485)
          ·
            refine ⟨1830585124392173560691057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4881560331712462828509485 1830585124392173560691057)
            ·
              refine ⟨1372938843294130170518293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830585124392173560691057 1372938843294130170518293)
              ·
                refine ⟨64356508279412351743045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1372938843294130170518293 64356508279412351743045)
                ·
                  rfl

theorem cell22_1692007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 6].length) (baseStart_1692007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692007 prefixEnd_1692007 := by exact prefixLift 1692007
  have htrace : WordTrace (prefixWord ++ tailWord_1692007) baseStart_1692007 baseEnd_1692007 := by
    simpa [prefixWord, tailWord_1692007, baseEnd_1692007] using wordTrace_append hprefix tailTrace_1692007
  have hstable : (prefixWord ++ tailWord_1692007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692007).length < 2 ^ (prefixWord ++ tailWord_1692007).sum := by decide
  have hdescent : baseEnd_1692007 < baseStart_1692007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692110 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1692110 : Nat := 118140960795 + 1692110 * 2 ^ 59
def prefixEnd_1692110 : Nat := 4983230072969 + 3 ^ 40 * 1692110 * 2
def baseEnd_1692110 : Nat := 579243833519653230362089

theorem tailTrace_1692110 : CollatzResearch.WordTrace tailWord_1692110 prefixEnd_1692110 579243833519653230362089 := by
  unfold tailWord_1692110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714540237472741778186223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41144214599854622816993189 7714540237472741778186223)
  ·
    refine ⟨11571810356209112667279335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7714540237472741778186223 11571810356209112667279335)
    ·
      refine ⟨17357715534313669000919003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571810356209112667279335 17357715534313669000919003)
      ·
        refine ⟨26036573301470503501378505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357715534313669000919003 26036573301470503501378505)
        ·
          refine ⟨19527429976102877626033879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26036573301470503501378505 19527429976102877626033879)
          ·
            refine ⟨29291144964154316439050819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19527429976102877626033879 29291144964154316439050819)
            ·
              refine ⟨43936717446231474658576229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29291144964154316439050819 43936717446231474658576229)
              ·
                refine ⟨8238134521168401498483043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43936717446231474658576229 8238134521168401498483043)
                ·
                  refine ⟨12357201781752602247724565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238134521168401498483043 12357201781752602247724565)
                  ·
                    refine ⟨579243833519653230362089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12357201781752602247724565 579243833519653230362089)
                    ·
                      rfl

theorem cell22_1692110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1692110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692110 prefixEnd_1692110 := by exact prefixLift 1692110
  have htrace : WordTrace (prefixWord ++ tailWord_1692110) baseStart_1692110 baseEnd_1692110 := by
    simpa [prefixWord, tailWord_1692110, baseEnd_1692110] using wordTrace_append hprefix tailTrace_1692110
  have hstable : (prefixWord ++ tailWord_1692110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692110).length < 2 ^ (prefixWord ++ tailWord_1692110).sum := by decide
  have hdescent : baseEnd_1692110 < baseStart_1692110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692114 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1692114 : Nat := 118140960795 + 1692114 * 2 ^ 59
def prefixEnd_1692114 : Nat := 4983230072969 + 3 ^ 40 * 1692114 * 2
def baseEnd_1692114 : Nat := 193081734267132851087359

theorem tailTrace_1692114 : CollatzResearch.WordTrace tailWord_1692114 prefixEnd_1692114 193081734267132851087359 := by
  unfold tailWord_1692114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429116947941860727158849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41144311861178295272423597 15429116947941860727158849)
  ·
    refine ⟨11571837710956395545369137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15429116947941860727158849 11571837710956395545369137)
    ·
      refine ⟨8678878283217296659026853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11571837710956395545369137 8678878283217296659026853)
      ·
        refine ⟨1627289678103243123567535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8678878283217296659026853 1627289678103243123567535)
        ·
          refine ⟨2440934517154864685351303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627289678103243123567535 2440934517154864685351303)
          ·
            refine ⟨3661401775732297028026955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440934517154864685351303 3661401775732297028026955)
            ·
              refine ⟨5492102663598445542040433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661401775732297028026955 5492102663598445542040433)
              ·
                refine ⟨4119076997698834156530325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492102663598445542040433 4119076997698834156530325)
                ·
                  refine ⟨193081734267132851087359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4119076997698834156530325 193081734267132851087359)
                  ·
                    rfl

theorem cell22_1692114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1692114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692114 prefixEnd_1692114 := by exact prefixLift 1692114
  have htrace : WordTrace (prefixWord ++ tailWord_1692114) baseStart_1692114 baseEnd_1692114 := by
    simpa [prefixWord, tailWord_1692114, baseEnd_1692114] using wordTrace_append hprefix tailTrace_1692114
  have hstable : (prefixWord ++ tailWord_1692114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692114).length < 2 ^ (prefixWord ++ tailWord_1692114).sum := by decide
  have hdescent : baseEnd_1692114 < baseStart_1692114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692127 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_1692127 : Nat := 118140960795 + 1692127 * 2 ^ 59
def prefixEnd_1692127 : Nat := 4983230072969 + 3 ^ 40 * 1692127 * 2
def baseEnd_1692127 : Nat := 579249652967070852687037

theorem tailTrace_1692127 : CollatzResearch.WordTrace tailWord_1692127 prefixEnd_1692127 579249652967070852687037 := by
  unfold tailWord_1692127
  simp only [CollatzResearch.WordTrace]
  refine ⟨61716941940720346128858635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41144627960480230752572423 61716941940720346128858635)
  ·
    refine ⟨92575412911080519193287953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61716941940720346128858635 92575412911080519193287953)
    ·
      refine ⟨69431559683310389394965965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92575412911080519193287953 69431559683310389394965965)
      ·
        refine ⟨26036834881241396023112237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69431559683310389394965965 26036834881241396023112237)
        ·
          refine ⟨9763813080465523508667089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26036834881241396023112237 9763813080465523508667089)
          ·
            refine ⟨7322859810349142631500317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9763813080465523508667089 7322859810349142631500317)
            ·
              refine ⟨2746072428880928486812619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7322859810349142631500317 2746072428880928486812619)
              ·
                refine ⟨4119108643321392730218929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746072428880928486812619 4119108643321392730218929)
                ·
                  refine ⟨3089331482491044547664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119108643321392730218929 3089331482491044547664197)
                  ·
                    refine ⟨579249652967070852687037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089331482491044547664197 579249652967070852687037)
                    ·
                      rfl

theorem cell22_1692127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_1692127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692127 prefixEnd_1692127 := by exact prefixLift 1692127
  have htrace : WordTrace (prefixWord ++ tailWord_1692127) baseStart_1692127 baseEnd_1692127 := by
    simpa [prefixWord, tailWord_1692127, baseEnd_1692127] using wordTrace_append hprefix tailTrace_1692127
  have hstable : (prefixWord ++ tailWord_1692127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692127).length < 2 ^ (prefixWord ++ tailWord_1692127).sum := by decide
  have hdescent : baseEnd_1692127 < baseStart_1692127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692133 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_1692133 : Nat := 118140960795 + 1692133 * 2 ^ 59
def prefixEnd_1692133 : Nat := 4983230072969 + 3 ^ 40 * 1692133 * 2
def baseEnd_1692133 : Nat := 579251706889688837037019

theorem tailTrace_1692133 : CollatzResearch.WordTrace tailWord_1692133 prefixEnd_1692133 579251706889688837037019 := by
  unfold tailWord_1692133
  simp only [CollatzResearch.WordTrace]
  refine ⟨61717160778698609153577053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41144773852465739435718035 61717160778698609153577053)
  ·
    refine ⟨23143935292011978432591395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61717160778698609153577053 23143935292011978432591395)
    ·
      refine ⟨34715902938017967648887093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23143935292011978432591395 34715902938017967648887093)
      ·
        refine ⟨3254615900439184467083165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34715902938017967648887093 3254615900439184467083165)
        ·
          refine ⟨1220480962664694175156187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3254615900439184467083165 1220480962664694175156187)
          ·
            refine ⟨1830721443997041262734281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220480962664694175156187 1830721443997041262734281)
            ·
              refine ⟨1373041082997780947050711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830721443997041262734281 1373041082997780947050711)
              ·
                refine ⟨2059561624496671420576067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373041082997780947050711 2059561624496671420576067)
                ·
                  refine ⟨3089342436745007130864101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059561624496671420576067 3089342436745007130864101)
                  ·
                    refine ⟨579251706889688837037019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089342436745007130864101 579251706889688837037019)
                    ·
                      rfl

theorem cell22_1692133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_1692133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692133 prefixEnd_1692133 := by exact prefixLift 1692133
  have htrace : WordTrace (prefixWord ++ tailWord_1692133) baseStart_1692133 baseEnd_1692133 := by
    simpa [prefixWord, tailWord_1692133, baseEnd_1692133] using wordTrace_append hprefix tailTrace_1692133
  have hstable : (prefixWord ++ tailWord_1692133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692133).length < 2 ^ (prefixWord ++ tailWord_1692133).sum := by decide
  have hdescent : baseEnd_1692133 < baseStart_1692133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692174 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1692174 : Nat := 118140960795 + 1692174 * 2 ^ 59
def prefixEnd_1692174 : Nat := 4983230072969 + 3 ^ 40 * 1692174 * 2
def baseEnd_1692174 : Nat := 579265742027578396761893

theorem tailTrace_1692174 : CollatzResearch.WordTrace tailWord_1692174 prefixEnd_1692174 579265742027578396761893 := by
  unfold tailWord_1692174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714832021443759144477447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41145770781033382103879717 7714832021443759144477447)
  ·
    refine ⟨11572248032165638716716171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7714832021443759144477447 11572248032165638716716171)
    ·
      refine ⟨17358372048248458075074257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11572248032165638716716171 17358372048248458075074257)
      ·
        refine ⟨13018779036186343556305693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17358372048248458075074257 13018779036186343556305693)
        ·
          refine ⟨4882042138569878833614635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13018779036186343556305693 4882042138569878833614635)
          ·
            refine ⟨7323063207854818250421953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882042138569878833614635 7323063207854818250421953)
            ·
              refine ⟨5492297405891113687816465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7323063207854818250421953 5492297405891113687816465)
              ·
                refine ⟨4119223054418335265862349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492297405891113687816465 4119223054418335265862349)
                ·
                  refine ⟨1544708645406875724698381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4119223054418335265862349 1544708645406875724698381)
                  ·
                    refine ⟨579265742027578396761893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544708645406875724698381 579265742027578396761893)
                    ·
                      rfl

theorem cell22_1692174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1692174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692174 prefixEnd_1692174 := by exact prefixLift 1692174
  have htrace : WordTrace (prefixWord ++ tailWord_1692174) baseStart_1692174 baseEnd_1692174 := by
    simpa [prefixWord, tailWord_1692174, baseEnd_1692174] using wordTrace_append hprefix tailTrace_1692174
  have hstable : (prefixWord ++ tailWord_1692174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692174).length < 2 ^ (prefixWord ++ tailWord_1692174).sum := by decide
  have hdescent : baseEnd_1692174 < baseStart_1692174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692217 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1692217 : Nat := 118140960795 + 1692217 * 2 ^ 59
def prefixEnd_1692217 : Nat := 4983230072969 + 3 ^ 40 * 1692217 * 2
def baseEnd_1692217 : Nat := 579280461806340617936761

theorem tailTrace_1692217 : CollatzResearch.WordTrace tailWord_1692217 prefixEnd_1692217 579280461806340617936761 := by
  unfold tailWord_1692217
  simp only [CollatzResearch.WordTrace]
  refine ⟨61720224510394291499634905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41146816340262860999756603 61720224510394291499634905)
  ·
    refine ⟨46290168382795718624726179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61720224510394291499634905 46290168382795718624726179)
    ·
      refine ⟨69435252574193577937089269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46290168382795718624726179 69435252574193577937089269)
      ·
        refine ⟨6509554928830647931602119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69435252574193577937089269 6509554928830647931602119)
        ·
          refine ⟨9764332393245971897403179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509554928830647931602119 9764332393245971897403179)
          ·
            refine ⟨14646498589868957846104769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764332393245971897403179 14646498589868957846104769)
            ·
              refine ⟨10984873942401718384578577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14646498589868957846104769 10984873942401718384578577)
              ·
                refine ⟨8238655456801288788433933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984873942401718384578577 8238655456801288788433933)
                ·
                  refine ⟨3089495796300483295662725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8238655456801288788433933 3089495796300483295662725)
                  ·
                    refine ⟨579280461806340617936761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089495796300483295662725 579280461806340617936761)
                    ·
                      rfl

theorem cell22_1692217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1692217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692217 prefixEnd_1692217 := by exact prefixLift 1692217
  have htrace : WordTrace (prefixWord ++ tailWord_1692217) baseStart_1692217 baseEnd_1692217 := by
    simpa [prefixWord, tailWord_1692217, baseEnd_1692217] using wordTrace_append hprefix tailTrace_1692217
  have hstable : (prefixWord ++ tailWord_1692217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692217).length < 2 ^ (prefixWord ++ tailWord_1692217).sum := by decide
  have hdescent : baseEnd_1692217 < baseStart_1692217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692221 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 5]
def baseStart_1692221 : Nat := 118140960795 + 1692221 * 2 ^ 59
def prefixEnd_1692221 : Nat := 4983230072969 + 3 ^ 40 * 1692221 * 2
def baseEnd_1692221 : Nat := 193093943696028646945583

theorem tailTrace_1692221 : CollatzResearch.WordTrace tailWord_1692221 prefixEnd_1692221 193093943696028646945583 := by
  unfold tailWord_1692221
  simp only [CollatzResearch.WordTrace]
  refine ⟨61720370402379800182780517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41146913601586533455187011 61720370402379800182780517)
  ·
    refine ⟨11572569450446212534271347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61720370402379800182780517 11572569450446212534271347)
    ·
      refine ⟨17358854175669318801407021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11572569450446212534271347 17358854175669318801407021)
      ·
        refine ⟨6509570315875994550527633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17358854175669318801407021 6509570315875994550527633)
        ·
          refine ⟨4882177736906995912895725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6509570315875994550527633 4882177736906995912895725)
          ·
            refine ⟨1830816651340123467335897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4882177736906995912895725 1830816651340123467335897)
            ·
              refine ⟨1373112488505092600501923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830816651340123467335897 1373112488505092600501923)
              ·
                refine ⟨2059668732757638900752885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373112488505092600501923 2059668732757638900752885)
                ·
                  refine ⟨193093943696028646945583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2059668732757638900752885 193093943696028646945583)
                  ·
                    rfl

theorem cell22_1692221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_1692221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692221 prefixEnd_1692221 := by exact prefixLift 1692221
  have htrace : WordTrace (prefixWord ++ tailWord_1692221) baseStart_1692221 baseEnd_1692221 := by
    simpa [prefixWord, tailWord_1692221, baseEnd_1692221] using wordTrace_append hprefix tailTrace_1692221
  have hstable : (prefixWord ++ tailWord_1692221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692221).length < 2 ^ (prefixWord ++ tailWord_1692221).sum := by decide
  have hdescent : baseEnd_1692221 < baseStart_1692221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692234 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1692234 : Nat := 118140960795 + 1692234 * 2 ^ 59
def prefixEnd_1692234 : Nat := 4983230072969 + 3 ^ 40 * 1692234 * 2
def baseEnd_1692234 : Nat := 579286281253758240261709

theorem tailTrace_1692234 : CollatzResearch.WordTrace tailWord_1692234 prefixEnd_1692234 579286281253758240261709 := by
  unfold tailWord_1692234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430211137833175850750939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41147229700888468935335837 15430211137833175850750939)
  ·
    refine ⟨23145316706749763776126409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15430211137833175850750939 23145316706749763776126409)
    ·
      refine ⟨17358987530062322832094807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23145316706749763776126409 17358987530062322832094807)
      ·
        refine ⟨26038481295093484248142211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358987530062322832094807 26038481295093484248142211)
        ·
          refine ⟨39057721942640226372213317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26038481295093484248142211 39057721942640226372213317)
          ·
            refine ⟨7323322864245042444789997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39057721942640226372213317 7323322864245042444789997)
            ·
              refine ⟨2746246074091890916796249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7323322864245042444789997 2746246074091890916796249)
              ·
                refine ⟨2059684555568918187597187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746246074091890916796249 2059684555568918187597187)
                ·
                  refine ⟨3089526833353377281395781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059684555568918187597187 3089526833353377281395781)
                  ·
                    refine ⟨579286281253758240261709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089526833353377281395781 579286281253758240261709)
                    ·
                      rfl

theorem cell22_1692234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1692234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692234 prefixEnd_1692234 := by exact prefixLift 1692234
  have htrace : WordTrace (prefixWord ++ tailWord_1692234) baseStart_1692234 baseEnd_1692234 := by
    simpa [prefixWord, tailWord_1692234, baseEnd_1692234] using wordTrace_append hprefix tailTrace_1692234
  have hstable : (prefixWord ++ tailWord_1692234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692234).length < 2 ^ (prefixWord ++ tailWord_1692234).sum := by decide
  have hdescent : baseEnd_1692234 < baseStart_1692234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692247 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1692247 : Nat := 118140960795 + 1692247 * 2 ^ 59
def prefixEnd_1692247 : Nat := 4983230072969 + 3 ^ 40 * 1692247 * 2
def baseEnd_1692247 : Nat := 579290731419430539686669

theorem tailTrace_1692247 : CollatzResearch.WordTrace tailWord_1692247 prefixEnd_1692247 579290731419430539686669 := by
  unfold tailWord_1692247
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721318700285606623226995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41147545800190404415484663 61721318700285606623226995)
  ·
    refine ⟨92581978050428409934840493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61721318700285606623226995 92581978050428409934840493)
    ·
      refine ⟨34718241768910653725565185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92581978050428409934840493 34718241768910653725565185)
      ·
        refine ⟨26038681326682990294173889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34718241768910653725565185 26038681326682990294173889)
        ·
          refine ⟨19529010995012242720630417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26038681326682990294173889 19529010995012242720630417)
          ·
            refine ⟨14646758246259182040472813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19529010995012242720630417 14646758246259182040472813)
            ·
              refine ⟨5492534342347193265177305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14646758246259182040472813 5492534342347193265177305)
              ·
                refine ⟨4119400756760394948882979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492534342347193265177305 4119400756760394948882979)
                ·
                  refine ⟨6179101135140592423324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119400756760394948882979 6179101135140592423324469)
                  ·
                    refine ⟨579290731419430539686669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6179101135140592423324469 579290731419430539686669)
                    ·
                      rfl

theorem cell22_1692247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1692247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692247 prefixEnd_1692247 := by exact prefixLift 1692247
  have htrace : WordTrace (prefixWord ++ tailWord_1692247) baseStart_1692247 baseEnd_1692247 := by
    simpa [prefixWord, tailWord_1692247, baseEnd_1692247] using wordTrace_append hprefix tailTrace_1692247
  have hstable : (prefixWord ++ tailWord_1692247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692247).length < 2 ^ (prefixWord ++ tailWord_1692247).sum := by decide
  have hdescent : baseEnd_1692247 < baseStart_1692247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692369 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1692369 : Nat := 118140960795 + 1692369 * 2 ^ 59
def prefixEnd_1692369 : Nat := 4983230072969 + 3 ^ 40 * 1692369 * 2
def baseEnd_1692369 : Nat := 579332494512662888136295

theorem tailTrace_1692369 : CollatzResearch.WordTrace tailWord_1692369 prefixEnd_1692369 579332494512662888136295 := by
  unfold tailWord_1692369
  simp only [CollatzResearch.WordTrace]
  refine ⟨61725768405843621459168161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41150512270562414306112107 61725768405843621459168161)
  ·
    refine ⟨46294326304382716094376121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61725768405843621459168161 46294326304382716094376121)
    ·
      refine ⟨34720744728287037070782091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46294326304382716094376121 34720744728287037070782091)
      ·
        refine ⟨52081117092430555606173137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34720744728287037070782091 52081117092430555606173137)
        ·
          refine ⟨39060837819322916704629853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52081117092430555606173137 39060837819322916704629853)
          ·
            refine ⟨14647814182246093764236195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39060837819322916704629853 14647814182246093764236195)
            ·
              refine ⟨21971721273369140646354293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647814182246093764236195 21971721273369140646354293)
              ·
                refine ⟨2059848869378356935595715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21971721273369140646354293 2059848869378356935595715)
                ·
                  refine ⟨3089773304067535403393573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059848869378356935595715 3089773304067535403393573)
                  ·
                    refine ⟨579332494512662888136295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3089773304067535403393573 579332494512662888136295)
                    ·
                      rfl

theorem cell22_1692369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1692369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692369 prefixEnd_1692369 := by exact prefixLift 1692369
  have htrace : WordTrace (prefixWord ++ tailWord_1692369) baseStart_1692369 baseEnd_1692369 := by
    simpa [prefixWord, tailWord_1692369, baseEnd_1692369] using wordTrace_append hprefix tailTrace_1692369
  have hstable : (prefixWord ++ tailWord_1692369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692369).length < 2 ^ (prefixWord ++ tailWord_1692369).sum := by decide
  have hdescent : baseEnd_1692369 < baseStart_1692369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692484 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1692484 : Nat := 118140960795 + 1692484 * 2 ^ 59
def prefixEnd_1692484 : Nat := 4983230072969 + 3 ^ 40 * 1692484 * 2
def baseEnd_1692484 : Nat := 579371861362840921510943

theorem tailTrace_1692484 : CollatzResearch.WordTrace tailWord_1692484 prefixEnd_1692484 579371861362840921510943 := by
  unfold tailWord_1692484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864981400213498049802253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41153308533617997399736337 30864981400213498049802253)
  ·
    refine ⟨11574368025080061768675845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30864981400213498049802253 11574368025080061768675845)
    ·
      refine ⟨2170194004702511581626721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11574368025080061768675845 2170194004702511581626721)
      ·
        refine ⟨1627645503526883686220041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170194004702511581626721 1627645503526883686220041)
        ·
          refine ⟨1220734127645162764665031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627645503526883686220041 1220734127645162764665031)
          ·
            refine ⟨1831101191467744146997547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220734127645162764665031 1831101191467744146997547)
            ·
              refine ⟨2746651787201616220496321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831101191467744146997547 2746651787201616220496321)
              ·
                refine ⟨2059988840401212165372241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746651787201616220496321 2059988840401212165372241)
                ·
                  refine ⟨1544991630300909124029181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2059988840401212165372241 1544991630300909124029181)
                  ·
                    refine ⟨579371861362840921510943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1544991630300909124029181 579371861362840921510943)
                    ·
                      rfl

theorem cell22_1692484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1692484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692484 prefixEnd_1692484 := by exact prefixLift 1692484
  have htrace : WordTrace (prefixWord ++ tailWord_1692484) baseStart_1692484 baseEnd_1692484 := by
    simpa [prefixWord, tailWord_1692484, baseEnd_1692484] using wordTrace_append hprefix tailTrace_1692484
  have hstable : (prefixWord ++ tailWord_1692484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692484).length < 2 ^ (prefixWord ++ tailWord_1692484).sum := by decide
  have hdescent : baseEnd_1692484 < baseStart_1692484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692489 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1692489 : Nat := 118140960795 + 1692489 * 2 ^ 59
def prefixEnd_1692489 : Nat := 4983230072969 + 3 ^ 40 * 1692489 * 2
def baseEnd_1692489 : Nat := 579373572965022575135927

theorem tailTrace_1692489 : CollatzResearch.WordTrace tailWord_1692489 prefixEnd_1692489 579373572965022575135927 := by
  unfold tailWord_1692489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61730145165408881953536521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41153430110272587969024347 61730145165408881953536521)
  ·
    refine ⟨46297608874056661465152391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61730145165408881953536521 46297608874056661465152391)
    ·
      refine ⟨69446413311084992197728587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46297608874056661465152391 69446413311084992197728587)
      ·
        refine ⟨104169619966627488296592881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69446413311084992197728587 104169619966627488296592881)
        ·
          refine ⟨78127214974970616222444661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104169619966627488296592881 78127214974970616222444661)
          ·
            refine ⟨7324426403903495270854187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78127214974970616222444661 7324426403903495270854187)
            ·
              refine ⟨10986639605855242906281281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324426403903495270854187 10986639605855242906281281)
              ·
                refine ⟨8239979704391432179710961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10986639605855242906281281 8239979704391432179710961)
                ·
                  refine ⟨6179984778293574134783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239979704391432179710961 6179984778293574134783221)
                  ·
                    refine ⟨579373572965022575135927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6179984778293574134783221 579373572965022575135927)
                    ·
                      rfl

theorem cell22_1692489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1692489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692489 prefixEnd_1692489 := by exact prefixLift 1692489
  have htrace : WordTrace (prefixWord ++ tailWord_1692489) baseStart_1692489 baseEnd_1692489 := by
    simpa [prefixWord, tailWord_1692489, baseEnd_1692489] using wordTrace_append hprefix tailTrace_1692489
  have hstable : (prefixWord ++ tailWord_1692489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692489).length < 2 ^ (prefixWord ++ tailWord_1692489).sum := by decide
  have hdescent : baseEnd_1692489 < baseStart_1692489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692504 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_1692504 : Nat := 118140960795 + 1692504 * 2 ^ 59
def prefixEnd_1692504 : Nat := 4983230072969 + 3 ^ 40 * 1692504 * 2
def baseEnd_1692504 : Nat := 579378707771567536010881

theorem tailTrace_1692504 : CollatzResearch.WordTrace tailWord_1692504 prefixEnd_1692504 579378707771567536010881 := by
  unfold tailWord_1692504
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865346130177269757666283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41153794840236359676888377 30865346130177269757666283)
  ·
    refine ⟨46298019195265904636499425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30865346130177269757666283 46298019195265904636499425)
    ·
      refine ⟨34723514396449428477374569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46298019195265904636499425 34723514396449428477374569)
      ·
        refine ⟨26042635797337071358030927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34723514396449428477374569 26042635797337071358030927)
        ·
          refine ⟨39063953696005607037046391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26042635797337071358030927 39063953696005607037046391)
          ·
            refine ⟨58595930544008410555569587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39063953696005607037046391 58595930544008410555569587)
            ·
              refine ⟨87893895816012615833354381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58595930544008410555569587 87893895816012615833354381)
              ·
                refine ⟨32960210931004730937507893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87893895816012615833354381 32960210931004730937507893)
                ·
                  refine ⟨3090019774781693525391365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32960210931004730937507893 3090019774781693525391365)
                  ·
                    refine ⟨579378707771567536010881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3090019774781693525391365 579378707771567536010881)
                    ·
                      rfl

theorem cell22_1692504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_1692504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692504 prefixEnd_1692504 := by exact prefixLift 1692504
  have htrace : WordTrace (prefixWord ++ tailWord_1692504) baseStart_1692504 baseEnd_1692504 := by
    simpa [prefixWord, tailWord_1692504, baseEnd_1692504] using wordTrace_append hprefix tailTrace_1692504
  have hstable : (prefixWord ++ tailWord_1692504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692504).length < 2 ^ (prefixWord ++ tailWord_1692504).sum := by decide
  have hdescent : baseEnd_1692504 < baseStart_1692504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692536 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_1692536 : Nat := 118140960795 + 1692536 * 2 ^ 59
def prefixEnd_1692536 : Nat := 4983230072969 + 3 ^ 40 * 1692536 * 2
def baseEnd_1692536 : Nat := 193129887341843373070261

theorem tailTrace_1692536 : CollatzResearch.WordTrace tailWord_1692536 prefixEnd_1692536 193129887341843373070261 := by
  unfold tailWord_1692536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30865929698119304490248731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41154572930825739320331641 30865929698119304490248731)
  ·
    refine ⟨46298894547178956735373097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30865929698119304490248731 46298894547178956735373097)
    ·
      refine ⟨34724170910384217551529823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46298894547178956735373097 34724170910384217551529823)
      ·
        refine ⟨52086256365576326327294735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34724170910384217551529823 52086256365576326327294735)
        ·
          refine ⟨78129384548364489490942103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52086256365576326327294735 78129384548364489490942103)
          ·
            refine ⟨117194076822546734236413155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78129384548364489490942103 117194076822546734236413155)
            ·
              refine ⟨175791115233820101354619733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117194076822546734236413155 175791115233820101354619733)
              ·
                refine ⟨1030026065823164656374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 175791115233820101354619733 1030026065823164656374725)
                ·
                  refine ⟨193129887341843373070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030026065823164656374725 193129887341843373070261)
                  ·
                    rfl

theorem cell22_1692536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_1692536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692536 prefixEnd_1692536 := by exact prefixLift 1692536
  have htrace : WordTrace (prefixWord ++ tailWord_1692536) baseStart_1692536 baseEnd_1692536 := by
    simpa [prefixWord, tailWord_1692536, baseEnd_1692536] using wordTrace_append hprefix tailTrace_1692536
  have hstable : (prefixWord ++ tailWord_1692536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692536).length < 2 ^ (prefixWord ++ tailWord_1692536).sum := by decide
  have hdescent : baseEnd_1692536 < baseStart_1692536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692546 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1692546 : Nat := 118140960795 + 1692546 * 2 ^ 59
def prefixEnd_1692546 : Nat := 4983230072969 + 3 ^ 40 * 1692546 * 2
def baseEnd_1692546 : Nat := 579393085229893426460753

theorem tailTrace_1692546 : CollatzResearch.WordTrace tailWord_1692546 prefixEnd_1692546 579393085229893426460753 := by
  unfold tailWord_1692546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433056031550595172090373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41154816084134920458907661 15433056031550595172090373)
  ·
    refine ⟨2893698005915736594766945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15433056031550595172090373 2893698005915736594766945)
    ·
      refine ⟨2170273504436802446075209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893698005915736594766945 2170273504436802446075209)
      ·
        refine ⟨1627705128327601834556407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170273504436802446075209 1627705128327601834556407)
        ·
          refine ⟨2441557692491402751834611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627705128327601834556407 2441557692491402751834611)
          ·
            refine ⟨3662336538737104127751917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441557692491402751834611 3662336538737104127751917)
            ·
              refine ⟨1373376202026414047906969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3662336538737104127751917 1373376202026414047906969)
              ·
                refine ⟨1030032151519810535930227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373376202026414047906969 1030032151519810535930227)
                ·
                  refine ⟨1545048227279715803895341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030032151519810535930227 1545048227279715803895341)
                  ·
                    refine ⟨579393085229893426460753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545048227279715803895341 579393085229893426460753)
                    ·
                      rfl

theorem cell22_1692546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1692546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692546 prefixEnd_1692546 := by exact prefixLift 1692546
  have htrace : WordTrace (prefixWord ++ tailWord_1692546) baseStart_1692546 baseEnd_1692546 := by
    simpa [prefixWord, tailWord_1692546, baseEnd_1692546] using wordTrace_append hprefix tailTrace_1692546
  have hstable : (prefixWord ++ tailWord_1692546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692546).length < 2 ^ (prefixWord ++ tailWord_1692546).sum := by decide
  have hdescent : baseEnd_1692546 < baseStart_1692546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692572 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1692572 : Nat := 118140960795 + 1692572 * 2 ^ 59
def prefixEnd_1692572 : Nat := 4983230072969 + 3 ^ 40 * 1692572 * 2
def baseEnd_1692572 : Nat := 579401985561238025310673

theorem tailTrace_1692572 : CollatzResearch.WordTrace tailWord_1692572 prefixEnd_1692572 579401985561238025310673 := by
  unfold tailWord_1692572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30866586212054093564403985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41155448282738791419205313 30866586212054093564403985)
  ·
    refine ⟨23149939659040570173302989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30866586212054093564403985 23149939659040570173302989)
    ·
      refine ⟨8681227372140213814988621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23149939659040570173302989 8681227372140213814988621)
      ·
        refine ⟨3255460264552580180620733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8681227372140213814988621 3255460264552580180620733)
        ·
          refine ⟨1220797599207217567732775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3255460264552580180620733 1220797599207217567732775)
          ·
            refine ⟨1831196398810826351599163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220797599207217567732775 1831196398810826351599163)
            ·
              refine ⟨2746794598216239527398745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831196398810826351599163 2746794598216239527398745)
              ·
                refine ⟨2060095948662179645549059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746794598216239527398745 2060095948662179645549059)
                ·
                  refine ⟨3090143922993269468323589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060095948662179645549059 3090143922993269468323589)
                  ·
                    refine ⟨579401985561238025310673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3090143922993269468323589 579401985561238025310673)
                    ·
                      rfl

theorem cell22_1692572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1692572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692572 prefixEnd_1692572 := by exact prefixLift 1692572
  have htrace : WordTrace (prefixWord ++ tailWord_1692572) baseStart_1692572 baseEnd_1692572 := by
    simpa [prefixWord, tailWord_1692572, baseEnd_1692572] using wordTrace_append hprefix tailTrace_1692572
  have hstable : (prefixWord ++ tailWord_1692572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692572).length < 2 ^ (prefixWord ++ tailWord_1692572).sum := by decide
  have hdescent : baseEnd_1692572 < baseStart_1692572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692579 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_1692579 : Nat := 118140960795 + 1692579 * 2 ^ 59
def prefixEnd_1692579 : Nat := 4983230072969 + 3 ^ 40 * 1692579 * 2
def baseEnd_1692579 : Nat := 579404381804292340385651

theorem tailTrace_1692579 : CollatzResearch.WordTrace tailWord_1692579 prefixEnd_1692579 579404381804292340385651 := by
  unfold tailWord_1692579
  simp only [CollatzResearch.WordTrace]
  refine ⟨61733427735082827324312791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41155618490055218216208527 61733427735082827324312791)
  ·
    refine ⟨92600141602624240986469187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61733427735082827324312791 92600141602624240986469187)
    ·
      refine ⟨138900212403936361479703781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92600141602624240986469187 138900212403936361479703781)
      ·
        refine ⟨26043789825738067777444459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138900212403936361479703781 26043789825738067777444459)
        ·
          refine ⟨39065684738607101666166689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26043789825738067777444459 39065684738607101666166689)
          ·
            refine ⟨29299263553955326249625017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39065684738607101666166689 29299263553955326249625017)
            ·
              refine ⟨21974447665466494687218763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29299263553955326249625017 21974447665466494687218763)
              ·
                refine ⟨32961671498199742030828145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21974447665466494687218763 32961671498199742030828145)
                ·
                  refine ⟨24721253623649806523121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32961671498199742030828145 24721253623649806523121109)
                  ·
                    refine ⟨579404381804292340385651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24721253623649806523121109 579404381804292340385651)
                    ·
                      rfl

theorem cell22_1692579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_1692579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692579 prefixEnd_1692579 := by exact prefixLift 1692579
  have htrace : WordTrace (prefixWord ++ tailWord_1692579) baseStart_1692579 baseEnd_1692579 := by
    simpa [prefixWord, tailWord_1692579, baseEnd_1692579] using wordTrace_append hprefix tailTrace_1692579
  have hstable : (prefixWord ++ tailWord_1692579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692579).length < 2 ^ (prefixWord ++ tailWord_1692579).sum := by decide
  have hdescent : baseEnd_1692579 < baseStart_1692579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692630 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1692630 : Nat := 118140960795 + 1692630 * 2 ^ 59
def prefixEnd_1692630 : Nat := 4983230072969 + 3 ^ 40 * 1692630 * 2
def baseEnd_1692630 : Nat := 579421840146545207360495

theorem tailTrace_1692630 : CollatzResearch.WordTrace tailWord_1692630 prefixEnd_1692630 579421840146545207360495 := by
  unfold tailWord_1692630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858455491118628939651209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41156858571932042022946229 3858455491118628939651209)
  ·
    refine ⟨2893841618338971704738407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858455491118628939651209 2893841618338971704738407)
    ·
      refine ⟨4340762427508457557107611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893841618338971704738407 4340762427508457557107611)
      ·
        refine ⟨6511143641262686335661417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340762427508457557107611 6511143641262686335661417)
        ·
          refine ⟨4883357730947014751746063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511143641262686335661417 4883357730947014751746063)
          ·
            refine ⟨7325036596420522127619095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883357730947014751746063 7325036596420522127619095)
            ·
              refine ⟨10987554894630783191428643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325036596420522127619095 10987554894630783191428643)
              ·
                refine ⟨16481332341946174787142965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987554894630783191428643 16481332341946174787142965)
                ·
                  refine ⟨1545124907057453886294653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16481332341946174787142965 1545124907057453886294653)
                  ·
                    refine ⟨579421840146545207360495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545124907057453886294653 579421840146545207360495)
                    ·
                      rfl

theorem cell22_1692630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1692630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692630 prefixEnd_1692630 := by exact prefixLift 1692630
  have htrace : WordTrace (prefixWord ++ tailWord_1692630) baseStart_1692630 baseEnd_1692630 := by
    simpa [prefixWord, tailWord_1692630, baseEnd_1692630] using wordTrace_append hprefix tailTrace_1692630
  have hstable : (prefixWord ++ tailWord_1692630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692630).length < 2 ^ (prefixWord ++ tailWord_1692630).sum := by decide
  have hdescent : baseEnd_1692630 < baseStart_1692630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692647 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1692647 : Nat := 118140960795 + 1692647 * 2 ^ 59
def prefixEnd_1692647 : Nat := 4983230072969 + 3 ^ 40 * 1692647 * 2
def baseEnd_1692647 : Nat := 579427659593962829685443

theorem tailTrace_1692647 : CollatzResearch.WordTrace tailWord_1692647 prefixEnd_1692647 579427659593962829685443 := by
  unfold tailWord_1692647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735907898836474937788195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41157271932557649958525463 61735907898836474937788195)
  ·
    refine ⟨92603861848254712406682293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61735907898836474937788195 92603861848254712406682293)
    ·
      refine ⟨8681612048273879288126465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92603861848254712406682293 8681612048273879288126465)
      ·
        refine ⟨6511209036205409466094849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8681612048273879288126465 6511209036205409466094849)
        ·
          refine ⟨4883406777154057099571137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511209036205409466094849 4883406777154057099571137)
          ·
            refine ⟨3662555082865542824678353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883406777154057099571137 3662555082865542824678353)
            ·
              refine ⟨2746916312149157118508765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662555082865542824678353 2746916312149157118508765)
              ·
                refine ⟨1030093617055933919440787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2746916312149157118508765 1030093617055933919440787)
                ·
                  refine ⟨1545140425583900879161181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030093617055933919440787 1545140425583900879161181)
                  ·
                    refine ⟨579427659593962829685443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545140425583900879161181 579427659593962829685443)
                    ·
                      rfl

theorem cell22_1692647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1692647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692647 prefixEnd_1692647 := by exact prefixLift 1692647
  have htrace : WordTrace (prefixWord ++ tailWord_1692647) baseStart_1692647 baseEnd_1692647 := by
    simpa [prefixWord, tailWord_1692647, baseEnd_1692647] using wordTrace_append hprefix tailTrace_1692647
  have hstable : (prefixWord ++ tailWord_1692647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692647).length < 2 ^ (prefixWord ++ tailWord_1692647).sum := by decide
  have hdescent : baseEnd_1692647 < baseStart_1692647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692703 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 4, 3]
def baseStart_1692703 : Nat := 118140960795 + 1692703 * 2 ^ 59
def prefixEnd_1692703 : Nat := 4983230072969 + 3 ^ 40 * 1692703 * 2
def baseEnd_1692703 : Nat := 579446829538397350285271

theorem tailTrace_1692703 : CollatzResearch.WordTrace tailWord_1692703 prefixEnd_1692703 579446829538397350285271 := by
  unfold tailWord_1692703
  simp only [CollatzResearch.WordTrace]
  refine ⟨61737950386633596501826763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41158633591089064334551175 61737950386633596501826763)
  ·
    refine ⟨92606925579950394752740145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61737950386633596501826763 92606925579950394752740145)
    ·
      refine ⟨69455194184962796064555109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92606925579950394752740145 69455194184962796064555109)
      ·
        refine ⟨13022848909680524262104083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69455194184962796064555109 13022848909680524262104083)
        ·
          refine ⟨19534273364520786393156125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022848909680524262104083 19534273364520786393156125)
          ·
            refine ⟨7325352511695294897433547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19534273364520786393156125 7325352511695294897433547)
            ·
              refine ⟨10988028767542942346150321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325352511695294897433547 10988028767542942346150321)
              ·
                refine ⟨8241021575657206759612741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988028767542942346150321 8241021575657206759612741)
                ·
                  refine ⟨1545191545435726267427389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8241021575657206759612741 1545191545435726267427389)
                  ·
                    refine ⟨579446829538397350285271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545191545435726267427389 579446829538397350285271)
                    ·
                      rfl

theorem cell22_1692703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_1692703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692703 prefixEnd_1692703 := by exact prefixLift 1692703
  have htrace : WordTrace (prefixWord ++ tailWord_1692703) baseStart_1692703 baseEnd_1692703 := by
    simpa [prefixWord, tailWord_1692703, baseEnd_1692703] using wordTrace_append hprefix tailTrace_1692703
  have hstable : (prefixWord ++ tailWord_1692703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692703).length < 2 ^ (prefixWord ++ tailWord_1692703).sum := by decide
  have hdescent : baseEnd_1692703 < baseStart_1692703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692705 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 4]
def baseStart_1692705 : Nat := 118140960795 + 1692705 * 2 ^ 59
def prefixEnd_1692705 : Nat := 4983230072969 + 3 ^ 40 * 1692705 * 2
def baseEnd_1692705 : Nat := 193149171393090003911755

theorem tailTrace_1692705 : CollatzResearch.WordTrace tailWord_1692705 prefixEnd_1692705 193149171393090003911755 := by
  unfold tailWord_1692705
  simp only [CollatzResearch.WordTrace]
  refine ⟨61738023332626350843399569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41158682221750900562266379 61738023332626350843399569)
  ·
    refine ⟨46303517499469763132549677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61738023332626350843399569 46303517499469763132549677)
    ·
      refine ⟨17363819062301161174706129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46303517499469763132549677 17363819062301161174706129)
      ·
        refine ⟨13022864296725870881029597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17363819062301161174706129 13022864296725870881029597)
        ·
          refine ⟨4883574111272201580386099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13022864296725870881029597 4883574111272201580386099)
          ·
            refine ⟨7325361166908302370579149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883574111272201580386099 7325361166908302370579149)
            ·
              refine ⟨2747010437590613388967181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7325361166908302370579149 2747010437590613388967181)
              ·
                refine ⟨1030128914096480020862693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2747010437590613388967181 1030128914096480020862693)
                ·
                  refine ⟨193149171393090003911755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030128914096480020862693 193149171393090003911755)
                  ·
                    rfl

theorem cell22_1692705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_1692705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692705 prefixEnd_1692705 := by exact prefixLift 1692705
  have htrace : WordTrace (prefixWord ++ tailWord_1692705) baseStart_1692705 baseEnd_1692705 := by
    simpa [prefixWord, tailWord_1692705, baseEnd_1692705] using wordTrace_append hprefix tailTrace_1692705
  have hstable : (prefixWord ++ tailWord_1692705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692705).length < 2 ^ (prefixWord ++ tailWord_1692705).sum := by decide
  have hdescent : baseEnd_1692705 < baseStart_1692705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692733 : List Nat := [1, 4, 1, 3, 1, 3, 2, 7]
def baseStart_1692733 : Nat := 118140960795 + 1692733 * 2 ^ 59
def prefixEnd_1692733 : Nat := 4983230072969 + 3 ^ 40 * 1692733 * 2
def baseEnd_1692733 : Nat := 64384122127943030226131

theorem tailTrace_1692733 : CollatzResearch.WordTrace tailWord_1692733 prefixEnd_1692733 64384122127943030226131 := by
  unfold tailWord_1692733
  simp only [CollatzResearch.WordTrace]
  refine ⟨61739044576524911625418853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41159363051016607750279235 61739044576524911625418853)
  ·
    refine ⟨11576070858098420929766035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61739044576524911625418853 11576070858098420929766035)
    ·
      refine ⟨17364106287147631394649053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576070858098420929766035 17364106287147631394649053)
      ·
        refine ⟨6511539857680361772993395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17364106287147631394649053 6511539857680361772993395)
        ·
          refine ⟨9767309786520542659490093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511539857680361772993395 9767309786520542659490093)
          ·
            refine ⟨3662741169945203497308785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9767309786520542659490093 3662741169945203497308785)
            ·
              refine ⟨2747055877458902622981589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662741169945203497308785 2747055877458902622981589)
              ·
                refine ⟨64384122127943030226131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2747055877458902622981589 64384122127943030226131)
                ·
                  rfl

theorem cell22_1692733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 7].length) (baseStart_1692733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692733 prefixEnd_1692733 := by exact prefixLift 1692733
  have htrace : WordTrace (prefixWord ++ tailWord_1692733) baseStart_1692733 baseEnd_1692733 := by
    simpa [prefixWord, tailWord_1692733, baseEnd_1692733] using wordTrace_append hprefix tailTrace_1692733
  have hstable : (prefixWord ++ tailWord_1692733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692733).length < 2 ^ (prefixWord ++ tailWord_1692733).sum := by decide
  have hdescent : baseEnd_1692733 < baseStart_1692733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692737 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1692737 : Nat := 118140960795 + 1692737 * 2 ^ 59
def prefixEnd_1692737 : Nat := 4983230072969 + 3 ^ 40 * 1692737 * 2
def baseEnd_1692737 : Nat := 579458468433232594935167

theorem tailTrace_1692737 : CollatzResearch.WordTrace tailWord_1692737 prefixEnd_1692737 579458468433232594935167 := by
  unfold tailWord_1692737
  simp only [CollatzResearch.WordTrace]
  refine ⟨61739190468510420308564465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41159460312340280205709643 61739190468510420308564465)
  ·
    refine ⟨46304392851382815231423349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61739190468510420308564465 46304392851382815231423349)
    ·
      refine ⟨4341036829817138927945939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46304392851382815231423349 4341036829817138927945939)
      ·
        refine ⟨6511555244725708391918909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4341036829817138927945939 6511555244725708391918909)
        ·
          refine ⟨2441833216772140646969591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6511555244725708391918909 2441833216772140646969591)
          ·
            refine ⟨3662749825158210970454387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441833216772140646969591 3662749825158210970454387)
            ·
              refine ⟨5494124737737316455681581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662749825158210970454387 5494124737737316455681581)
              ·
                refine ⟨2060296776651493670880593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5494124737737316455681581 2060296776651493670880593)
                ·
                  refine ⟨1545222582488620253160445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060296776651493670880593 1545222582488620253160445)
                  ·
                    refine ⟨579458468433232594935167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545222582488620253160445 579458468433232594935167)
                    ·
                      rfl

theorem cell22_1692737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1692737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692737 prefixEnd_1692737 := by exact prefixLift 1692737
  have htrace : WordTrace (prefixWord ++ tailWord_1692737) baseStart_1692737 baseEnd_1692737 := by
    simpa [prefixWord, tailWord_1692737, baseEnd_1692737] using wordTrace_append hprefix tailTrace_1692737
  have hstable : (prefixWord ++ tailWord_1692737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692737).length < 2 ^ (prefixWord ++ tailWord_1692737).sum := by decide
  have hdescent : baseEnd_1692737 < baseStart_1692737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692748 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1692748 : Nat := 118140960795 + 1692748 * 2 ^ 59
def prefixEnd_1692748 : Nat := 4983230072969 + 3 ^ 40 * 1692748 * 2
def baseEnd_1692748 : Nat := 579462233958032232910133

theorem tailTrace_1692748 : CollatzResearch.WordTrace tailWord_1692748 prefixEnd_1692748 579462233958032232910133 := by
  unfold tailWord_1692748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30869795835735284593607449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41159727780980379458143265 30869795835735284593607449)
  ·
    refine ⟨23152346876801463445205587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30869795835735284593607449 23152346876801463445205587)
    ·
      refine ⟨34728520315202195167808381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23152346876801463445205587 34728520315202195167808381)
      ·
        refine ⟨13023195118200823187928143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34728520315202195167808381 13023195118200823187928143)
        ·
          refine ⟨19534792677301234781892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13023195118200823187928143 19534792677301234781892215)
          ·
            refine ⟨29302189015951852172838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19534792677301234781892215 29302189015951852172838323)
            ·
              refine ⟨43953283523927778259257485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29302189015951852172838323 43953283523927778259257485)
              ·
                refine ⟨16482481321472916847221557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43953283523927778259257485 16482481321472916847221557)
                ·
                  refine ⟨1545232623888085954427021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16482481321472916847221557 1545232623888085954427021)
                  ·
                    refine ⟨579462233958032232910133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545232623888085954427021 579462233958032232910133)
                    ·
                      rfl

theorem cell22_1692748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1692748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692748 prefixEnd_1692748 := by exact prefixLift 1692748
  have htrace : WordTrace (prefixWord ++ tailWord_1692748) baseStart_1692748 baseEnd_1692748 := by
    simpa [prefixWord, tailWord_1692748, baseEnd_1692748] using wordTrace_append hprefix tailTrace_1692748
  have hstable : (prefixWord ++ tailWord_1692748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692748).length < 2 ^ (prefixWord ++ tailWord_1692748).sum := by decide
  have hdescent : baseEnd_1692748 < baseStart_1692748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692761 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 7]
def baseStart_1692761 : Nat := 118140960795 + 1692761 * 2 ^ 59
def prefixEnd_1692761 : Nat := 4983230072969 + 3 ^ 40 * 1692761 * 2
def baseEnd_1692761 : Nat := 193155561374568177445031

theorem tailTrace_1692761 : CollatzResearch.WordTrace tailWord_1692761 prefixEnd_1692761 193155561374568177445031 := by
  unfold tailWord_1692761
  simp only [CollatzResearch.WordTrace]
  refine ⟨61740065820423472407438137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41160043880282314938292091 61740065820423472407438137)
  ·
    refine ⟨46305049365317604305578603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61740065820423472407438137 46305049365317604305578603)
    ·
      refine ⟨69457574047976406458367905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46305049365317604305578603 69457574047976406458367905)
      ·
        refine ⟨52093180535982304843775929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69457574047976406458367905 52093180535982304843775929)
        ·
          refine ⟨39069885401986728632831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52093180535982304843775929 39069885401986728632831947)
          ·
            refine ⟨58604828102980092949247921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39069885401986728632831947 58604828102980092949247921)
            ·
              refine ⟨43953621077235069711935941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58604828102980092949247921 43953621077235069711935941)
              ·
                refine ⟨8241303951981575570987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43953621077235069711935941 8241303951981575570987989)
                ·
                  refine ⟨193155561374568177445031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8241303951981575570987989 193155561374568177445031)
                  ·
                    rfl

theorem cell22_1692761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_1692761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692761 prefixEnd_1692761 := by exact prefixLift 1692761
  have htrace : WordTrace (prefixWord ++ tailWord_1692761) baseStart_1692761 baseEnd_1692761 := by
    simpa [prefixWord, tailWord_1692761, baseEnd_1692761] using wordTrace_append hprefix tailTrace_1692761
  have hstable : (prefixWord ++ tailWord_1692761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692761).length < 2 ^ (prefixWord ++ tailWord_1692761).sum := by decide
  have hdescent : baseEnd_1692761 < baseStart_1692761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692885 : List Nat := [1, 3, 2, 4, 1, 3, 8]
def baseStart_1692885 : Nat := 118140960795 + 1692885 * 2 ^ 59
def prefixEnd_1692885 : Nat := 4983230072969 + 3 ^ 40 * 1692885 * 2
def baseEnd_1692885 : Nat := 21463301179918871934619

theorem tailTrace_1692885 : CollatzResearch.WordTrace tailWord_1692885 prefixEnd_1692885 21463301179918871934619 := by
  unfold tailWord_1692885
  simp only [CollatzResearch.WordTrace]
  refine ⟨61744588471974241584952109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41163058981316161056634739 61744588471974241584952109)
  ·
    refine ⟨23154220676990340594357041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61744588471974241584952109 23154220676990340594357041)
    ·
      refine ⟨17365665507742755445767781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23154220676990340594357041 17365665507742755445767781)
      ·
        refine ⟨3256062282701766646081459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17365665507742755445767781 3256062282701766646081459)
        ·
          refine ⟨4884093424052649969122189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256062282701766646081459 4884093424052649969122189)
          ·
            refine ⟨1831535034019743738420821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4884093424052649969122189 1831535034019743738420821)
            ·
              refine ⟨21463301179918871934619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1831535034019743738420821 21463301179918871934619)
              ·
                rfl

theorem cell22_1692885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 8].length) (baseStart_1692885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692885 prefixEnd_1692885 := by exact prefixLift 1692885
  have htrace : WordTrace (prefixWord ++ tailWord_1692885) baseStart_1692885 baseEnd_1692885 := by
    simpa [prefixWord, tailWord_1692885, baseEnd_1692885] using wordTrace_append hprefix tailTrace_1692885
  have hstable : (prefixWord ++ tailWord_1692885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692885).length < 2 ^ (prefixWord ++ tailWord_1692885).sum := by decide
  have hdescent : baseEnd_1692885 < baseStart_1692885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692928 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_1692928 : Nat := 118140960795 + 1692928 * 2 ^ 59
def prefixEnd_1692928 : Nat := 4983230072969 + 3 ^ 40 * 1692928 * 2
def baseEnd_1692928 : Nat := 579523851636571763409581

theorem tailTrace_1692928 : CollatzResearch.WordTrace tailWord_1692928 prefixEnd_1692928 579523851636571763409581 := by
  unfold tailWord_1692928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30873078405409229964383719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41164104540545639952511625 30873078405409229964383719)
  ·
    refine ⟨46309617608113844946575579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30873078405409229964383719 46309617608113844946575579)
    ·
      refine ⟨69464426412170767419863369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46309617608113844946575579 69464426412170767419863369)
      ·
        refine ⟨52098319809128075564897527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69464426412170767419863369 52098319809128075564897527)
        ·
          refine ⟨78147479713692113347346291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52098319809128075564897527 78147479713692113347346291)
          ·
            refine ⟨117221219570538170021019437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78147479713692113347346291 117221219570538170021019437)
            ·
              refine ⟨43957957338951813757882289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117221219570538170021019437 43957957338951813757882289)
              ·
                refine ⟨32968468004213860318411717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43957957338951813757882289 32968468004213860318411717)
                ·
                  refine ⟨6181587750790098809702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32968468004213860318411717 6181587750790098809702197)
                  ·
                    refine ⟨579523851636571763409581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6181587750790098809702197 579523851636571763409581)
                    ·
                      rfl

theorem cell22_1692928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_1692928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692928 prefixEnd_1692928 := by exact prefixLift 1692928
  have htrace : WordTrace (prefixWord ++ tailWord_1692928) baseStart_1692928 baseEnd_1692928 := by
    simpa [prefixWord, tailWord_1692928, baseEnd_1692928] using wordTrace_append hprefix tailTrace_1692928
  have hstable : (prefixWord ++ tailWord_1692928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692928).length < 2 ^ (prefixWord ++ tailWord_1692928).sum := by decide
  have hdescent : baseEnd_1692928 < baseStart_1692928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692962 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1692962 : Nat := 118140960795 + 1692962 * 2 ^ 59
def prefixEnd_1692962 : Nat := 4983230072969 + 3 ^ 40 * 1692962 * 2
def baseEnd_1692962 : Nat := 579535490531407008059477

theorem tailTrace_1692962 : CollatzResearch.WordTrace tailWord_1692962 prefixEnd_1692962 579535490531407008059477 := by
  unfold tailWord_1692962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436849223173820933876285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41164931261796855823670093 15436849223173820933876285)
  ·
    refine ⟨5788818458690182850203607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15436849223173820933876285 5788818458690182850203607)
    ·
      refine ⟨8683227688035274275305411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788818458690182850203607 8683227688035274275305411)
      ·
        refine ⟨13024841532052911412958117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683227688035274275305411 13024841532052911412958117)
        ·
          refine ⟨2442157787259920889929647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13024841532052911412958117 2442157787259920889929647)
          ·
            refine ⟨3663236680889881334894471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442157787259920889929647 3663236680889881334894471)
            ·
              refine ⟨5494855021334822002341707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663236680889881334894471 5494855021334822002341707)
              ·
                refine ⟨8242282532002233003512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5494855021334822002341707 8242282532002233003512561)
                ·
                  refine ⟨6181711899001674752634421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242282532002233003512561 6181711899001674752634421)
                  ·
                    refine ⟨579535490531407008059477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6181711899001674752634421 579535490531407008059477)
                    ·
                      rfl

theorem cell22_1692962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1692962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692962 prefixEnd_1692962 := by exact prefixLift 1692962
  have htrace : WordTrace (prefixWord ++ tailWord_1692962) baseStart_1692962 baseEnd_1692962 := by
    simpa [prefixWord, tailWord_1692962, baseEnd_1692962] using wordTrace_append hprefix tailTrace_1692962
  have hstable : (prefixWord ++ tailWord_1692962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692962).length < 2 ^ (prefixWord ++ tailWord_1692962).sum := by decide
  have hdescent : baseEnd_1692962 < baseStart_1692962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692992 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_1692992 : Nat := 118140960795 + 1692992 * 2 ^ 59
def prefixEnd_1692992 : Nat := 4983230072969 + 3 ^ 40 * 1692992 * 2
def baseEnd_1692992 : Nat := 193181920048165643269795

theorem tailTrace_1692992 : CollatzResearch.WordTrace tailWord_1692992 prefixEnd_1692992 193181920048165643269795 := by
  unfold tailWord_1692992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874245541293299429548615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41165660721724399239398153 30874245541293299429548615)
  ·
    refine ⟨46311368311939949144322923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30874245541293299429548615 46311368311939949144322923)
    ·
      refine ⟨69467052467909923716484385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46311368311939949144322923 69467052467909923716484385)
      ·
        refine ⟨52100289350932442787363289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69467052467909923716484385 52100289350932442787363289)
        ·
          refine ⟨39075217013199332090522467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52100289350932442787363289 39075217013199332090522467)
          ·
            refine ⟨58612825519798998135783701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39075217013199332090522467 58612825519798998135783701)
            ·
              refine ⟨2747476196240578037614861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58612825519798998135783701 2747476196240578037614861)
              ·
                refine ⟨1030303573590216764105573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2747476196240578037614861 1030303573590216764105573)
                ·
                  refine ⟨193181920048165643269795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030303573590216764105573 193181920048165643269795)
                  ·
                    rfl

theorem cell22_1692992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_1692992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692992 prefixEnd_1692992 := by exact prefixLift 1692992
  have htrace : WordTrace (prefixWord ++ tailWord_1692992) baseStart_1692992 baseEnd_1692992 := by
    simpa [prefixWord, tailWord_1692992, baseEnd_1692992] using wordTrace_append hprefix tailTrace_1692992
  have hstable : (prefixWord ++ tailWord_1692992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692992).length < 2 ^ (prefixWord ++ tailWord_1692992).sum := by decide
  have hdescent : baseEnd_1692992 < baseStart_1692992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1692998 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1692998 : Nat := 118140960795 + 1692998 * 2 ^ 59
def prefixEnd_1692998 : Nat := 4983230072969 + 3 ^ 40 * 1692998 * 2
def baseEnd_1692998 : Nat := 193182604689038304719789

theorem tailTrace_1692998 : CollatzResearch.WordTrace tailWord_1692998 prefixEnd_1692998 193182604689038304719789 := by
  unfold tailWord_1692998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929647185017651933869239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41165806613709907922543765 1929647185017651933869239)
  ·
    refine ⟨2894470777526477900803859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929647185017651933869239 2894470777526477900803859)
    ·
      refine ⟨4341706166289716851205789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2894470777526477900803859 4341706166289716851205789)
      ·
        refine ⟨1628139812358643819202171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4341706166289716851205789 1628139812358643819202171)
        ·
          refine ⟨2442209718537965728803257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628139812358643819202171 2442209718537965728803257)
          ·
            refine ⟨1831657288903474296602443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442209718537965728803257 1831657288903474296602443)
            ·
              refine ⟨2747485933355211444903665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831657288903474296602443 2747485933355211444903665)
              ·
                refine ⟨2060614450016408583677749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747485933355211444903665 2060614450016408583677749)
                ·
                  refine ⟨193182604689038304719789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060614450016408583677749 193182604689038304719789)
                  ·
                    rfl

theorem cell22_1692998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1692998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1692998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1692998 prefixEnd_1692998 := by exact prefixLift 1692998
  have htrace : WordTrace (prefixWord ++ tailWord_1692998) baseStart_1692998 baseEnd_1692998 := by
    simpa [prefixWord, tailWord_1692998, baseEnd_1692998] using wordTrace_append hprefix tailTrace_1692998
  have hstable : (prefixWord ++ tailWord_1692998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1692998).length < 2 ^ (prefixWord ++ tailWord_1692998).sum := by decide
  have hdescent : baseEnd_1692998 < baseStart_1692998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1692998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693037 : List Nat := [1, 5, 1, 1, 1, 3, 4, 6]
def baseStart_1693037 : Nat := 118140960795 + 1693037 * 2 ^ 59
def prefixEnd_1693037 : Nat := 4983230072969 + 3 ^ 40 * 1693037 * 2
def baseEnd_1693037 : Nat := 64395684951570201381583

theorem tailTrace_1693037 : CollatzResearch.WordTrace tailWord_1693037 prefixEnd_1693037 64395684951570201381583 := by
  unfold tailWord_1693037
  simp only [CollatzResearch.WordTrace]
  refine ⟨61750132367423571544485365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41166754911615714362990243 61750132367423571544485365)
  ·
    refine ⟨5789074909445959832295503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61750132367423571544485365 5789074909445959832295503)
    ·
      refine ⟨8683612364168939748443255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789074909445959832295503 8683612364168939748443255)
      ·
        refine ⟨13025418546253409622664883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683612364168939748443255 13025418546253409622664883)
        ·
          refine ⟨19538127819380114433997325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13025418546253409622664883 19538127819380114433997325)
          ·
            refine ⟨7326797932267542912748997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19538127819380114433997325 7326797932267542912748997)
            ·
              refine ⟨1373774612300164296140437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7326797932267542912748997 1373774612300164296140437)
              ·
                refine ⟨64395684951570201381583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1373774612300164296140437 64395684951570201381583)
                ·
                  rfl

theorem cell22_1693037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 6].length) (baseStart_1693037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693037 prefixEnd_1693037 := by exact prefixLift 1693037
  have htrace : WordTrace (prefixWord ++ tailWord_1693037) baseStart_1693037 baseEnd_1693037 := by
    simpa [prefixWord, tailWord_1693037, baseEnd_1693037] using wordTrace_append hprefix tailTrace_1693037
  have hstable : (prefixWord ++ tailWord_1693037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693037).length < 2 ^ (prefixWord ++ tailWord_1693037).sum := by decide
  have hdescent : baseEnd_1693037 < baseStart_1693037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693082 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1693082 : Nat := 118140960795 + 1693082 * 2 ^ 59
def prefixEnd_1693082 : Nat := 4983230072969 + 3 ^ 40 * 1693082 * 2
def baseEnd_1693082 : Nat := 193192189661255565019703

theorem tailTrace_1693082 : CollatzResearch.WordTrace tailWord_1693082 prefixEnd_1693082 193192189661255565019703 := by
  unfold tailWord_1693082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437943413065136057468375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41167849101507029486582333 15437943413065136057468375)
  ·
    refine ⟨23156915119597704086202563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437943413065136057468375 23156915119597704086202563)
    ·
      refine ⟨34735372679396556129303845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23156915119597704086202563 34735372679396556129303845)
      ·
        refine ⟨6512882377386854274244471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34735372679396556129303845 6512882377386854274244471)
        ·
          refine ⟨9769323566080281411366707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512882377386854274244471 9769323566080281411366707)
          ·
            refine ⟨14653985349120422117050061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9769323566080281411366707 14653985349120422117050061)
            ·
              refine ⟨5495244505920158293893773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14653985349120422117050061 5495244505920158293893773)
              ·
                refine ⟨2060716689720059360210165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5495244505920158293893773 2060716689720059360210165)
                ·
                  refine ⟨193192189661255565019703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2060716689720059360210165 193192189661255565019703)
                  ·
                    rfl

theorem cell22_1693082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1693082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693082 prefixEnd_1693082 := by exact prefixLift 1693082
  have htrace : WordTrace (prefixWord ++ tailWord_1693082) baseStart_1693082 baseEnd_1693082 := by
    simpa [prefixWord, tailWord_1693082, baseEnd_1693082] using wordTrace_append hprefix tailTrace_1693082
  have hstable : (prefixWord ++ tailWord_1693082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693082).length < 2 ^ (prefixWord ++ tailWord_1693082).sum := by decide
  have hdescent : baseEnd_1693082 < baseStart_1693082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693112 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_1693112 : Nat := 118140960795 + 1693112 * 2 ^ 59
def prefixEnd_1693112 : Nat := 4983230072969 + 3 ^ 40 * 1693112 * 2
def baseEnd_1693112 : Nat := 579586838596856616809017

theorem tailTrace_1693112 : CollatzResearch.WordTrace tailWord_1693112 prefixEnd_1693112 579586838596856616809017 := by
  unfold tailWord_1693112
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876433921075929676732795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41168578561434572902310393 30876433921075929676732795)
  ·
    refine ⟨46314650881613894515099193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30876433921075929676732795 46314650881613894515099193)
    ·
      refine ⟨34735988161210420886324395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46314650881613894515099193 34735988161210420886324395)
      ·
        refine ⟨52103982241815631329486593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34735988161210420886324395 52103982241815631329486593)
        ·
          refine ⟨39077986681361723497114945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52103982241815631329486593 39077986681361723497114945)
          ·
            refine ⟨29308490011021292622836209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39077986681361723497114945 29308490011021292622836209)
            ·
              refine ⟨21981367508265969467127157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29308490011021292622836209 21981367508265969467127157)
              ·
                refine ⟨2060753203899934637543171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21981367508265969467127157 2060753203899934637543171)
                ·
                  refine ⟨3091129805849901956314757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060753203899934637543171 3091129805849901956314757)
                  ·
                    refine ⟨579586838596856616809017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091129805849901956314757 579586838596856616809017)
                    ·
                      rfl

theorem cell22_1693112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_1693112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693112 prefixEnd_1693112 := by exact prefixLift 1693112
  have htrace : WordTrace (prefixWord ++ tailWord_1693112) baseStart_1693112 baseEnd_1693112 := by
    simpa [prefixWord, tailWord_1693112, baseEnd_1693112] using wordTrace_append hprefix tailTrace_1693112
  have hstable : (prefixWord ++ tailWord_1693112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693112).length < 2 ^ (prefixWord ++ tailWord_1693112).sum := by decide
  have hdescent : baseEnd_1693112 < baseStart_1693112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693176 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_1693176 : Nat := 118140960795 + 1693176 * 2 ^ 59
def prefixEnd_1693176 : Nat := 4983230072969 + 3 ^ 40 * 1693176 * 2
def baseEnd_1693176 : Nat := 579608747104781783208821

theorem tailTrace_1693176 : CollatzResearch.WordTrace tailWord_1693176 prefixEnd_1693176 579608747104781783208821 := by
  unfold tailWord_1693176
  simp only [CollatzResearch.WordTrace]
  refine ⟨30877601056959999141897691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41170134742613332189196921 30877601056959999141897691)
  ·
    refine ⟨46316401585439998712846537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30877601056959999141897691 46316401585439998712846537)
    ·
      refine ⟨34737301189079999034634903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46316401585439998712846537 34737301189079999034634903)
      ·
        refine ⟨52105951783619998551952355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34737301189079999034634903 52105951783619998551952355)
        ·
          refine ⟨78158927675429997827928533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52105951783619998551952355 78158927675429997827928533)
          ·
            refine ⟨1831849867392890574092075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78158927675429997827928533 1831849867392890574092075)
            ·
              refine ⟨2747774801089335861138113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831849867392890574092075 2747774801089335861138113)
              ·
                refine ⟨2060831100817001895853585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747774801089335861138113 2060831100817001895853585)
                ·
                  refine ⟨1545623325612751421890189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2060831100817001895853585 1545623325612751421890189)
                  ·
                    refine ⟨579608747104781783208821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545623325612751421890189 579608747104781783208821)
                    ·
                      rfl

theorem cell22_1693176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_1693176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693176 prefixEnd_1693176 := by exact prefixLift 1693176
  have htrace : WordTrace (prefixWord ++ tailWord_1693176) baseStart_1693176 baseEnd_1693176 := by
    simpa [prefixWord, tailWord_1693176, baseEnd_1693176] using wordTrace_append hprefix tailTrace_1693176
  have hstable : (prefixWord ++ tailWord_1693176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693176).length < 2 ^ (prefixWord ++ tailWord_1693176).sum := by decide
  have hdescent : baseEnd_1693176 < baseStart_1693176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693217 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 7]
def baseStart_1693217 : Nat := 118140960795 + 1693217 * 2 ^ 59
def prefixEnd_1693217 : Nat := 4983230072969 + 3 ^ 40 * 1693217 * 2
def baseEnd_1693217 : Nat := 193207594080890447644565

theorem tailTrace_1693217 : CollatzResearch.WordTrace tailWord_1693217 prefixEnd_1693217 193207594080890447644565 := by
  unfold tailWord_1693217
  simp only [CollatzResearch.WordTrace]
  refine ⟨61756697506771462286037905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41171131671180974857358603 61756697506771462286037905)
  ·
    refine ⟨46317523130078596714528429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61756697506771462286037905 46317523130078596714528429)
    ·
      refine ⟨17369071173779473767948161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46317523130078596714528429 17369071173779473767948161)
      ·
        refine ⟨13026803380334605325961121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17369071173779473767948161 13026803380334605325961121)
        ·
          refine ⟨9770102535250953994470841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13026803380334605325961121 9770102535250953994470841)
          ·
            refine ⟨7327576901438215495853131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770102535250953994470841 7327576901438215495853131)
            ·
              refine ⟨10991365352157323243779697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7327576901438215495853131 10991365352157323243779697)
              ·
                refine ⟨8243524014117992432834773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991365352157323243779697 8243524014117992432834773)
                ·
                  refine ⟨193207594080890447644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8243524014117992432834773 193207594080890447644565)
                  ·
                    rfl

theorem cell22_1693217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_1693217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693217 prefixEnd_1693217 := by exact prefixLift 1693217
  have htrace : WordTrace (prefixWord ++ tailWord_1693217) baseStart_1693217 baseEnd_1693217 := by
    simpa [prefixWord, tailWord_1693217, baseEnd_1693217] using wordTrace_append hprefix tailTrace_1693217
  have hstable : (prefixWord ++ tailWord_1693217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693217).length < 2 ^ (prefixWord ++ tailWord_1693217).sum := by decide
  have hdescent : baseEnd_1693217 < baseStart_1693217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693262 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1693262 : Nat := 118140960795 + 1693262 * 2 ^ 59
def prefixEnd_1693262 : Nat := 4983230072969 + 3 ^ 40 * 1693262 * 2
def baseEnd_1693262 : Nat := 193212728887435408519519

theorem tailTrace_1693262 : CollatzResearch.WordTrace tailWord_1693262 prefixEnd_1693262 193212728887435408519519 := by
  unfold tailWord_1693262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719792348951054371428255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41172225861072289980950693 7719792348951054371428255)
  ·
    refine ⟨11579688523426581557142383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7719792348951054371428255 11579688523426581557142383)
    ·
      refine ⟨17369532785139872335713575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579688523426581557142383 17369532785139872335713575)
      ·
        refine ⟨26054299177709808503570363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369532785139872335713575 26054299177709808503570363)
        ·
          refine ⟨39081448766564712755355545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054299177709808503570363 39081448766564712755355545)
          ·
            refine ⟨29311086574923534566516659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39081448766564712755355545 29311086574923534566516659)
            ·
              refine ⟨43966629862385301849774989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29311086574923534566516659 43966629862385301849774989)
              ·
                refine ⟨16487486198394488193665621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43966629862385301849774989 16487486198394488193665621)
                ·
                  refine ⟨193212728887435408519519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16487486198394488193665621 193212728887435408519519)
                  ·
                    rfl

theorem cell22_1693262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1693262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693262 prefixEnd_1693262 := by exact prefixLift 1693262
  have htrace : WordTrace (prefixWord ++ tailWord_1693262) baseStart_1693262 baseEnd_1693262 := by
    simpa [prefixWord, tailWord_1693262, baseEnd_1693262] using wordTrace_append hprefix tailTrace_1693262
  have hstable : (prefixWord ++ tailWord_1693262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693262).length < 2 ^ (prefixWord ++ tailWord_1693262).sum := by decide
  have hdescent : baseEnd_1693262 < baseStart_1693262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693281 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1693281 : Nat := 118140960795 + 1693281 * 2 ^ 59
def prefixEnd_1693281 : Nat := 4983230072969 + 3 ^ 40 * 1693281 * 2
def baseEnd_1693281 : Nat := 579644690750596509333499

theorem tailTrace_1693281 : CollatzResearch.WordTrace tailWord_1693281 prefixEnd_1693281 579644690750596509333499 := by
  unfold tailWord_1693281
  simp only [CollatzResearch.WordTrace]
  refine ⟨61759031778539601216367697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41172687852359734144245131 61759031778539601216367697)
  ·
    refine ⟨46319273833904700912275773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61759031778539601216367697 46319273833904700912275773)
    ·
      refine ⟨17369727687714262842103415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46319273833904700912275773 17369727687714262842103415)
      ·
        refine ⟨26054591531571394263155123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369727687714262842103415 26054591531571394263155123)
        ·
          refine ⟨39081887297357091394732685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26054591531571394263155123 39081887297357091394732685)
          ·
            refine ⟨14655707736508909273024757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39081887297357091394732685 14655707736508909273024757)
            ·
              refine ⟨1373972600297710244346071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14655707736508909273024757 1373972600297710244346071)
              ·
                refine ⟨2060958900446565366519107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373972600297710244346071 2060958900446565366519107)
                ·
                  refine ⟨3091438350669848049778661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060958900446565366519107 3091438350669848049778661)
                  ·
                    refine ⟨579644690750596509333499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091438350669848049778661 579644690750596509333499)
                    ·
                      rfl

theorem cell22_1693281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1693281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693281 prefixEnd_1693281 := by exact prefixLift 1693281
  have htrace : WordTrace (prefixWord ++ tailWord_1693281) baseStart_1693281 baseEnd_1693281 := by
    simpa [prefixWord, tailWord_1693281, baseEnd_1693281] using wordTrace_append hprefix tailTrace_1693281
  have hstable : (prefixWord ++ tailWord_1693281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693281).length < 2 ^ (prefixWord ++ tailWord_1693281).sum := by decide
  have hdescent : baseEnd_1693281 < baseStart_1693281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693292 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1693292 : Nat := 118140960795 + 1693292 * 2 ^ 59
def prefixEnd_1693292 : Nat := 4983230072969 + 3 ^ 40 * 1693292 * 2
def baseEnd_1693292 : Nat := 579648456275396147308465

theorem tailTrace_1693292 : CollatzResearch.WordTrace tailWord_1693292 prefixEnd_1693292 579648456275396147308465 := by
  unfold tailWord_1693292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879716490749875047509065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41172955320999833396678753 30879716490749875047509065)
  ·
    refine ⟨23159787368062406285631799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30879716490749875047509065 23159787368062406285631799)
    ·
      refine ⟨34739681052093609428447699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23159787368062406285631799 34739681052093609428447699)
      ·
        refine ⟨52109521578140414142671549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34739681052093609428447699 52109521578140414142671549)
        ·
          refine ⟨19541070591802655303501831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52109521578140414142671549 19541070591802655303501831)
          ·
            refine ⟨29311605887703982955252747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19541070591802655303501831 29311605887703982955252747)
            ·
              refine ⟨43967408831555974432879121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29311605887703982955252747 43967408831555974432879121)
              ·
                refine ⟨32975556623666980824659341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43967408831555974432879121 32975556623666980824659341)
                ·
                  refine ⟨12365833733875117809247253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32975556623666980824659341 12365833733875117809247253)
                  ·
                    refine ⟨579648456275396147308465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12365833733875117809247253 579648456275396147308465)
                    ·
                      rfl

theorem cell22_1693292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1693292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693292 prefixEnd_1693292 := by exact prefixLift 1693292
  have htrace : WordTrace (prefixWord ++ tailWord_1693292) baseStart_1693292 baseEnd_1693292 := by
    simpa [prefixWord, tailWord_1693292, baseEnd_1693292] using wordTrace_append hprefix tailTrace_1693292
  have hstable : (prefixWord ++ tailWord_1693292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693292).length < 2 ^ (prefixWord ++ tailWord_1693292).sum := by decide
  have hdescent : baseEnd_1693292 < baseStart_1693292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693296 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_1693296 : Nat := 118140960795 + 1693296 * 2 ^ 59
def prefixEnd_1693296 : Nat := 4983230072969 + 3 ^ 40 * 1693296 * 2
def baseEnd_1693296 : Nat := 193216608519047156736151

theorem tailTrace_1693296 : CollatzResearch.WordTrace tailWord_1693296 prefixEnd_1693296 193216608519047156736151 := by
  unfold tailWord_1693296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879789436742629389081871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41173052582323505852109161 30879789436742629389081871)
  ·
    refine ⟨46319684155113944083622807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30879789436742629389081871 46319684155113944083622807)
    ·
      refine ⟨69479526232670916125434211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46319684155113944083622807 69479526232670916125434211)
      ·
        refine ⟨104219289349006374188151317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69479526232670916125434211 104219289349006374188151317)
        ·
          refine ⟨4885279188234673790069593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104219289349006374188151317 4885279188234673790069593)
          ·
            refine ⟨3663959391176005342552195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4885279188234673790069593 3663959391176005342552195)
            ·
              refine ⟨5495939086764008013828293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663959391176005342552195 5495939086764008013828293)
              ·
                refine ⟨1030488578768251502592805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5495939086764008013828293 1030488578768251502592805)
                ·
                  refine ⟨193216608519047156736151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030488578768251502592805 193216608519047156736151)
                  ·
                    rfl

theorem cell22_1693296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_1693296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693296 prefixEnd_1693296 := by exact prefixLift 1693296
  have htrace : WordTrace (prefixWord ++ tailWord_1693296) baseStart_1693296 baseEnd_1693296 := by
    simpa [prefixWord, tailWord_1693296, baseEnd_1693296] using wordTrace_append hprefix tailTrace_1693296
  have hstable : (prefixWord ++ tailWord_1693296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693296).length < 2 ^ (prefixWord ++ tailWord_1693296).sum := by decide
  have hdescent : baseEnd_1693296 < baseStart_1693296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693324 : List Nat := [2, 2, 1, 2, 1, 1, 7, 6]
def baseStart_1693324 : Nat := 118140960795 + 1693324 * 2 ^ 59
def prefixEnd_1693324 : Nat := 4983230072969 + 3 ^ 40 * 1693324 * 2
def baseEnd_1693324 : Nat := 64406601169928747834263

theorem tailTrace_1693324 : CollatzResearch.WordTrace tailWord_1693324 prefixEnd_1693324 64406601169928747834263 := by
  unfold tailWord_1693324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880300058691909780091513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41173733411589213040122017 30880300058691909780091513)
  ·
    refine ⟨23160225044018932335068635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30880300058691909780091513 23160225044018932335068635)
    ·
      refine ⟨34740337566028398502602953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160225044018932335068635 34740337566028398502602953)
      ·
        refine ⟨26055253174521298876952215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34740337566028398502602953 26055253174521298876952215)
        ·
          refine ⟨39082879761781948315428323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26055253174521298876952215 39082879761781948315428323)
          ·
            refine ⟨58624319642672922473142485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39082879761781948315428323 58624319642672922473142485)
            ·
              refine ⟨1374007491625146620464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58624319642672922473142485 1374007491625146620464277)
              ·
                refine ⟨64406601169928747834263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374007491625146620464277 64406601169928747834263)
                ·
                  rfl

theorem cell22_1693324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_1693324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693324 prefixEnd_1693324 := by exact prefixLift 1693324
  have htrace : WordTrace (prefixWord ++ tailWord_1693324) baseStart_1693324 baseEnd_1693324 := by
    simpa [prefixWord, tailWord_1693324, baseEnd_1693324] using wordTrace_append hprefix tailTrace_1693324
  have hstable : (prefixWord ++ tailWord_1693324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693324).length < 2 ^ (prefixWord ++ tailWord_1693324).sum := by decide
  have hdescent : baseEnd_1693324 < baseStart_1693324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693326 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1693326 : Nat := 118140960795 + 1693326 * 2 ^ 59
def prefixEnd_1693326 : Nat := 4983230072969 + 3 ^ 40 * 1693326 * 2
def baseEnd_1693326 : Nat := 579660095170231391958361

theorem tailTrace_1693326 : CollatzResearch.WordTrace tailWord_1693326 prefixEnd_1693326 579660095170231391958361 := by
  unfold tailWord_1693326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720084132922071737719479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41173782042251049267837221 7720084132922071737719479)
  ·
    refine ⟨11580126199383107606579219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7720084132922071737719479 11580126199383107606579219)
    ·
      refine ⟨17370189299074661409868829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11580126199383107606579219 17370189299074661409868829)
      ·
        refine ⟨6513820987152998028700811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17370189299074661409868829 6513820987152998028700811)
        ·
          refine ⟨9770731480729497043051217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513820987152998028700811 9770731480729497043051217)
          ·
            refine ⟨7328048610547122782288413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9770731480729497043051217 7328048610547122782288413)
            ·
              refine ⟨2748018228955171043358155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328048610547122782288413 2748018228955171043358155)
              ·
                refine ⟨4122027343432756565037233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748018228955171043358155 4122027343432756565037233)
                ·
                  refine ⟨3091520507574567423777925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122027343432756565037233 3091520507574567423777925)
                  ·
                    refine ⟨579660095170231391958361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091520507574567423777925 579660095170231391958361)
                    ·
                      rfl

theorem cell22_1693326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1693326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693326 prefixEnd_1693326 := by exact prefixLift 1693326
  have htrace : WordTrace (prefixWord ++ tailWord_1693326) baseStart_1693326 baseEnd_1693326 := by
    simpa [prefixWord, tailWord_1693326, baseEnd_1693326] using wordTrace_append hprefix tailTrace_1693326
  have hstable : (prefixWord ++ tailWord_1693326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693326).length < 2 ^ (prefixWord ++ tailWord_1693326).sum := by decide
  have hdescent : baseEnd_1693326 < baseStart_1693326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693332 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1693332 : Nat := 118140960795 + 1693332 * 2 ^ 59
def prefixEnd_1693332 : Nat := 4983230072969 + 3 ^ 40 * 1693332 * 2
def baseEnd_1693332 : Nat := 579662149092849376308343

theorem tailTrace_1693332 : CollatzResearch.WordTrace tailWord_1693332 prefixEnd_1693332 579662149092849376308343 := by
  unfold tailWord_1693332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880445950677418463237125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41173927934236557950982833 30880445950677418463237125)
  ·
    refine ⟨5790083615752015961856961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30880445950677418463237125 5790083615752015961856961)
    ·
      refine ⟨4342562711814011971392721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5790083615752015961856961 4342562711814011971392721)
      ·
        refine ⟨3256922033860508978544541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4342562711814011971392721 3256922033860508978544541)
        ·
          refine ⟨1221345762697690866954203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3256922033860508978544541 1221345762697690866954203)
          ·
            refine ⟨1832018644046536300431305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221345762697690866954203 1832018644046536300431305)
            ·
              refine ⟨1374013983034902225323479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832018644046536300431305 1374013983034902225323479)
              ·
                refine ⟨2061020974552353337985219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374013983034902225323479 2061020974552353337985219)
                ·
                  refine ⟨3091531461828530006977829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061020974552353337985219 3091531461828530006977829)
                  ·
                    refine ⟨579662149092849376308343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091531461828530006977829 579662149092849376308343)
                    ·
                      rfl

theorem cell22_1693332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1693332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693332 prefixEnd_1693332 := by exact prefixLift 1693332
  have htrace : WordTrace (prefixWord ++ tailWord_1693332) baseStart_1693332 baseEnd_1693332 := by
    simpa [prefixWord, tailWord_1693332, baseEnd_1693332] using wordTrace_append hprefix tailTrace_1693332
  have hstable : (prefixWord ++ tailWord_1693332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693332).length < 2 ^ (prefixWord ++ tailWord_1693332).sum := by decide
  have hdescent : baseEnd_1693332 < baseStart_1693332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693337 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1693337 : Nat := 118140960795 + 1693337 * 2 ^ 59
def prefixEnd_1693337 : Nat := 4983230072969 + 3 ^ 40 * 1693337 * 2
def baseEnd_1693337 : Nat := 579663860695031029933327

theorem tailTrace_1693337 : CollatzResearch.WordTrace tailWord_1693337 prefixEnd_1693337 579663860695031029933327 := by
  unfold tailWord_1693337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61761074266336722780406265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41174049510891148520270843 61761074266336722780406265)
  ·
    refine ⟨46320805699752542085304699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61761074266336722780406265 46320805699752542085304699)
    ·
      refine ⟨69481208549628813127957049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46320805699752542085304699 69481208549628813127957049)
      ·
        refine ⟨52110906412221609845967787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69481208549628813127957049 52110906412221609845967787)
        ·
          refine ⟨78166359618332414768951681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52110906412221609845967787 78166359618332414768951681)
          ·
            refine ⟨58624769713749311076713761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78166359618332414768951681 58624769713749311076713761)
            ·
              refine ⟨43968577285311983307535321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58624769713749311076713761 43968577285311983307535321)
              ·
                refine ⟨32976432963983987480651491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43968577285311983307535321 32976432963983987480651491)
                ·
                  refine ⟨49464649445975981220977237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32976432963983987480651491 49464649445975981220977237)
                  ·
                    refine ⟨579663860695031029933327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49464649445975981220977237 579663860695031029933327)
                    ·
                      rfl

theorem cell22_1693337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1693337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693337 prefixEnd_1693337 := by exact prefixLift 1693337
  have htrace : WordTrace (prefixWord ++ tailWord_1693337) baseStart_1693337 baseEnd_1693337 := by
    simpa [prefixWord, tailWord_1693337, baseEnd_1693337] using wordTrace_append hprefix tailTrace_1693337
  have hstable : (prefixWord ++ tailWord_1693337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693337).length < 2 ^ (prefixWord ++ tailWord_1693337).sum := by decide
  have hdescent : baseEnd_1693337 < baseStart_1693337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693369 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 5]
def baseStart_1693369 : Nat := 118140960795 + 1693369 * 2 ^ 59
def prefixEnd_1693369 : Nat := 4983230072969 + 3 ^ 40 * 1693369 * 2
def baseEnd_1693369 : Nat := 193224938316331204377743

theorem tailTrace_1693369 : CollatzResearch.WordTrace tailWord_1693369 prefixEnd_1693369 193224938316331204377743 := by
  unfold tailWord_1693369
  simp only [CollatzResearch.WordTrace]
  refine ⟨61762241402220792245571161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41174827601480528163714107 61762241402220792245571161)
  ·
    refine ⟨46321681051665594184178371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61762241402220792245571161 46321681051665594184178371)
    ·
      refine ⟨69482521577498391276267557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46321681051665594184178371 69482521577498391276267557)
      ·
        refine ⟨13027972795780948364300167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69482521577498391276267557 13027972795780948364300167)
        ·
          refine ⟨19541959193671422546450251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13027972795780948364300167 19541959193671422546450251)
          ·
            refine ⟨29312938790507133819675377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19541959193671422546450251 29312938790507133819675377)
            ·
              refine ⟨21984704092880350364756533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29312938790507133819675377 21984704092880350364756533)
              ·
                refine ⟨2061066008707532846695925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21984704092880350364756533 2061066008707532846695925)
                ·
                  refine ⟨193224938316331204377743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2061066008707532846695925 193224938316331204377743)
                  ·
                    rfl

theorem cell22_1693369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_1693369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693369 prefixEnd_1693369 := by exact prefixLift 1693369
  have htrace : WordTrace (prefixWord ++ tailWord_1693369) baseStart_1693369 baseEnd_1693369 := by
    simpa [prefixWord, tailWord_1693369, baseEnd_1693369] using wordTrace_append hprefix tailTrace_1693369
  have hstable : (prefixWord ++ tailWord_1693369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693369).length < 2 ^ (prefixWord ++ tailWord_1693369).sum := by decide
  have hdescent : baseEnd_1693369 < baseStart_1693369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693461 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1693461 : Nat := 118140960795 + 1693461 * 2 ^ 59
def prefixEnd_1693461 : Nat := 4983230072969 + 3 ^ 40 * 1693461 * 2
def baseEnd_1693461 : Nat := 579706308429136039832947

theorem tailTrace_1693461 : CollatzResearch.WordTrace tailWord_1693461 prefixEnd_1693461 579706308429136039832947 := by
  unfold tailWord_1693461
  simp only [CollatzResearch.WordTrace]
  refine ⟨61765596917887491957920237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41177064611924994638613491 61765596917887491957920237)
  ·
    refine ⟨23162098844207809484220089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61765596917887491957920237 23162098844207809484220089)
    ·
      refine ⟨17371574133155857113165067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23162098844207809484220089 17371574133155857113165067)
      ·
        refine ⟨26057361199733785669747601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17371574133155857113165067 26057361199733785669747601)
        ·
          refine ⟨19543020899800339252310701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26057361199733785669747601 19543020899800339252310701)
          ·
            refine ⟨7328632837425127219616513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19543020899800339252310701 7328632837425127219616513)
            ·
              refine ⟨5496474628068845414712385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328632837425127219616513 5496474628068845414712385)
              ·
                refine ⟨4122355971051634061034289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496474628068845414712385 4122355971051634061034289)
                ·
                  refine ⟨3091766978288725545775717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122355971051634061034289 3091766978288725545775717)
                  ·
                    refine ⟨579706308429136039832947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3091766978288725545775717 579706308429136039832947)
                    ·
                      rfl

theorem cell22_1693461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1693461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693461 prefixEnd_1693461 := by exact prefixLift 1693461
  have htrace : WordTrace (prefixWord ++ tailWord_1693461) baseStart_1693461 baseEnd_1693461 := by
    simpa [prefixWord, tailWord_1693461, baseEnd_1693461] using wordTrace_append hprefix tailTrace_1693461
  have hstable : (prefixWord ++ tailWord_1693461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693461).length < 2 ^ (prefixWord ++ tailWord_1693461).sum := by decide
  have hdescent : baseEnd_1693461 < baseStart_1693461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693463 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1693463 : Nat := 118140960795 + 1693463 * 2 ^ 59
def prefixEnd_1693463 : Nat := 4983230072969 + 3 ^ 40 * 1693463 * 2
def baseEnd_1693463 : Nat := 579706993070008701282941

theorem tailTrace_1693463 : CollatzResearch.WordTrace tailWord_1693463 prefixEnd_1693463 579706993070008701282941 := by
  unfold tailWord_1693463
  simp only [CollatzResearch.WordTrace]
  refine ⟨61765669863880246299493043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41177113242586830866328695 61765669863880246299493043)
  ·
    refine ⟨92648504795820369449239565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61765669863880246299493043 92648504795820369449239565)
    ·
      refine ⟨34743189298432638543464837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92648504795820369449239565 34743189298432638543464837)
      ·
        refine ⟨6514347993456119726899657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34743189298432638543464837 6514347993456119726899657)
        ·
          refine ⟨4885760995092089795174743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514347993456119726899657 4885760995092089795174743)
          ·
            refine ⟨7328641492638134692762115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885760995092089795174743 7328641492638134692762115)
            ·
              refine ⟨10992962238957202039143173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328641492638134692762115 10992962238957202039143173)
              ·
                refine ⟨2061180419804475382339345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10992962238957202039143173 2061180419804475382339345)
                ·
                  refine ⟨1545885314853356536754509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2061180419804475382339345 1545885314853356536754509)
                  ·
                    refine ⟨579706993070008701282941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545885314853356536754509 579706993070008701282941)
                    ·
                      rfl

theorem cell22_1693463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1693463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693463 prefixEnd_1693463 := by exact prefixLift 1693463
  have htrace : WordTrace (prefixWord ++ tailWord_1693463) baseStart_1693463 baseEnd_1693463 := by
    simpa [prefixWord, tailWord_1693463, baseEnd_1693463] using wordTrace_append hprefix tailTrace_1693463
  have hstable : (prefixWord ++ tailWord_1693463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693463).length < 2 ^ (prefixWord ++ tailWord_1693463).sum := by decide
  have hdescent : baseEnd_1693463 < baseStart_1693463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693476 : List Nat := [2, 3, 1, 3, 2, 1, 3, 7]
def baseStart_1693476 : Nat := 118140960795 + 1693476 * 2 ^ 59
def prefixEnd_1693476 : Nat := 4983230072969 + 3 ^ 40 * 1693476 * 2
def baseEnd_1693476 : Nat := 64412382581742333411989

theorem tailTrace_1693476 : CollatzResearch.WordTrace tailWord_1693476 prefixEnd_1693476 64412382581742333411989 := by
  unfold tailWord_1693476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30883072006416574759858141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41177429341888766346477521 30883072006416574759858141)
  ·
    refine ⟨11581152002406215534946803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30883072006416574759858141 11581152002406215534946803)
    ·
      refine ⟨17371728003609323302420205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11581152002406215534946803 17371728003609323302420205)
      ·
        refine ⟨6514398001353496238407577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17371728003609323302420205 6514398001353496238407577)
        ·
          refine ⟨4885798501015122178805683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514398001353496238407577 4885798501015122178805683)
          ·
            refine ⟨7328697751522683268208525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885798501015122178805683 7328697751522683268208525)
            ·
              refine ⟨2748261656821006225578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7328697751522683268208525 2748261656821006225578197)
              ·
                refine ⟨64412382581742333411989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2748261656821006225578197 64412382581742333411989)
                ·
                  rfl

theorem cell22_1693476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_1693476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693476 prefixEnd_1693476 := by exact prefixLift 1693476
  have htrace : WordTrace (prefixWord ++ tailWord_1693476) baseStart_1693476 baseEnd_1693476 := by
    simpa [prefixWord, tailWord_1693476, baseEnd_1693476] using wordTrace_append hprefix tailTrace_1693476
  have hstable : (prefixWord ++ tailWord_1693476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693476).length < 2 ^ (prefixWord ++ tailWord_1693476).sum := by decide
  have hdescent : baseEnd_1693476 < baseStart_1693476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693493 : List Nat := [1, 3, 3, 1, 4, 1, 3, 6]
def baseStart_1693493 : Nat := 118140960795 + 1693493 * 2 ^ 59
def prefixEnd_1693493 : Nat := 4983230072969 + 3 ^ 40 * 1693493 * 2
def baseEnd_1693493 : Nat := 64413029187010958114761

theorem tailTrace_1693493 : CollatzResearch.WordTrace tailWord_1693493 prefixEnd_1693493 64413029187010958114761 := by
  unfold tailWord_1693493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61766764053771561423085133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41177842702514374282056755 61766764053771561423085133)
  ·
    refine ⟨23162536520164335533656925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61766764053771561423085133 23162536520164335533656925)
    ·
      refine ⟨8685951195061625825121347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23162536520164335533656925 8685951195061625825121347)
      ·
        refine ⟨13028926792592438737682021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8685951195061625825121347 13028926792592438737682021)
        ·
          refine ⟨2442923773611082263315379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13028926792592438737682021 2442923773611082263315379)
          ·
            refine ⟨3664385660416623394973069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442923773611082263315379 3664385660416623394973069)
            ·
              refine ⟨1374144622656233773114901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664385660416623394973069 1374144622656233773114901)
              ·
                refine ⟨64413029187010958114761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374144622656233773114901 64413029187010958114761)
                ·
                  rfl

theorem cell22_1693493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 6].length) (baseStart_1693493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693493 prefixEnd_1693493 := by exact prefixLift 1693493
  have htrace : WordTrace (prefixWord ++ tailWord_1693493) baseStart_1693493 baseEnd_1693493 := by
    simpa [prefixWord, tailWord_1693493, baseEnd_1693493] using wordTrace_append hprefix tailTrace_1693493
  have hstable : (prefixWord ++ tailWord_1693493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693493).length < 2 ^ (prefixWord ++ tailWord_1693493).sum := by decide
  have hdescent : baseEnd_1693493 < baseStart_1693493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693521 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 7]
def baseStart_1693521 : Nat := 118140960795 + 1693521 * 2 ^ 59
def prefixEnd_1693521 : Nat := 4983230072969 + 3 ^ 40 * 1693521 * 2
def baseEnd_1693521 : Nat := 193242282551771961110921

theorem tailTrace_1693521 : CollatzResearch.WordTrace tailWord_1693521 prefixEnd_1693521 193242282551771961110921 := by
  unfold tailWord_1693521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61767785297670122205104417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41178523531780081470069611 61767785297670122205104417)
  ·
    refine ⟨46325838973252591653828313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61767785297670122205104417 46325838973252591653828313)
    ·
      refine ⟨34744379229939443740371235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46325838973252591653828313 34744379229939443740371235)
      ·
        refine ⟨52116568844909165610556853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34744379229939443740371235 52116568844909165610556853)
        ·
          refine ⟨4885928329210234275989705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52116568844909165610556853 4885928329210234275989705)
          ·
            refine ⟨3664446246907675706992279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4885928329210234275989705 3664446246907675706992279)
            ·
              refine ⟨5496669370361513560488419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664446246907675706992279 5496669370361513560488419)
              ·
                refine ⟨8245004055542270340732629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496669370361513560488419 8245004055542270340732629)
                ·
                  refine ⟨193242282551771961110921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8245004055542270340732629 193242282551771961110921)
                  ·
                    rfl

theorem cell22_1693521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_1693521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693521 prefixEnd_1693521 := by exact prefixLift 1693521
  have htrace : WordTrace (prefixWord ++ tailWord_1693521) baseStart_1693521 baseEnd_1693521 := by
    simpa [prefixWord, tailWord_1693521, baseEnd_1693521] using wordTrace_append hprefix tailTrace_1693521
  have hstable : (prefixWord ++ tailWord_1693521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693521).length < 2 ^ (prefixWord ++ tailWord_1693521).sum := by decide
  have hdescent : baseEnd_1693521 < baseStart_1693521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693525 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1693525 : Nat := 118140960795 + 1693525 * 2 ^ 59
def prefixEnd_1693525 : Nat := 4983230072969 + 3 ^ 40 * 1693525 * 2
def baseEnd_1693525 : Nat := 579728216937061206232751

theorem tailTrace_1693525 : CollatzResearch.WordTrace tailWord_1693525 prefixEnd_1693525 579728216937061206232751 := by
  unfold tailWord_1693525
  simp only [CollatzResearch.WordTrace]
  refine ⟨61767931189655630888250029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41178620793103753925500019 61767931189655630888250029)
  ·
    refine ⟨23162974196120861583093761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61767931189655630888250029 23162974196120861583093761)
    ·
      refine ⟨17372230647090646187320321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23162974196120861583093761 17372230647090646187320321)
      ·
        refine ⟨13029172985317984640490241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17372230647090646187320321 13029172985317984640490241)
        ·
          refine ⟨9771879738988488480367681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13029172985317984640490241 9771879738988488480367681)
          ·
            refine ⟨7328909804241366360275761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9771879738988488480367681 7328909804241366360275761)
            ·
              refine ⟨5496682353181024770206821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328909804241366360275761 5496682353181024770206821)
              ·
                refine ⟨1030627941221442144413779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5496682353181024770206821 1030627941221442144413779)
                ·
                  refine ⟨1545941911832163216620669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030627941221442144413779 1545941911832163216620669)
                  ·
                    refine ⟨579728216937061206232751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1545941911832163216620669 579728216937061206232751)
                    ·
                      rfl

theorem cell22_1693525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1693525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693525 prefixEnd_1693525 := by exact prefixLift 1693525
  have htrace : WordTrace (prefixWord ++ tailWord_1693525) baseStart_1693525 baseEnd_1693525 := by
    simpa [prefixWord, tailWord_1693525, baseEnd_1693525] using wordTrace_append hprefix tailTrace_1693525
  have hstable : (prefixWord ++ tailWord_1693525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693525).length < 2 ^ (prefixWord ++ tailWord_1693525).sum := by decide
  have hdescent : baseEnd_1693525 < baseStart_1693525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693536 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_1693536 : Nat := 118140960795 + 1693536 * 2 ^ 59
def prefixEnd_1693536 : Nat := 4983230072969 + 3 ^ 40 * 1693536 * 2
def baseEnd_1693536 : Nat := 579731982461860844207717

theorem tailTrace_1693536 : CollatzResearch.WordTrace tailWord_1693536 prefixEnd_1693536 579731982461860844207717 := by
  unfold tailWord_1693536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30884166196307889883450231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41178888261743853177933641 30884166196307889883450231)
  ·
    refine ⟨46326249294461834825175347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30884166196307889883450231 46326249294461834825175347)
    ·
      refine ⟨69489373941692752237763021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46326249294461834825175347 69489373941692752237763021)
      ·
        refine ⟨26058515228134782089161133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69489373941692752237763021 26058515228134782089161133)
        ·
          refine ⟨9771943210550543283435425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26058515228134782089161133 9771943210550543283435425)
          ·
            refine ⟨7328957407912907462576569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9771943210550543283435425 7328957407912907462576569)
            ·
              refine ⟨5496718055934680596932427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328957407912907462576569 5496718055934680596932427)
              ·
                refine ⟨8245077083902020895398641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496718055934680596932427 8245077083902020895398641)
                ·
                  refine ⟨6183807812926515671548981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8245077083902020895398641 6183807812926515671548981)
                  ·
                    refine ⟨579731982461860844207717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6183807812926515671548981 579731982461860844207717)
                    ·
                      rfl

theorem cell22_1693536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_1693536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693536 prefixEnd_1693536 := by exact prefixLift 1693536
  have htrace : WordTrace (prefixWord ++ tailWord_1693536) baseStart_1693536 baseEnd_1693536 := by
    simpa [prefixWord, tailWord_1693536, baseEnd_1693536] using wordTrace_append hprefix tailTrace_1693536
  have hstable : (prefixWord ++ tailWord_1693536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693536).length < 2 ^ (prefixWord ++ tailWord_1693536).sum := by decide
  have hdescent : baseEnd_1693536 < baseStart_1693536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693602 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1693602 : Nat := 118140960795 + 1693602 * 2 ^ 59
def prefixEnd_1693602 : Nat := 4983230072969 + 3 ^ 40 * 1693602 * 2
def baseEnd_1693602 : Nat := 579754575610658672057515

theorem tailTrace_1693602 : CollatzResearch.WordTrace tailWord_1693602 prefixEnd_1693602 579754575610658672057515 := by
  unfold tailWord_1693602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15442684902594168259700765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41180493073584448692535373 15442684902594168259700765)
  ·
    refine ⟨5791006838472813097387787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15442684902594168259700765 5791006838472813097387787)
    ·
      refine ⟨8686510257709219646081681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791006838472813097387787 8686510257709219646081681)
      ·
        refine ⟨6514882693281914734561261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8686510257709219646081681 6514882693281914734561261)
        ·
          refine ⟨2443081009980718025460473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6514882693281914734561261 2443081009980718025460473)
          ·
            refine ⟨1832310757485538519095355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443081009980718025460473 1832310757485538519095355)
            ·
              refine ⟨2748466136228307778643033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832310757485538519095355 2748466136228307778643033)
              ·
                refine ⟨2061349602171230833982275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748466136228307778643033 2061349602171230833982275)
                ·
                  refine ⟨3092024403256846250973413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061349602171230833982275 3092024403256846250973413)
                  ·
                    refine ⟨579754575610658672057515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092024403256846250973413 579754575610658672057515)
                    ·
                      rfl

theorem cell22_1693602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1693602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693602 prefixEnd_1693602 := by exact prefixLift 1693602
  have htrace : WordTrace (prefixWord ++ tailWord_1693602) baseStart_1693602 baseEnd_1693602 := by
    simpa [prefixWord, tailWord_1693602, baseEnd_1693602] using wordTrace_append hprefix tailTrace_1693602
  have hstable : (prefixWord ++ tailWord_1693602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693602).length < 2 ^ (prefixWord ++ tailWord_1693602).sum := by decide
  have hdescent : baseEnd_1693602 < baseStart_1693602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693628 : List Nat := [2, 2, 2, 5, 1, 10]
def baseStart_1693628 : Nat := 118140960795 + 1693628 * 2 ^ 59
def prefixEnd_1693628 : Nat := 4983230072969 + 3 ^ 40 * 1693628 * 2
def baseEnd_1693628 : Nat := 7157573777061768776635

theorem tailTrace_1693628 : CollatzResearch.WordTrace tailWord_1693628 prefixEnd_1693628 7157573777061768776635 := by
  unfold tailWord_1693628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30885843954141239739624769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41181125272188319652833025 30885843954141239739624769)
  ·
    refine ⟨23164382965605929804718577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30885843954141239739624769 23164382965605929804718577)
    ·
      refine ⟨17373287224204447353538933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23164382965605929804718577 17373287224204447353538933)
      ·
        refine ⟨1628745677269166939394275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17373287224204447353538933 1628745677269166939394275)
        ·
          refine ⟨2443118515903750409091413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628745677269166939394275 2443118515903750409091413)
          ·
            refine ⟨7157573777061768776635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2443118515903750409091413 7157573777061768776635)
            ·
              rfl

theorem cell22_1693628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 10].length) (baseStart_1693628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693628 prefixEnd_1693628 := by exact prefixLift 1693628
  have htrace : WordTrace (prefixWord ++ tailWord_1693628) baseStart_1693628 baseEnd_1693628 := by
    simpa [prefixWord, tailWord_1693628, baseEnd_1693628] using wordTrace_append hprefix tailTrace_1693628
  have hstable : (prefixWord ++ tailWord_1693628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693628).length < 2 ^ (prefixWord ++ tailWord_1693628).sum := by decide
  have hdescent : baseEnd_1693628 < baseStart_1693628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693643 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 3, 3]
def baseStart_1693643 : Nat := 118140960795 + 1693643 * 2 ^ 59
def prefixEnd_1693643 : Nat := 4983230072969 + 3 ^ 40 * 1693643 * 2
def baseEnd_1693643 : Nat := 579768610748548231782389

theorem tailTrace_1693643 : CollatzResearch.WordTrace tailWord_1693643 prefixEnd_1693643 579768610748548231782389 := by
  unfold tailWord_1693643
  simp only [CollatzResearch.WordTrace]
  refine ⟨61772235003228137041045583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41181490002152091360697055 61772235003228137041045583)
  ·
    refine ⟨92658352504842205561568375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61772235003228137041045583 92658352504842205561568375)
    ·
      refine ⟨138987528757263308342352563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92658352504842205561568375 138987528757263308342352563)
      ·
        refine ⟨208481293135894962513528845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138987528757263308342352563 208481293135894962513528845)
        ·
          refine ⟨78180484925960610942573317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208481293135894962513528845 78180484925960610942573317)
          ·
            refine ⟨14658840923617614551732497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78180484925960610942573317 14658840923617614551732497)
            ·
              refine ⟨10994130692713210913799373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14658840923617614551732497 10994130692713210913799373)
              ·
                refine ⟨4122799009767454092674765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10994130692713210913799373 4122799009767454092674765)
                ·
                  refine ⟨1546049628662795284753037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4122799009767454092674765 1546049628662795284753037)
                  ·
                    refine ⟨579768610748548231782389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546049628662795284753037 579768610748548231782389)
                    ·
                      rfl

theorem cell22_1693643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 3].length) (baseStart_1693643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693643 prefixEnd_1693643 := by exact prefixLift 1693643
  have htrace : WordTrace (prefixWord ++ tailWord_1693643) baseStart_1693643 baseEnd_1693643 := by
    simpa [prefixWord, tailWord_1693643, baseEnd_1693643] using wordTrace_append hprefix tailTrace_1693643
  have hstable : (prefixWord ++ tailWord_1693643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693643).length < 2 ^ (prefixWord ++ tailWord_1693643).sum := by decide
  have hdescent : baseEnd_1693643 < baseStart_1693643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693694 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1693694 : Nat := 118140960795 + 1693694 * 2 ^ 59
def prefixEnd_1693694 : Nat := 4983230072969 + 3 ^ 40 * 1693694 * 2
def baseEnd_1693694 : Nat := 579786069090801098757233

theorem tailTrace_1693694 : CollatzResearch.WordTrace tailWord_1693694 prefixEnd_1693694 579786069090801098757233 := by
  unfold tailWord_1693694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721761890755421593894017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41182730084028915167434757 7721761890755421593894017)
  ·
    refine ⟨5791321418066566195420513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7721761890755421593894017 5791321418066566195420513)
    ·
      refine ⟨4343491063549924646565385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5791321418066566195420513 4343491063549924646565385)
      ·
        refine ⟨3257618297662443484924039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343491063549924646565385 3257618297662443484924039)
        ·
          refine ⟨4886427446493665227386059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257618297662443484924039 4886427446493665227386059)
          ·
            refine ⟨7329641169740497841079089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886427446493665227386059 7329641169740497841079089)
            ·
              refine ⟨5497230877305373380809317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7329641169740497841079089 5497230877305373380809317)
              ·
                refine ⟨1030730789494757508901747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5497230877305373380809317 1030730789494757508901747)
                ·
                  refine ⟨1546096184242136263352621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030730789494757508901747 1546096184242136263352621)
                  ·
                    refine ⟨579786069090801098757233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546096184242136263352621 579786069090801098757233)
                    ·
                      rfl

theorem cell22_1693694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1693694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693694 prefixEnd_1693694 := by exact prefixLift 1693694
  have htrace : WordTrace (prefixWord ++ tailWord_1693694) baseStart_1693694 baseEnd_1693694 := by
    simpa [prefixWord, tailWord_1693694, baseEnd_1693694] using wordTrace_append hprefix tailTrace_1693694
  have hstable : (prefixWord ++ tailWord_1693694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693694).length < 2 ^ (prefixWord ++ tailWord_1693694).sum := by decide
  have hdescent : baseEnd_1693694 < baseStart_1693694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693720 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_1693720 : Nat := 118140960795 + 1693720 * 2 ^ 59
def prefixEnd_1693720 : Nat := 4983230072969 + 3 ^ 40 * 1693720 * 2
def baseEnd_1693720 : Nat := 579794969422145697607153

theorem tailTrace_1693720 : CollatzResearch.WordTrace tailWord_1693720 prefixEnd_1693720 579794969422145697607153 := by
  unfold tailWord_1693720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30887521711974589595799307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41183362282632786127732409 30887521711974589595799307)
  ·
    refine ⟨46331282567961884393698961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30887521711974589595799307 46331282567961884393698961)
    ·
      refine ⟨34748461925971413295274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46331282567961884393698961 34748461925971413295274221)
      ·
        refine ⟨13030673222239279985727833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34748461925971413295274221 13030673222239279985727833)
        ·
          refine ⟨9773004916679459989295875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13030673222239279985727833 9773004916679459989295875)
          ·
            refine ⟨14659507375019189983943813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9773004916679459989295875 14659507375019189983943813)
            ·
              refine ⟨2748657632816098121989465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14659507375019189983943813 2748657632816098121989465)
              ·
                refine ⟨2061493224612073591492099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748657632816098121989465 2061493224612073591492099)
                ·
                  refine ⟨3092239836918110387238149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061493224612073591492099 3092239836918110387238149)
                  ·
                    refine ⟨579794969422145697607153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092239836918110387238149 579794969422145697607153)
                    ·
                      rfl

theorem cell22_1693720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_1693720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693720 prefixEnd_1693720 := by exact prefixLift 1693720
  have htrace : WordTrace (prefixWord ++ tailWord_1693720) baseStart_1693720 baseEnd_1693720 := by
    simpa [prefixWord, tailWord_1693720, baseEnd_1693720] using wordTrace_append hprefix tailTrace_1693720
  have hstable : (prefixWord ++ tailWord_1693720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693720).length < 2 ^ (prefixWord ++ tailWord_1693720).sum := by decide
  have hdescent : baseEnd_1693720 < baseStart_1693720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693752 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_1693752 : Nat := 118140960795 + 1693752 * 2 ^ 59
def prefixEnd_1693752 : Nat := 4983230072969 + 3 ^ 40 * 1693752 * 2
def baseEnd_1693752 : Nat := 193268641225369426935685

theorem tailTrace_1693752 : CollatzResearch.WordTrace tailWord_1693752 prefixEnd_1693752 193268641225369426935685 := by
  unfold tailWord_1693752
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888105279916624328381755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41184140373222165771175673 30888105279916624328381755)
  ·
    refine ⟨46332157919874936492572633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30888105279916624328381755 46332157919874936492572633)
    ·
      refine ⟨34749118439906202369429475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46332157919874936492572633 34749118439906202369429475)
      ·
        refine ⟨52123677659859303554144213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34749118439906202369429475 52123677659859303554144213)
        ·
          refine ⟨1221648695152952427050255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52123677659859303554144213 1221648695152952427050255)
          ·
            refine ⟨1832473042729428640575383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221648695152952427050255 1832473042729428640575383)
            ·
              refine ⟨2748709564094142960863075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832473042729428640575383 2748709564094142960863075)
              ·
                refine ⟨4123064346141214441294613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748709564094142960863075 4123064346141214441294613)
                ·
                  refine ⟨193268641225369426935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4123064346141214441294613 193268641225369426935685)
                  ·
                    rfl

theorem cell22_1693752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_1693752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693752 prefixEnd_1693752 := by exact prefixLift 1693752
  have htrace : WordTrace (prefixWord ++ tailWord_1693752) baseStart_1693752 baseEnd_1693752 := by
    simpa [prefixWord, tailWord_1693752, baseEnd_1693752] using wordTrace_append hprefix tailTrace_1693752
  have hstable : (prefixWord ++ tailWord_1693752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693752).length < 2 ^ (prefixWord ++ tailWord_1693752).sum := by decide
  have hdescent : baseEnd_1693752 < baseStart_1693752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693883 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_1693883 : Nat := 118140960795 + 1693883 * 2 ^ 59
def prefixEnd_1693883 : Nat := 4983230072969 + 3 ^ 40 * 1693883 * 2
def baseEnd_1693883 : Nat := 579850767653267605781653

theorem tailTrace_1693883 : CollatzResearch.WordTrace tailWord_1693883 prefixEnd_1693883 579850767653267605781653 := by
  unfold tailWord_1693883
  simp only [CollatzResearch.WordTrace]
  refine ⟨61780988522358658029782303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41187325681572438686521535 61780988522358658029782303)
  ·
    refine ⟨92671482783537987044673455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61780988522358658029782303 92671482783537987044673455)
    ·
      refine ⟨139007224175306980567010183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92671482783537987044673455 139007224175306980567010183)
      ·
        refine ⟨208510836262960470850515275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139007224175306980567010183 208510836262960470850515275)
        ·
          refine ⟨312766254394440706275772913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208510836262960470850515275 312766254394440706275772913)
          ·
            refine ⟨234574690795830529706829685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312766254394440706275772913 234574690795830529706829685)
            ·
              refine ⟨21991377262109112160015283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234574690795830529706829685 21991377262109112160015283)
              ·
                refine ⟨32987065893163668240022925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21991377262109112160015283 32987065893163668240022925)
                ·
                  refine ⟨12370149709936375590008597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32987065893163668240022925 12370149709936375590008597)
                  ·
                    refine ⟨579850767653267605781653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12370149709936375590008597 579850767653267605781653)
                    ·
                      rfl

theorem cell22_1693883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_1693883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693883 prefixEnd_1693883 := by exact prefixLift 1693883
  have htrace : WordTrace (prefixWord ++ tailWord_1693883) baseStart_1693883 baseEnd_1693883 := by
    simpa [prefixWord, tailWord_1693883, baseEnd_1693883] using wordTrace_append hprefix tailTrace_1693883
  have hstable : (prefixWord ++ tailWord_1693883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693883).length < 2 ^ (prefixWord ++ tailWord_1693883).sum := by decide
  have hdescent : baseEnd_1693883 < baseStart_1693883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693902 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1693902 : Nat := 118140960795 + 1693902 * 2 ^ 59
def prefixEnd_1693902 : Nat := 4983230072969 + 3 ^ 40 * 1693902 * 2
def baseEnd_1693902 : Nat := 579857271741557889556595

theorem tailTrace_1693902 : CollatzResearch.WordTrace tailWord_1693902 prefixEnd_1693902 579857271741557889556595 := by
  unfold tailWord_1693902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722710188661228034340495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41187787672859882849815973 7722710188661228034340495)
  ·
    refine ⟨11584065282991842051510743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722710188661228034340495 11584065282991842051510743)
    ·
      refine ⟨17376097924487763077266115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584065282991842051510743 17376097924487763077266115)
      ·
        refine ⟨26064146886731644615899173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376097924487763077266115 26064146886731644615899173)
        ·
          refine ⟨4887027541262183365481095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26064146886731644615899173 4887027541262183365481095)
          ·
            refine ⟨7330541311893275048221643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887027541262183365481095 7330541311893275048221643)
            ·
              refine ⟨10995811967839912572332465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330541311893275048221643 10995811967839912572332465)
              ·
                refine ⟨8246858975879934429249349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10995811967839912572332465 8246858975879934429249349)
                ·
                  refine ⟨1546286057977487705484253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8246858975879934429249349 1546286057977487705484253)
                  ·
                    refine ⟨579857271741557889556595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546286057977487705484253 579857271741557889556595)
                    ·
                      rfl

theorem cell22_1693902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1693902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693902 prefixEnd_1693902 := by exact prefixLift 1693902
  have htrace : WordTrace (prefixWord ++ tailWord_1693902) baseStart_1693902 baseEnd_1693902 := by
    simpa [prefixWord, tailWord_1693902, baseEnd_1693902] using wordTrace_append hprefix tailTrace_1693902
  have hstable : (prefixWord ++ tailWord_1693902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693902).length < 2 ^ (prefixWord ++ tailWord_1693902).sum := by decide
  have hdescent : baseEnd_1693902 < baseStart_1693902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693917 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1693917 : Nat := 118140960795 + 1693917 * 2 ^ 59
def prefixEnd_1693917 : Nat := 4983230072969 + 3 ^ 40 * 1693917 * 2
def baseEnd_1693917 : Nat := 579862406548102850431549

theorem tailTrace_1693917 : CollatzResearch.WordTrace tailWord_1693917 prefixEnd_1693917 579862406548102850431549 := by
  unfold tailWord_1693917
  simp only [CollatzResearch.WordTrace]
  refine ⟨61782228604235481836520005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41188152402823654557680003 61782228604235481836520005)
  ·
    refine ⟨11584167863294152844347501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61782228604235481836520005 11584167863294152844347501)
    ·
      refine ⟨4344062948735307316630313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11584167863294152844347501 4344062948735307316630313)
      ·
        refine ⟨3258047211551480487472735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4344062948735307316630313 3258047211551480487472735)
        ·
          refine ⟨4887070817327220731209103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258047211551480487472735 4887070817327220731209103)
          ·
            refine ⟨7330606225990831096813655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887070817327220731209103 7330606225990831096813655)
            ·
              refine ⟨10995909338986246645220483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330606225990831096813655 10995909338986246645220483)
              ·
                refine ⟨16493864008479369967830725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995909338986246645220483 16493864008479369967830725)
                ·
                  refine ⟨3092599501589881868968261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16493864008479369967830725 3092599501589881868968261)
                  ·
                    refine ⟨579862406548102850431549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092599501589881868968261 579862406548102850431549)
                    ·
                      rfl

theorem cell22_1693917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1693917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693917 prefixEnd_1693917 := by exact prefixLift 1693917
  have htrace : WordTrace (prefixWord ++ tailWord_1693917) baseStart_1693917 baseEnd_1693917 := by
    simpa [prefixWord, tailWord_1693917, baseEnd_1693917] using wordTrace_append hprefix tailTrace_1693917
  have hstable : (prefixWord ++ tailWord_1693917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693917).length < 2 ^ (prefixWord ++ tailWord_1693917).sum := by decide
  have hdescent : baseEnd_1693917 < baseStart_1693917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1693964 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_1693964 : Nat := 118140960795 + 1693964 * 2 ^ 59
def prefixEnd_1693964 : Nat := 4983230072969 + 3 ^ 40 * 1693964 * 2
def baseEnd_1693964 : Nat := 579878495608610394506405

theorem tailTrace_1693964 : CollatzResearch.WordTrace tailWord_1693964 prefixEnd_1693964 579878495608610394506405 := by
  unfold tailWord_1693964
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891971417532604431740473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41189295223376805908987297 30891971417532604431740473)
  ·
    refine ⟨23168978563149453323805355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30891971417532604431740473 23168978563149453323805355)
    ·
      refine ⟨34753467844724179985708033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23168978563149453323805355 34753467844724179985708033)
      ·
        refine ⟨26065100883543134989281025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34753467844724179985708033 26065100883543134989281025)
        ·
          refine ⟨19548825662657351241960769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26065100883543134989281025 19548825662657351241960769)
          ·
            refine ⟨14661619246993013431470577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19548825662657351241960769 14661619246993013431470577)
            ·
              refine ⟨10996214435244760073602933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14661619246993013431470577 10996214435244760073602933)
              ·
                refine ⟨1030895103304196256900275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10996214435244760073602933 1030895103304196256900275)
                ·
                  refine ⟨1546342654956294385350413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1030895103304196256900275 1546342654956294385350413)
                  ·
                    refine ⟨579878495608610394506405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546342654956294385350413 579878495608610394506405)
                    ·
                      rfl

theorem cell22_1693964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_1693964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1693964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1693964 prefixEnd_1693964 := by exact prefixLift 1693964
  have htrace : WordTrace (prefixWord ++ tailWord_1693964) baseStart_1693964 baseEnd_1693964 := by
    simpa [prefixWord, tailWord_1693964, baseEnd_1693964] using wordTrace_append hprefix tailTrace_1693964
  have hstable : (prefixWord ++ tailWord_1693964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1693964).length < 2 ^ (prefixWord ++ tailWord_1693964).sum := by decide
  have hdescent : baseEnd_1693964 < baseStart_1693964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1693964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694024 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1694024 : Nat := 118140960795 + 1694024 * 2 ^ 59
def prefixEnd_1694024 : Nat := 4983230072969 + 3 ^ 40 * 1694024 * 2
def baseEnd_1694024 : Nat := 579899034834790238006221

theorem tailTrace_1694024 : CollatzResearch.WordTrace tailWord_1694024 prefixEnd_1694024 579899034834790238006221 := by
  unfold tailWord_1694024
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893065607423919555332563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41190754143231892740443417 30893065607423919555332563)
  ·
    refine ⟨46339598411135879332998845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30893065607423919555332563 46339598411135879332998845)
    ·
      refine ⟨17377349404175954749874567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46339598411135879332998845 17377349404175954749874567)
      ·
        refine ⟨26066024106263932124811851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17377349404175954749874567 26066024106263932124811851)
        ·
          refine ⟨39099036159395898187217777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26066024106263932124811851 39099036159395898187217777)
          ·
            refine ⟨29324277119546923640413333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39099036159395898187217777 29324277119546923640413333)
            ·
              refine ⟨1374575489978762045644375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29324277119546923640413333 1374575489978762045644375)
              ·
                refine ⟨2061863234968143068466563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374575489978762045644375 2061863234968143068466563)
                ·
                  refine ⟨3092794852452214602699845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061863234968143068466563 3092794852452214602699845)
                  ·
                    refine ⟨579899034834790238006221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092794852452214602699845 579899034834790238006221)
                    ·
                      rfl

theorem cell22_1694024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1694024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694024 prefixEnd_1694024 := by exact prefixLift 1694024
  have htrace : WordTrace (prefixWord ++ tailWord_1694024) baseStart_1694024 baseEnd_1694024 := by
    simpa [prefixWord, tailWord_1694024, baseEnd_1694024] using wordTrace_append hprefix tailTrace_1694024
  have hstable : (prefixWord ++ tailWord_1694024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694024).length < 2 ^ (prefixWord ++ tailWord_1694024).sum := by decide
  have hdescent : baseEnd_1694024 < baseStart_1694024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694065 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1694065 : Nat := 118140960795 + 1694065 * 2 ^ 59
def prefixEnd_1694065 : Nat := 4983230072969 + 3 ^ 40 * 1694065 * 2
def baseEnd_1694065 : Nat := 579913069972679797731095

theorem tailTrace_1694065 : CollatzResearch.WordTrace tailWord_1694065 prefixEnd_1694065 579913069972679797731095 := by
  unfold tailWord_1694065
  simp only [CollatzResearch.WordTrace]
  refine ⟨61787626607699303112907649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41191751071799535408605099 61787626607699303112907649)
  ·
    refine ⟨46340719955774477334680737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61787626607699303112907649 46340719955774477334680737)
    ·
      refine ⟨34755539966830858001010553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46340719955774477334680737 34755539966830858001010553)
      ·
        refine ⟨26066654975123143500757915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34755539966830858001010553 26066654975123143500757915)
        ·
          refine ⟨39099982462684715251136873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26066654975123143500757915 39099982462684715251136873)
          ·
            refine ⟨29324986847013536438352655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39099982462684715251136873 29324986847013536438352655)
            ·
              refine ⟨43987480270520304657528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29324986847013536438352655 43987480270520304657528983)
              ·
                refine ⟨65981220405780456986293475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43987480270520304657528983 65981220405780456986293475)
                ·
                  refine ⟨98971830608670685479440213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65981220405780456986293475 98971830608670685479440213)
                  ·
                    refine ⟨579913069972679797731095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98971830608670685479440213 579913069972679797731095)
                    ·
                      rfl

theorem cell22_1694065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1694065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694065 prefixEnd_1694065 := by exact prefixLift 1694065
  have htrace : WordTrace (prefixWord ++ tailWord_1694065) baseStart_1694065 baseEnd_1694065 := by
    simpa [prefixWord, tailWord_1694065, baseEnd_1694065] using wordTrace_append hprefix tailTrace_1694065
  have hstable : (prefixWord ++ tailWord_1694065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694065).length < 2 ^ (prefixWord ++ tailWord_1694065).sum := by decide
  have hdescent : baseEnd_1694065 < baseStart_1694065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694080 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_1694080 : Nat := 118140960795 + 1694080 * 2 ^ 59
def prefixEnd_1694080 : Nat := 4983230072969 + 3 ^ 40 * 1694080 * 2
def baseEnd_1694080 : Nat := 579918204779224758606049

theorem tailTrace_1694080 : CollatzResearch.WordTrace tailWord_1694080 prefixEnd_1694080 579918204779224758606049 := by
  unfold tailWord_1694080
  simp only [CollatzResearch.WordTrace]
  refine ⟨30894086851322480337351847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41192115801763307116469129 30894086851322480337351847)
  ·
    refine ⟨46341130276983720506027771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30894086851322480337351847 46341130276983720506027771)
    ·
      refine ⟨69511695415475580759041657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46341130276983720506027771 69511695415475580759041657)
      ·
        refine ⟨52133771561606685569281243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69511695415475580759041657 52133771561606685569281243)
        ·
          refine ⟨78200657342410028353921865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52133771561606685569281243 78200657342410028353921865)
          ·
            refine ⟨58650493006807521265441399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78200657342410028353921865 58650493006807521265441399)
            ·
              refine ⟨87975739510211281898162099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58650493006807521265441399 87975739510211281898162099)
              ·
                refine ⟨131963609265316922847243149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87975739510211281898162099 131963609265316922847243149)
                ·
                  refine ⟨49486353474493846067716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131963609265316922847243149 49486353474493846067716181)
                  ·
                    refine ⟨579918204779224758606049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49486353474493846067716181 579918204779224758606049)
                    ·
                      rfl

theorem cell22_1694080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_1694080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694080 prefixEnd_1694080 := by exact prefixLift 1694080
  have htrace : WordTrace (prefixWord ++ tailWord_1694080) baseStart_1694080 baseEnd_1694080 := by
    simpa [prefixWord, tailWord_1694080, baseEnd_1694080] using wordTrace_append hprefix tailTrace_1694080
  have hstable : (prefixWord ++ tailWord_1694080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694080).length < 2 ^ (prefixWord ++ tailWord_1694080).sum := by decide
  have hdescent : baseEnd_1694080 < baseStart_1694080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694187 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_1694187 : Nat := 118140960795 + 1694187 * 2 ^ 59
def prefixEnd_1694187 : Nat := 4983230072969 + 3 ^ 40 * 1694187 * 2
def baseEnd_1694187 : Nat := 579954833065912146180721

theorem tailTrace_1694187 : CollatzResearch.WordTrace tailWord_1694187 prefixEnd_1694187 579954833065912146180721 := by
  unfold tailWord_1694187
  simp only [CollatzResearch.WordTrace]
  refine ⟨61792076313257317948848815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41194717542171545299232543 61792076313257317948848815)
  ·
    refine ⟨92688114469885976923273223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61792076313257317948848815 92688114469885976923273223)
    ·
      refine ⟨139032171704828965384909835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92688114469885976923273223 139032171704828965384909835)
      ·
        refine ⟨208548257557243448077364753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139032171704828965384909835 208548257557243448077364753)
        ·
          refine ⟨156411193167932586058023565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208548257557243448077364753 156411193167932586058023565)
          ·
            refine ⟨58654197437974719771758837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156411193167932586058023565 58654197437974719771758837)
            ·
              refine ⟨5498831009810129978602391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58654197437974719771758837 5498831009810129978602391)
              ·
                refine ⟨8248246514715194967903587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498831009810129978602391 8248246514715194967903587)
                ·
                  refine ⟨12372369772072792451855381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8248246514715194967903587 12372369772072792451855381)
                  ·
                    refine ⟨579954833065912146180721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12372369772072792451855381 579954833065912146180721)
                    ·
                      rfl

theorem cell22_1694187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_1694187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694187 prefixEnd_1694187 := by exact prefixLift 1694187
  have htrace : WordTrace (prefixWord ++ tailWord_1694187) baseStart_1694187 baseEnd_1694187 := by
    simpa [prefixWord, tailWord_1694187, baseEnd_1694187] using wordTrace_append hprefix tailTrace_1694187
  have hstable : (prefixWord ++ tailWord_1694187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694187).length < 2 ^ (prefixWord ++ tailWord_1694187).sum := by decide
  have hdescent : baseEnd_1694187 < baseStart_1694187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694236 : List Nat := [2, 2, 3, 1, 2, 4, 2, 6]
def baseStart_1694236 : Nat := 118140960795 + 1694236 * 2 ^ 59
def prefixEnd_1694236 : Nat := 4983230072969 + 3 ^ 40 * 1694236 * 2
def baseEnd_1694236 : Nat := 64441289640810261300619

theorem tailTrace_1694236 : CollatzResearch.WordTrace tailWord_1694236 prefixEnd_1694236 64441289640810261300619 := by
  unfold tailWord_1694236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896931745039899658691281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41195908993386532878255041 30896931745039899658691281)
  ·
    refine ⟨23172698808779924744018461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30896931745039899658691281 23172698808779924744018461)
    ·
      refine ⟨8689762053292471779006923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23172698808779924744018461 8689762053292471779006923)
      ·
        refine ⟨13034643079938707668510385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8689762053292471779006923 13034643079938707668510385)
        ·
          refine ⟨9775982309954030751382789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13034643079938707668510385 9775982309954030751382789)
          ·
            refine ⟨1832996683116380765884273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9775982309954030751382789 1832996683116380765884273)
            ·
              refine ⟨1374747512337285574413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832996683116380765884273 1374747512337285574413205)
              ·
                refine ⟨64441289640810261300619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1374747512337285574413205 64441289640810261300619)
                ·
                  rfl

theorem cell22_1694236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_1694236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694236 prefixEnd_1694236 := by exact prefixLift 1694236
  have htrace : WordTrace (prefixWord ++ tailWord_1694236) baseStart_1694236 baseEnd_1694236 := by
    simpa [prefixWord, tailWord_1694236, baseEnd_1694236] using wordTrace_append hprefix tailTrace_1694236
  have hstable : (prefixWord ++ tailWord_1694236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694236).length < 2 ^ (prefixWord ++ tailWord_1694236).sum := by decide
  have hdescent : baseEnd_1694236 < baseStart_1694236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694264 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_1694264 : Nat := 118140960795 + 1694264 * 2 ^ 59
def prefixEnd_1694264 : Nat := 4983230072969 + 3 ^ 40 * 1694264 * 2
def baseEnd_1694264 : Nat := 193327063913169870668495

theorem tailTrace_1694264 : CollatzResearch.WordTrace tailWord_1694264 prefixEnd_1694264 193327063913169870668495 := by
  unfold tailWord_1694264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30897442366989180049700923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41196589822652240066267897 30897442366989180049700923)
  ·
    refine ⟨46346163550483770074551385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30897442366989180049700923 46346163550483770074551385)
    ·
      refine ⟨34759622662862827555913539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46346163550483770074551385 34759622662862827555913539)
      ·
        refine ⟨52139433994294241333870309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34759622662862827555913539 52139433994294241333870309)
        ·
          refine ⟨9776143873930170250100683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52139433994294241333870309 9776143873930170250100683)
          ·
            refine ⟨14664215810895255375151025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776143873930170250100683 14664215810895255375151025)
            ·
              refine ⟨10998161858171441531363269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14664215810895255375151025 10998161858171441531363269)
              ·
                refine ⟨2062155348407145287130613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10998161858171441531363269 2062155348407145287130613)
                ·
                  refine ⟨193327063913169870668495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2062155348407145287130613 193327063913169870668495)
                  ·
                    rfl

theorem cell22_1694264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_1694264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694264 prefixEnd_1694264 := by exact prefixLift 1694264
  have htrace : WordTrace (prefixWord ++ tailWord_1694264) baseStart_1694264 baseEnd_1694264 := by
    simpa [prefixWord, tailWord_1694264, baseEnd_1694264] using wordTrace_append hprefix tailTrace_1694264
  have hstable : (prefixWord ++ tailWord_1694264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694264).length < 2 ^ (prefixWord ++ tailWord_1694264).sum := by decide
  have hdescent : baseEnd_1694264 < baseStart_1694264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694268 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1694268 : Nat := 118140960795 + 1694268 * 2 ^ 59
def prefixEnd_1694268 : Nat := 4983230072969 + 3 ^ 40 * 1694268 * 2
def baseEnd_1694268 : Nat := 579982561021254934905473

theorem tailTrace_1694268 : CollatzResearch.WordTrace tailWord_1694268 prefixEnd_1694268 579982561021254934905473 := by
  unfold tailWord_1694268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30897515312981934391273729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41196687083975912521698305 30897515312981934391273729)
  ·
    refine ⟨23173136484736450793455297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30897515312981934391273729 23173136484736450793455297)
    ·
      refine ⟨17379852363552338095091473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23173136484736450793455297 17379852363552338095091473)
      ·
        refine ⟨13034889272664253571318605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17379852363552338095091473 13034889272664253571318605)
        ·
          refine ⟨4888083477249095089244477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13034889272664253571318605 4888083477249095089244477)
          ·
            refine ⟨1833031303968410658466679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4888083477249095089244477 1833031303968410658466679)
            ·
              refine ⟨2749546955952615987700019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833031303968410658466679 2749546955952615987700019)
              ·
                refine ⟨4124320433928923981550029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749546955952615987700019 4124320433928923981550029)
                ·
                  refine ⟨1546620162723346493081261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4124320433928923981550029 1546620162723346493081261)
                  ·
                    refine ⟨579982561021254934905473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546620162723346493081261 579982561021254934905473)
                    ·
                      rfl

theorem cell22_1694268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1694268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694268 prefixEnd_1694268 := by exact prefixLift 1694268
  have htrace : WordTrace (prefixWord ++ tailWord_1694268) baseStart_1694268 baseEnd_1694268 := by
    simpa [prefixWord, tailWord_1694268, baseEnd_1694268] using wordTrace_append hprefix tailTrace_1694268
  have hstable : (prefixWord ++ tailWord_1694268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694268).length < 2 ^ (prefixWord ++ tailWord_1694268).sum := by decide
  have hdescent : baseEnd_1694268 < baseStart_1694268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694339 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_1694339 : Nat := 118140960795 + 1694339 * 2 ^ 59
def prefixEnd_1694339 : Nat := 4983230072969 + 3 ^ 40 * 1694339 * 2
def baseEnd_1694339 : Nat := 580006865772234416380255

theorem tailTrace_1694339 : CollatzResearch.WordTrace tailWord_1694339 prefixEnd_1694339 580006865772234416380255 := by
  unfold tailWord_1694339
  simp only [CollatzResearch.WordTrace]
  refine ⟨61797620208706647908382071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41198413472471098605588047 61797620208706647908382071)
  ·
    refine ⟨92696430313059971862573107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61797620208706647908382071 92696430313059971862573107)
    ·
      refine ⟨139044645469589957793859661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92696430313059971862573107 139044645469589957793859661)
      ·
        refine ⟨52141742051096234172697373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139044645469589957793859661 52141742051096234172697373)
        ·
          refine ⟨19553153269161087814761515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52141742051096234172697373 19553153269161087814761515)
          ·
            refine ⟨29329729903741631722142273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19553153269161087814761515 29329729903741631722142273)
            ·
              refine ⟨21997297427806223791606705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29329729903741631722142273 21997297427806223791606705)
              ·
                refine ⟨16497973070854667843705029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21997297427806223791606705 16497973070854667843705029)
                ·
                  refine ⟨3093369950785250220694693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16497973070854667843705029 3093369950785250220694693)
                  ·
                    refine ⟨580006865772234416380255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093369950785250220694693 580006865772234416380255)
                    ·
                      rfl

theorem cell22_1694339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_1694339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694339 prefixEnd_1694339 := by exact prefixLift 1694339
  have htrace : WordTrace (prefixWord ++ tailWord_1694339) baseStart_1694339 baseEnd_1694339 := by
    simpa [prefixWord, tailWord_1694339, baseEnd_1694339] using wordTrace_append hprefix tailTrace_1694339
  have hstable : (prefixWord ++ tailWord_1694339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694339).length < 2 ^ (prefixWord ++ tailWord_1694339).sum := by decide
  have hdescent : baseEnd_1694339 < baseStart_1694339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694341 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1694341 : Nat := 118140960795 + 1694341 * 2 ^ 59
def prefixEnd_1694341 : Nat := 4983230072969 + 3 ^ 40 * 1694341 * 2
def baseEnd_1694341 : Nat := 580007550413107077830249

theorem tailTrace_1694341 : CollatzResearch.WordTrace tailWord_1694341 prefixEnd_1694341 580007550413107077830249 := by
  unfold tailWord_1694341
  simp only [CollatzResearch.WordTrace]
  refine ⟨61797693154699402249954877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41198462103132934833303251 61797693154699402249954877)
  ·
    refine ⟨23174134933012275843733079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61797693154699402249954877 23174134933012275843733079)
    ·
      refine ⟨34761202399518413765599619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23174134933012275843733079 34761202399518413765599619)
      ·
        refine ⟨52141803599277620648399429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34761202399518413765599619 52141803599277620648399429)
        ·
          refine ⟨9776588174864553871574893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52141803599277620648399429 9776588174864553871574893)
          ·
            refine ⟨3666220565574207701840585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9776588174864553871574893 3666220565574207701840585)
            ·
              refine ⟨2749665424180655776380439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666220565574207701840585 2749665424180655776380439)
              ·
                refine ⟨4124498136270983664570659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749665424180655776380439 4124498136270983664570659)
                ·
                  refine ⟨6186747204406475496855989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124498136270983664570659 6186747204406475496855989)
                  ·
                    refine ⟨580007550413107077830249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6186747204406475496855989 580007550413107077830249)
                    ·
                      rfl

theorem cell22_1694341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1694341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694341 prefixEnd_1694341 := by exact prefixLift 1694341
  have htrace : WordTrace (prefixWord ++ tailWord_1694341) baseStart_1694341 baseEnd_1694341 := by
    simpa [prefixWord, tailWord_1694341, baseEnd_1694341] using wordTrace_append hprefix tailTrace_1694341
  have hstable : (prefixWord ++ tailWord_1694341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694341).length < 2 ^ (prefixWord ++ tailWord_1694341).sum := by decide
  have hdescent : baseEnd_1694341 < baseStart_1694341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694362 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_1694362 : Nat := 118140960795 + 1694362 * 2 ^ 59
def prefixEnd_1694362 : Nat := 4983230072969 + 3 ^ 40 * 1694362 * 2
def baseEnd_1694362 : Nat := 580014739142270023055185

theorem tailTrace_1694362 : CollatzResearch.WordTrace tailWord_1694362 prefixEnd_1694362 580014739142270023055185 := by
  unfold tailWord_1694362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15449614771905830709117335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41198972725082215224312893 15449614771905830709117335)
  ·
    refine ⟨23174422157858746063676003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15449614771905830709117335 23174422157858746063676003)
    ·
      refine ⟨34761633236788119095514005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23174422157858746063676003 34761633236788119095514005)
      ·
        refine ⟨1629451557974443082602219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34761633236788119095514005 1629451557974443082602219)
        ·
          refine ⟨2444177336961664623903329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629451557974443082602219 2444177336961664623903329)
          ·
            refine ⟨1833133002721248467927497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444177336961664623903329 1833133002721248467927497)
            ·
              refine ⟨1374849752040936350945623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833133002721248467927497 1374849752040936350945623)
              ·
                refine ⟨2062274628061404526418435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374849752040936350945623 2062274628061404526418435)
                ·
                  refine ⟨3093411942092106789627653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062274628061404526418435 3093411942092106789627653)
                  ·
                    refine ⟨580014739142270023055185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093411942092106789627653 580014739142270023055185)
                    ·
                      rfl

theorem cell22_1694362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_1694362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694362 prefixEnd_1694362 := by exact prefixLift 1694362
  have htrace : WordTrace (prefixWord ++ tailWord_1694362) baseStart_1694362 baseEnd_1694362 := by
    simpa [prefixWord, tailWord_1694362, baseEnd_1694362] using wordTrace_append hprefix tailTrace_1694362
  have hstable : (prefixWord ++ tailWord_1694362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694362).length < 2 ^ (prefixWord ++ tailWord_1694362).sum := by decide
  have hdescent : baseEnd_1694362 < baseStart_1694362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694375 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1694375 : Nat := 118140960795 + 1694375 * 2 ^ 59
def prefixEnd_1694375 : Nat := 4983230072969 + 3 ^ 40 * 1694375 * 2
def baseEnd_1694375 : Nat := 580019189307942322480145

theorem tailTrace_1694375 : CollatzResearch.WordTrace tailWord_1694375 prefixEnd_1694375 580019189307942322480145 := by
  unfold tailWord_1694375
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798933236576226056692579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41199288824384150704461719 61798933236576226056692579)
  ·
    refine ⟨92698399854864339085038869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61798933236576226056692579 92698399854864339085038869)
    ·
      refine ⟨4345237493196765894611197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92698399854864339085038869 4345237493196765894611197)
      ·
        refine ⟨1629464059948787210479199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4345237493196765894611197 1629464059948787210479199)
        ·
          refine ⟨2444196089923180815718799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629464059948787210479199 2444196089923180815718799)
          ·
            refine ⟨3666294134884771223578199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444196089923180815718799 3666294134884771223578199)
            ·
              refine ⟨5499441202327156835367299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666294134884771223578199 5499441202327156835367299)
              ·
                refine ⟨8249161803490735253050949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499441202327156835367299 8249161803490735253050949)
                ·
                  refine ⟨1546717838154512859947053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8249161803490735253050949 1546717838154512859947053)
                  ·
                    refine ⟨580019189307942322480145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546717838154512859947053 580019189307942322480145)
                    ·
                      rfl

theorem cell22_1694375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1694375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694375 prefixEnd_1694375 := by exact prefixLift 1694375
  have htrace : WordTrace (prefixWord ++ tailWord_1694375) baseStart_1694375 baseEnd_1694375 := by
    simpa [prefixWord, tailWord_1694375, baseEnd_1694375] using wordTrace_append hprefix tailTrace_1694375
  have hstable : (prefixWord ++ tailWord_1694375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694375).length < 2 ^ (prefixWord ++ tailWord_1694375).sum := by decide
  have hdescent : baseEnd_1694375 < baseStart_1694375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694437 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_1694437 : Nat := 118140960795 + 1694437 * 2 ^ 59
def prefixEnd_1694437 : Nat := 4983230072969 + 3 ^ 40 * 1694437 * 2
def baseEnd_1694437 : Nat := 580040413174994827429955

theorem tailTrace_1694437 : CollatzResearch.WordTrace tailWord_1694437 prefixEnd_1694437 580040413174994827429955 := by
  unfold tailWord_1694437
  simp only [CollatzResearch.WordTrace]
  refine ⟨61801194562351610645449565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41200796374901073763633043 61801194562351610645449565)
  ·
    refine ⟨23175447960881853992043587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61801194562351610645449565 23175447960881853992043587)
    ·
      refine ⟨34763171941322780988065381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175447960881853992043587 34763171941322780988065381)
      ·
        refine ⟨6518094738998021435262259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34763171941322780988065381 6518094738998021435262259)
        ·
          refine ⟨9777142108497032152893389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518094738998021435262259 9777142108497032152893389)
          ·
            refine ⟨3666428290686387057335021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9777142108497032152893389 3666428290686387057335021)
            ·
              refine ⟨1374910609007395146500633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3666428290686387057335021 1374910609007395146500633)
              ·
                refine ⟨1031182956755546359875475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374910609007395146500633 1031182956755546359875475)
                ·
                  refine ⟨1546774435133319539813213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031182956755546359875475 1546774435133319539813213)
                  ·
                    refine ⟨580040413174994827429955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1546774435133319539813213 580040413174994827429955)
                    ·
                      rfl

theorem cell22_1694437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_1694437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694437 prefixEnd_1694437 := by exact prefixLift 1694437
  have htrace : WordTrace (prefixWord ++ tailWord_1694437) baseStart_1694437 baseEnd_1694437 := by
    simpa [prefixWord, tailWord_1694437, baseEnd_1694437] using wordTrace_append hprefix tailTrace_1694437
  have hstable : (prefixWord ++ tailWord_1694437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694437).length < 2 ^ (prefixWord ++ tailWord_1694437).sum := by decide
  have hdescent : baseEnd_1694437 < baseStart_1694437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694450 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1694450 : Nat := 118140960795 + 1694450 * 2 ^ 59
def prefixEnd_1694450 : Nat := 4983230072969 + 3 ^ 40 * 1694450 * 2
def baseEnd_1694450 : Nat := 193348287780222375618305

theorem tailTrace_1694450 : CollatzResearch.WordTrace tailWord_1694450 prefixEnd_1694450 193348287780222375618305 := by
  unfold tailWord_1694450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450417177826128466418201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41201112474203009243781869 15450417177826128466418201)
  ·
    refine ⟨11587812883369596349813651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15450417177826128466418201 11587812883369596349813651)
    ·
      refine ⟨17381719325054394524720477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11587812883369596349813651 17381719325054394524720477)
      ·
        refine ⟨6518144746895397946770179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17381719325054394524720477 6518144746895397946770179)
        ·
          refine ⟨9777217120343096920155269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518144746895397946770179 9777217120343096920155269)
          ·
            refine ⟨1833228210064330672529113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9777217120343096920155269 1833228210064330672529113)
            ·
              refine ⟨1374921157548248004396835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833228210064330672529113 1374921157548248004396835)
              ·
                refine ⟨2062381736322372006595253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374921157548248004396835 2062381736322372006595253)
                ·
                  refine ⟨193348287780222375618305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2062381736322372006595253 193348287780222375618305)
                  ·
                    rfl

theorem cell22_1694450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1694450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694450 prefixEnd_1694450 := by exact prefixLift 1694450
  have htrace : WordTrace (prefixWord ++ tailWord_1694450) baseStart_1694450 baseEnd_1694450 := by
    simpa [prefixWord, tailWord_1694450, baseEnd_1694450] using wordTrace_append hprefix tailTrace_1694450
  have hstable : (prefixWord ++ tailWord_1694450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694450).length < 2 ^ (prefixWord ++ tailWord_1694450).sum := by decide
  have hdescent : baseEnd_1694450 < baseStart_1694450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694478 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_1694478 : Nat := 118140960795 + 1694478 * 2 ^ 59
def prefixEnd_1694478 : Nat := 4983230072969 + 3 ^ 40 * 1694478 * 2
def baseEnd_1694478 : Nat := 193351482770961462384943

theorem tailTrace_1694478 : CollatzResearch.WordTrace tailWord_1694478 prefixEnd_1694478 193351482770961462384943 := by
  unfold tailWord_1694478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725336244400384330961511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41201793303468716431794725 7725336244400384330961511)
  ·
    refine ⟨11588004366600576496442267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725336244400384330961511 11588004366600576496442267)
    ·
      refine ⟨17382006549900864744663401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588004366600576496442267 17382006549900864744663401)
      ·
        refine ⟨13036504912425648558497551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17382006549900864744663401 13036504912425648558497551)
        ·
          refine ⟨19554757368638472837746327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036504912425648558497551 19554757368638472837746327)
          ·
            refine ⟨29332136052957709256619491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554757368638472837746327 29332136052957709256619491)
            ·
              refine ⟨43998204079436563884929237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29332136052957709256619491 43998204079436563884929237)
              ·
                refine ⟨1031207908111794466053029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43998204079436563884929237 1031207908111794466053029)
                ·
                  refine ⟨193351482770961462384943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031207908111794466053029 193351482770961462384943)
                  ·
                    rfl

theorem cell22_1694478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_1694478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694478 prefixEnd_1694478 := by exact prefixLift 1694478
  have htrace : WordTrace (prefixWord ++ tailWord_1694478) baseStart_1694478 baseEnd_1694478 := by
    simpa [prefixWord, tailWord_1694478, baseEnd_1694478] using wordTrace_append hprefix tailTrace_1694478
  have hstable : (prefixWord ++ tailWord_1694478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694478).length < 2 ^ (prefixWord ++ tailWord_1694478).sum := by decide
  have hdescent : baseEnd_1694478 < baseStart_1694478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694495 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 4]
def baseStart_1694495 : Nat := 118140960795 + 1694495 * 2 ^ 59
def prefixEnd_1694495 : Nat := 4983230072969 + 3 ^ 40 * 1694495 * 2
def baseEnd_1694495 : Nat := 193353422586767336493259

theorem tailTrace_1694495 : CollatzResearch.WordTrace tailWord_1694495 prefixEnd_1694495 193353422586767336493259 := by
  unfold tailWord_1694495
  simp only [CollatzResearch.WordTrace]
  refine ⟨61803309996141486551060939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41202206664094324367373959 61803309996141486551060939)
  ·
    refine ⟨92704964994212229826591409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61803309996141486551060939 92704964994212229826591409)
    ·
      refine ⟨69528723745659172369943557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92704964994212229826591409 69528723745659172369943557)
      ·
        refine ⟨13036635702311094819364417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69528723745659172369943557 13036635702311094819364417)
        ·
          refine ⟨9777476776733321114523313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13036635702311094819364417 9777476776733321114523313)
          ·
            refine ⟨7333107582549990835892485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9777476776733321114523313 7333107582549990835892485)
            ·
              refine ⟨1374957671728123281729841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7333107582549990835892485 1374957671728123281729841)
              ·
                refine ⟨1031218253796092461297381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374957671728123281729841 1031218253796092461297381)
                ·
                  refine ⟨193353422586767336493259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031218253796092461297381 193353422586767336493259)
                  ·
                    rfl

theorem cell22_1694495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 4].length) (baseStart_1694495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694495 prefixEnd_1694495 := by exact prefixLift 1694495
  have htrace : WordTrace (prefixWord ++ tailWord_1694495) baseStart_1694495 baseEnd_1694495 := by
    simpa [prefixWord, tailWord_1694495, baseEnd_1694495] using wordTrace_append hprefix tailTrace_1694495
  have hstable : (prefixWord ++ tailWord_1694495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694495).length < 2 ^ (prefixWord ++ tailWord_1694495).sum := by decide
  have hdescent : baseEnd_1694495 < baseStart_1694495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694510 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1694510 : Nat := 118140960795 + 1694510 * 2 ^ 59
def prefixEnd_1694510 : Nat := 4983230072969 + 3 ^ 40 * 1694510 * 2
def baseEnd_1694510 : Nat := 580065402566846970354731

theorem tailTrace_1694510 : CollatzResearch.WordTrace tailWord_1694510 prefixEnd_1694510 580065402566846970354731 := by
  unfold tailWord_1694510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725482136385893014107123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41202571394058096075237989 7725482136385893014107123)
  ·
    refine ⟨11588223204578839521160685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725482136385893014107123 11588223204578839521160685)
    ·
      refine ⟨4345583701717064820435257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11588223204578839521160685 4345583701717064820435257)
      ·
        refine ⟨3259187776287798615326443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4345583701717064820435257 3259187776287798615326443)
        ·
          refine ⟨4888781664431697922989665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259187776287798615326443 4888781664431697922989665)
          ·
            refine ⟨3666586248323773442242249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4888781664431697922989665 3666586248323773442242249)
            ·
              refine ⟨2749939686242830081681687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666586248323773442242249 2749939686242830081681687)
              ·
                refine ⟨4124909529364245122522531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749939686242830081681687 4124909529364245122522531)
                ·
                  refine ⟨6187364294046367683783797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124909529364245122522531 6187364294046367683783797)
                  ·
                    refine ⟨580065402566846970354731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6187364294046367683783797 580065402566846970354731)
                    ·
                      rfl

theorem cell22_1694510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1694510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694510 prefixEnd_1694510 := by exact prefixLift 1694510
  have htrace : WordTrace (prefixWord ++ tailWord_1694510) baseStart_1694510 baseEnd_1694510 := by
    simpa [prefixWord, tailWord_1694510, baseEnd_1694510] using wordTrace_append hprefix tailTrace_1694510
  have hstable : (prefixWord ++ tailWord_1694510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694510).length < 2 ^ (prefixWord ++ tailWord_1694510).sum := by decide
  have hdescent : baseEnd_1694510 < baseStart_1694510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694611 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_1694611 : Nat := 118140960795 + 1694611 * 2 ^ 59
def prefixEnd_1694611 : Nat := 4983230072969 + 3 ^ 40 * 1694611 * 2
def baseEnd_1694611 : Nat := 580099976930916373579421

theorem tailTrace_1694611 : CollatzResearch.WordTrace tailWord_1694611 prefixEnd_1694611 580099976930916373579421 := by
  unfold tailWord_1694611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807540863721238362283687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41205027242480825574855791 61807540863721238362283687)
  ·
    refine ⟨92711311295581857543425531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61807540863721238362283687 92711311295581857543425531)
    ·
      refine ⟨139066966943372786315138297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92711311295581857543425531 139066966943372786315138297)
      ·
        refine ⟨104300225207529589736353723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139066966943372786315138297 104300225207529589736353723)
        ·
          refine ⟨156450337811294384604530585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104300225207529589736353723 156450337811294384604530585)
          ·
            refine ⟨117337753358470788453397939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156450337811294384604530585 117337753358470788453397939)
            ·
              refine ⟨176006630037706182680096909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117337753358470788453397939 176006630037706182680096909)
              ·
                refine ⟨66002486264139818505036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176006630037706182680096909 66002486264139818505036341)
                ·
                  refine ⟨6187733087263107984847157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66002486264139818505036341 6187733087263107984847157)
                  ·
                    refine ⟨580099976930916373579421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6187733087263107984847157 580099976930916373579421)
                    ·
                      rfl

theorem cell22_1694611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_1694611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694611 prefixEnd_1694611 := by exact prefixLift 1694611
  have htrace : WordTrace (prefixWord ++ tailWord_1694611) baseStart_1694611 baseEnd_1694611 := by
    simpa [prefixWord, tailWord_1694611, baseEnd_1694611] using wordTrace_append hprefix tailTrace_1694611
  have hstable : (prefixWord ++ tailWord_1694611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694611).length < 2 ^ (prefixWord ++ tailWord_1694611).sum := by decide
  have hdescent : baseEnd_1694611 < baseStart_1694611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694613 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 6]
def baseStart_1694613 : Nat := 118140960795 + 1694613 * 2 ^ 59
def prefixEnd_1694613 : Nat := 4983230072969 + 3 ^ 40 * 1694613 * 2
def baseEnd_1694613 : Nat := 193366887190596345009805

theorem tailTrace_1694613 : CollatzResearch.WordTrace tailWord_1694613 prefixEnd_1694613 193366887190596345009805 := by
  unfold tailWord_1694613
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807613809713992703856493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41205075873142661802570995 61807613809713992703856493)
  ·
    refine ⟨23177855178642747263946185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61807613809713992703856493 23177855178642747263946185)
    ·
      refine ⟨17383391383982060447959639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23177855178642747263946185 17383391383982060447959639)
      ·
        refine ⟨26075087075973090671939459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383391383982060447959639 26075087075973090671939459)
        ·
          refine ⟨39112630613959636007909189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26075087075973090671939459 39112630613959636007909189)
          ·
            refine ⟨7333618240117431751482973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39112630613959636007909189 7333618240117431751482973)
            ·
              refine ⟨2750106840044036906806115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7333618240117431751482973 2750106840044036906806115)
              ·
                refine ⟨4125160260066055360209173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750106840044036906806115 4125160260066055360209173)
                ·
                  refine ⟨193366887190596345009805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4125160260066055360209173 193366887190596345009805)
                  ·
                    rfl

theorem cell22_1694613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_1694613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694613 prefixEnd_1694613 := by exact prefixLift 1694613
  have htrace : WordTrace (prefixWord ++ tailWord_1694613) baseStart_1694613 baseEnd_1694613 := by
    simpa [prefixWord, tailWord_1694613, baseEnd_1694613] using wordTrace_append hprefix tailTrace_1694613
  have hstable : (prefixWord ++ tailWord_1694613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694613).length < 2 ^ (prefixWord ++ tailWord_1694613).sum := by decide
  have hdescent : baseEnd_1694613 < baseStart_1694613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694628 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1694628 : Nat := 118140960795 + 1694628 * 2 ^ 59
def prefixEnd_1694628 : Nat := 4983230072969 + 3 ^ 40 * 1694628 * 2
def baseEnd_1694628 : Nat := 580105796378333995904369

theorem tailTrace_1694628 : CollatzResearch.WordTrace tailWord_1694628 prefixEnd_1694628 580105796378333995904369 := by
  unfold tailWord_1694628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904080452329825132826269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41205440603106433510435025 30904080452329825132826269)
  ·
    refine ⟨11589030169623684424809851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30904080452329825132826269 11589030169623684424809851)
    ·
      refine ⟨17383545254435526637214777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11589030169623684424809851 17383545254435526637214777)
      ·
        refine ⟨13037658940826644977911083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17383545254435526637214777 13037658940826644977911083)
        ·
          refine ⟨19556488411239967466866625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037658940826644977911083 19556488411239967466866625)
          ·
            refine ⟨14667366308429975600149969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19556488411239967466866625 14667366308429975600149969)
            ·
              refine ⟨11000524731322481700112477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14667366308429975600149969 11000524731322481700112477)
              ·
                refine ⟨4125196774245930637542179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11000524731322481700112477 4125196774245930637542179)
                ·
                  refine ⟨6187795161368895956313269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125196774245930637542179 6187795161368895956313269)
                  ·
                    refine ⟨580105796378333995904369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6187795161368895956313269 580105796378333995904369)
                    ·
                      rfl

theorem cell22_1694628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1694628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694628 prefixEnd_1694628 := by exact prefixLift 1694628
  have htrace : WordTrace (prefixWord ++ tailWord_1694628) baseStart_1694628 baseEnd_1694628 := by
    simpa [prefixWord, tailWord_1694628, baseEnd_1694628] using wordTrace_append hprefix tailTrace_1694628
  have hstable : (prefixWord ++ tailWord_1694628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694628).length < 2 ^ (prefixWord ++ tailWord_1694628).sum := by decide
  have hdescent : baseEnd_1694628 < baseStart_1694628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694658 : List Nat := [3, 5, 14]
def baseStart_1694658 : Nat := 118140960795 + 1694658 * 2 ^ 59
def prefixEnd_1694658 : Nat := 4983230072969 + 3 ^ 40 * 1694658 * 2
def baseEnd_1694658 : Nat := 265256545949439377071

theorem tailTrace_1694658 : CollatzResearch.WordTrace tailWord_1694658 prefixEnd_1694658 265256545949439377071 := by
  unfold tailWord_1694658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452313773637741347311157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41206170063033976926163085 15452313773637741347311157)
  ·
    refine ⟨1448654416278538251310421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15452313773637741347311157 1448654416278538251310421)
    ·
      refine ⟨265256545949439377071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1448654416278538251310421 265256545949439377071)
      ·
        rfl

theorem cell22_1694658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 14].length) (baseStart_1694658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694658 prefixEnd_1694658 := by exact prefixLift 1694658
  have htrace : WordTrace (prefixWord ++ tailWord_1694658) baseStart_1694658 baseEnd_1694658 := by
    simpa [prefixWord, tailWord_1694658, baseEnd_1694658] using wordTrace_append hprefix tailTrace_1694658
  have hstable : (prefixWord ++ tailWord_1694658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694658).length < 2 ^ (prefixWord ++ tailWord_1694658).sum := by decide
  have hdescent : baseEnd_1694658 < baseStart_1694658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694664 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_1694664 : Nat := 118140960795 + 1694664 * 2 ^ 59
def prefixEnd_1694664 : Nat := 4983230072969 + 3 ^ 40 * 1694664 * 2
def baseEnd_1694664 : Nat := 193372706638013967334753

theorem tailTrace_1694664 : CollatzResearch.WordTrace tailWord_1694664 prefixEnd_1694664 193372706638013967334753 := by
  unfold tailWord_1694664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904736966264614206981523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41206315955019485609308697 30904736966264614206981523)
  ·
    refine ⟨46357105449396921310472285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30904736966264614206981523 46357105449396921310472285)
    ·
      refine ⟨17383914543523845491427107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46357105449396921310472285 17383914543523845491427107)
      ·
        refine ⟨26075871815285768237140661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383914543523845491427107 26075871815285768237140661)
        ·
          refine ⟨2444612982683040772231937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26075871815285768237140661 2444612982683040772231937)
          ·
            refine ⟨1833459737012280579173953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444612982683040772231937 1833459737012280579173953)
            ·
              refine ⟨1375094802759210434380465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833459737012280579173953 1375094802759210434380465)
              ·
                refine ⟨1031321102069407825785349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375094802759210434380465 1031321102069407825785349)
                ·
                  refine ⟨193372706638013967334753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031321102069407825785349 193372706638013967334753)
                  ·
                    rfl

theorem cell22_1694664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_1694664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694664 prefixEnd_1694664 := by exact prefixLift 1694664
  have htrace : WordTrace (prefixWord ++ tailWord_1694664) baseStart_1694664 baseEnd_1694664 := by
    simpa [prefixWord, tailWord_1694664, baseEnd_1694664] using wordTrace_append hprefix tailTrace_1694664
  have hstable : (prefixWord ++ tailWord_1694664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694664).length < 2 ^ (prefixWord ++ tailWord_1694664).sum := by decide
  have hdescent : baseEnd_1694664 < baseStart_1694664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694763 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_1694763 : Nat := 118140960795 + 1694763 * 2 ^ 59
def prefixEnd_1694763 : Nat := 4983230072969 + 3 ^ 40 * 1694763 * 2
def baseEnd_1694763 : Nat := 580152009637238643778955

theorem tailTrace_1694763 : CollatzResearch.WordTrace tailWord_1694763 prefixEnd_1694763 580152009637238643778955 := by
  unfold tailWord_1694763
  simp only [CollatzResearch.WordTrace]
  refine ⟨61813084759170568321816943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41208723172780378881211295 61813084759170568321816943)
  ·
    refine ⟨92719627138755852482725415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61813084759170568321816943 92719627138755852482725415)
    ·
      refine ⟨139079440708133778724088123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92719627138755852482725415 139079440708133778724088123)
      ·
        refine ⟨208619161062200668086132185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139079440708133778724088123 208619161062200668086132185)
        ·
          refine ⟨156464370796650501064599139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208619161062200668086132185 156464370796650501064599139)
          ·
            refine ⟨234696556194975751596898709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156464370796650501064599139 234696556194975751596898709)
            ·
              refine ⟨11001401071639488356104627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234696556194975751596898709 11001401071639488356104627)
              ·
                refine ⟨16502101607459232534156941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001401071639488356104627 16502101607459232534156941)
                ·
                  refine ⟨6188288102797212200308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16502101607459232534156941 6188288102797212200308853)
                  ·
                    refine ⟨580152009637238643778955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188288102797212200308853 580152009637238643778955)
                    ·
                      rfl

theorem cell22_1694763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_1694763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694763 prefixEnd_1694763 := by exact prefixLift 1694763
  have htrace : WordTrace (prefixWord ++ tailWord_1694763) baseStart_1694763 baseEnd_1694763 := by
    simpa [prefixWord, tailWord_1694763, baseEnd_1694763] using wordTrace_append hprefix tailTrace_1694763
  have hstable : (prefixWord ++ tailWord_1694763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694763).length < 2 ^ (prefixWord ++ tailWord_1694763).sum := by decide
  have hdescent : baseEnd_1694763 < baseStart_1694763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694782 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1694782 : Nat := 118140960795 + 1694782 * 2 ^ 59
def prefixEnd_1694782 : Nat := 4983230072969 + 3 ^ 40 * 1694782 * 2
def baseEnd_1694782 : Nat := 193386171241842975851299

theorem tailTrace_1694782 : CollatzResearch.WordTrace tailWord_1694782 prefixEnd_1694782 193386171241842975851299 := by
  unfold tailWord_1694782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726722218262716820844825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41209185164067823044505733 7726722218262716820844825)
  ·
    refine ⟨5795041663697037615633619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7726722218262716820844825 5795041663697037615633619)
    ·
      refine ⟨8692562495545556423450429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795041663697037615633619 8692562495545556423450429)
      ·
        refine ⟨3259710935829583658793911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8692562495545556423450429 3259710935829583658793911)
        ·
          refine ⟨4889566403744375488190867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259710935829583658793911 4889566403744375488190867)
          ·
            refine ⟨7334349605616563232286301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889566403744375488190867 7334349605616563232286301)
            ·
              refine ⟨2750381102106211212107363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7334349605616563232286301 2750381102106211212107363)
              ·
                refine ⟨4125571653159316818161045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750381102106211212107363 4125571653159316818161045)
                ·
                  refine ⟨193386171241842975851299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4125571653159316818161045 193386171241842975851299)
                  ·
                    rfl

theorem cell22_1694782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1694782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694782 prefixEnd_1694782 := by exact prefixLift 1694782
  have htrace : WordTrace (prefixWord ++ tailWord_1694782) baseStart_1694782 baseEnd_1694782 := by
    simpa [prefixWord, tailWord_1694782, baseEnd_1694782] using wordTrace_append hprefix tailTrace_1694782
  have hstable : (prefixWord ++ tailWord_1694782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694782).length < 2 ^ (prefixWord ++ tailWord_1694782).sum := by decide
  have hdescent : baseEnd_1694782 < baseStart_1694782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694812 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1694812 : Nat := 118140960795 + 1694812 * 2 ^ 59
def prefixEnd_1694812 : Nat := 4983230072969 + 3 ^ 40 * 1694812 * 2
def baseEnd_1694812 : Nat := 580168783338618849303805

theorem tailTrace_1694812 : CollatzResearch.WordTrace tailWord_1694812 prefixEnd_1694812 580168783338618849303805 := by
  unfold tailWord_1694812
  simp only [CollatzResearch.WordTrace]
  refine ⟨30907435967996524845175345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41209914623995366460233793 30907435967996524845175345)
  ·
    refine ⟨23180576975997393633881509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30907435967996524845175345 23180576975997393633881509)
    ·
      refine ⟨4346358182999511306352783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23180576975997393633881509 4346358182999511306352783)
      ·
        refine ⟨6519537274499266959529175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346358182999511306352783 6519537274499266959529175)
        ·
          refine ⟨9779305911748900439293763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519537274499266959529175 9779305911748900439293763)
          ·
            refine ⟨14668958867623350658940645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9779305911748900439293763 14668958867623350658940645)
            ·
              refine ⟨2750429787679378248551371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14668958867623350658940645 2750429787679378248551371)
              ·
                refine ⟨4125644681519067372827057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750429787679378248551371 4125644681519067372827057)
                ·
                  refine ⟨3094233511139300529620293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125644681519067372827057 3094233511139300529620293)
                  ·
                    refine ⟨580168783338618849303805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094233511139300529620293 580168783338618849303805)
                    ·
                      rfl

theorem cell22_1694812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1694812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694812 prefixEnd_1694812 := by exact prefixLift 1694812
  have htrace : WordTrace (prefixWord ++ tailWord_1694812) baseStart_1694812 baseEnd_1694812 := by
    simpa [prefixWord, tailWord_1694812, baseEnd_1694812] using wordTrace_append hprefix tailTrace_1694812
  have hstable : (prefixWord ++ tailWord_1694812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694812).length < 2 ^ (prefixWord ++ tailWord_1694812).sum := by decide
  have hdescent : baseEnd_1694812 < baseStart_1694812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694814 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1694814 : Nat := 118140960795 + 1694814 * 2 ^ 59
def prefixEnd_1694814 : Nat := 4983230072969 + 3 ^ 40 * 1694814 * 2
def baseEnd_1694814 : Nat := 580169467979491510753799

theorem tailTrace_1694814 : CollatzResearch.WordTrace tailWord_1694814 prefixEnd_1694814 580169467979491510753799 := by
  unfold tailWord_1694814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726868110248225503990437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41209963254657202687948997 7726868110248225503990437)
  ·
    refine ⟨1448787770671542281998207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7726868110248225503990437 1448787770671542281998207)
    ·
      refine ⟨2173181656007313422997311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448787770671542281998207 2173181656007313422997311)
      ·
        refine ⟨3259772484010970134495967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173181656007313422997311 3259772484010970134495967)
        ·
          refine ⟨4889658726016455201743951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259772484010970134495967 4889658726016455201743951)
          ·
            refine ⟨7334488089024682802615927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889658726016455201743951 7334488089024682802615927)
            ·
              refine ⟨11001732133537024203923891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334488089024682802615927 11001732133537024203923891)
              ·
                refine ⟨16502598200305536305885837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001732133537024203923891 16502598200305536305885837)
                ·
                  refine ⟨6188474325114576114707189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16502598200305536305885837 6188474325114576114707189)
                  ·
                    refine ⟨580169467979491510753799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188474325114576114707189 580169467979491510753799)
                    ·
                      rfl

theorem cell22_1694814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1694814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694814 prefixEnd_1694814 := by exact prefixLift 1694814
  have htrace : WordTrace (prefixWord ++ tailWord_1694814) baseStart_1694814 baseEnd_1694814 := by
    simpa [prefixWord, tailWord_1694814, baseEnd_1694814] using wordTrace_append hprefix tailTrace_1694814
  have hstable : (prefixWord ++ tailWord_1694814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694814).length < 2 ^ (prefixWord ++ tailWord_1694814).sum := by decide
  have hdescent : baseEnd_1694814 < baseStart_1694814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694876 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1694876 : Nat := 118140960795 + 1694876 * 2 ^ 59
def prefixEnd_1694876 : Nat := 4983230072969 + 3 ^ 40 * 1694876 * 2
def baseEnd_1694876 : Nat := 580190691846544015703609

theorem tailTrace_1694876 : CollatzResearch.WordTrace tailWord_1694876 prefixEnd_1694876 580190691846544015703609 := by
  unfold tailWord_1694876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908603103880594310340241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41211470805174125747120321 30908603103880594310340241)
  ·
    refine ⟨23181452327910445732755181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30908603103880594310340241 23181452327910445732755181)
    ·
      refine ⟨8693044622966417149783193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23181452327910445732755181 8693044622966417149783193)
      ·
        refine ⟨6519783467224812862337395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693044622966417149783193 6519783467224812862337395)
        ·
          refine ⟨9779675200837219293506093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519783467224812862337395 9779675200837219293506093)
          ·
            refine ⟨3667378200313957235064785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9779675200837219293506093 3667378200313957235064785)
            ·
              refine ⟨2750533650235467926298589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667378200313957235064785 2750533650235467926298589)
              ·
                refine ⟨1031450118838300472361971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2750533650235467926298589 1031450118838300472361971)
                ·
                  refine ⟨1547175178257450708542957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031450118838300472361971 1547175178257450708542957)
                  ·
                    refine ⟨580190691846544015703609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547175178257450708542957 580190691846544015703609)
                    ·
                      rfl

theorem cell22_1694876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1694876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694876 prefixEnd_1694876 := by exact prefixLift 1694876
  have htrace : WordTrace (prefixWord ++ tailWord_1694876) baseStart_1694876 baseEnd_1694876 := by
    simpa [prefixWord, tailWord_1694876, baseEnd_1694876] using wordTrace_append hprefix tailTrace_1694876
  have hstable : (prefixWord ++ tailWord_1694876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694876).length < 2 ^ (prefixWord ++ tailWord_1694876).sum := by decide
  have hdescent : baseEnd_1694876 < baseStart_1694876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694887 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1694887 : Nat := 118140960795 + 1694887 * 2 ^ 59
def prefixEnd_1694887 : Nat := 4983230072969 + 3 ^ 40 * 1694887 * 2
def baseEnd_1694887 : Nat := 580194457371343653678575

theorem tailTrace_1694887 : CollatzResearch.WordTrace tailWord_1694887 prefixEnd_1694887 580194457371343653678575 := by
  unfold tailWord_1694887
  simp only [CollatzResearch.WordTrace]
  refine ⟨61817607410721337499330915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41211738273814224999553943 61817607410721337499330915)
  ·
    refine ⟨92726411116082006248996373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61817607410721337499330915 92726411116082006248996373)
    ·
      refine ⟨4346550521066344042921705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92726411116082006248996373 4346550521066344042921705)
      ·
        refine ⟨3259912890799758032191279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4346550521066344042921705 3259912890799758032191279)
        ·
          refine ⟨4889869336199637048286919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259912890799758032191279 4889869336199637048286919)
          ·
            refine ⟨7334804004299455572430379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889869336199637048286919 7334804004299455572430379)
            ·
              refine ⟨11002206006449183358645569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334804004299455572430379 11002206006449183358645569)
              ·
                refine ⟨8251654504836887518984177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11002206006449183358645569 8251654504836887518984177)
                ·
                  refine ⟨6188740878627665639238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8251654504836887518984177 6188740878627665639238133)
                  ·
                    refine ⟨580194457371343653678575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188740878627665639238133 580194457371343653678575)
                    ·
                      rfl

theorem cell22_1694887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1694887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694887 prefixEnd_1694887 := by exact prefixLift 1694887
  have htrace : WordTrace (prefixWord ++ tailWord_1694887) baseStart_1694887 baseEnd_1694887 := by
    simpa [prefixWord, tailWord_1694887, baseEnd_1694887] using wordTrace_append hprefix tailTrace_1694887
  have hstable : (prefixWord ++ tailWord_1694887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694887).length < 2 ^ (prefixWord ++ tailWord_1694887).sum := by decide
  have hdescent : baseEnd_1694887 < baseStart_1694887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694915 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_1694915 : Nat := 118140960795 + 1694915 * 2 ^ 59
def prefixEnd_1694915 : Nat := 4983230072969 + 3 ^ 40 * 1694915 * 2
def baseEnd_1694915 : Nat := 580204042343560913978489

theorem tailTrace_1694915 : CollatzResearch.WordTrace tailWord_1694915 prefixEnd_1694915 580204042343560913978489 := by
  unfold tailWord_1694915
  simp only [CollatzResearch.WordTrace]
  refine ⟨61818628654619898281350199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41212419103079932187566799 61818628654619898281350199)
  ·
    refine ⟨92727942981929847422025299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61818628654619898281350199 92727942981929847422025299)
    ·
      refine ⟨139091914472894771133037949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92727942981929847422025299 139091914472894771133037949)
      ·
        refine ⟨52159467927335539174889231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139091914472894771133037949 52159467927335539174889231)
        ·
          refine ⟨78239201891003308762333847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52159467927335539174889231 78239201891003308762333847)
          ·
            refine ⟨117358802836504963143500771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78239201891003308762333847 117358802836504963143500771)
            ·
              refine ⟨176038204254757444715251157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117358802836504963143500771 176038204254757444715251157)
              ·
                refine ⟨4125895412220877610513699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176038204254757444715251157 4125895412220877610513699)
                ·
                  refine ⟨6188843118331316415770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125895412220877610513699 6188843118331316415770549)
                  ·
                    refine ⟨580204042343560913978489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188843118331316415770549 580204042343560913978489)
                    ·
                      rfl

theorem cell22_1694915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_1694915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694915 prefixEnd_1694915 := by exact prefixLift 1694915
  have htrace : WordTrace (prefixWord ++ tailWord_1694915) baseStart_1694915 baseEnd_1694915 := by
    simpa [prefixWord, tailWord_1694915, baseEnd_1694915] using wordTrace_append hprefix tailTrace_1694915
  have hstable : (prefixWord ++ tailWord_1694915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694915).length < 2 ^ (prefixWord ++ tailWord_1694915).sum := by decide
  have hdescent : baseEnd_1694915 < baseStart_1694915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694945 : List Nat := [1, 2, 3, 1, 3, 2, 10]
def baseStart_1694945 : Nat := 118140960795 + 1694945 * 2 ^ 59
def prefixEnd_1694945 : Nat := 4983230072969 + 3 ^ 40 * 1694945 * 2
def baseEnd_1694945 : Nat := 21489418961357438360311

theorem tailTrace_1694945 : CollatzResearch.WordTrace tailWord_1694945 prefixEnd_1694945 21489418961357438360311 := by
  unfold tailWord_1694945
  simp only [CollatzResearch.WordTrace]
  refine ⟨61819722844511213404942289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41213148563007475603294859 61819722844511213404942289)
  ·
    refine ⟨46364792133383410053706717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61819722844511213404942289 46364792133383410053706717)
    ·
      refine ⟨17386797050018778770140019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46364792133383410053706717 17386797050018778770140019)
      ·
        refine ⟨26080195575028168155210029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17386797050018778770140019 26080195575028168155210029)
        ·
          refine ⟨9780073340635563058203761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26080195575028168155210029 9780073340635563058203761)
          ·
            refine ⟨7335055005476672293652821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9780073340635563058203761 7335055005476672293652821)
            ·
              refine ⟨21489418961357438360311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7335055005476672293652821 21489418961357438360311)
              ·
                rfl

theorem cell22_1694945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 10].length) (baseStart_1694945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694945 prefixEnd_1694945 := by exact prefixLift 1694945
  have htrace : WordTrace (prefixWord ++ tailWord_1694945) baseStart_1694945 baseEnd_1694945 := by
    simpa [prefixWord, tailWord_1694945, baseEnd_1694945] using wordTrace_append hprefix tailTrace_1694945
  have hstable : (prefixWord ++ tailWord_1694945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694945).length < 2 ^ (prefixWord ++ tailWord_1694945).sum := by decide
  have hdescent : baseEnd_1694945 < baseStart_1694945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694951 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 6]
def baseStart_1694951 : Nat := 118140960795 + 1694951 * 2 ^ 59
def prefixEnd_1694951 : Nat := 4983230072969 + 3 ^ 40 * 1694951 * 2
def baseEnd_1694951 : Nat := 193405455293089606692793

theorem tailTrace_1694951 : CollatzResearch.WordTrace tailWord_1694951 prefixEnd_1694951 193405455293089606692793 := by
  unfold tailWord_1694951
  simp only [CollatzResearch.WordTrace]
  refine ⟨61819941682489476429660707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41213294454992984286440471 61819941682489476429660707)
  ·
    refine ⟨92729912523734214644491061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61819941682489476429660707 92729912523734214644491061)
    ·
      refine ⟨8693429299100082622921037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92729912523734214644491061 8693429299100082622921037)
      ·
        refine ⟨3260035987162530983595389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8693429299100082622921037 3260035987162530983595389)
        ·
          refine ⟨1222513495185949118848271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3260035987162530983595389 1222513495185949118848271)
          ·
            refine ⟨1833770242778923678272407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222513495185949118848271 1833770242778923678272407)
            ·
              refine ⟨2750655364168385517408611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833770242778923678272407 2750655364168385517408611)
              ·
                refine ⟨4125983046252578276112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750655364168385517408611 4125983046252578276112917)
                ·
                  refine ⟨193405455293089606692793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4125983046252578276112917 193405455293089606692793)
                  ·
                    rfl

theorem cell22_1694951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 6].length) (baseStart_1694951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1694951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1694951 prefixEnd_1694951 := by exact prefixLift 1694951
  have htrace : WordTrace (prefixWord ++ tailWord_1694951) baseStart_1694951 baseEnd_1694951 := by
    simpa [prefixWord, tailWord_1694951, baseEnd_1694951] using wordTrace_append hprefix tailTrace_1694951
  have hstable : (prefixWord ++ tailWord_1694951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694951).length < 2 ^ (prefixWord ++ tailWord_1694951).sum := by decide
  have hdescent : baseEnd_1694951 < baseStart_1694951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695011 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 1, 3]
def baseStart_1695011 : Nat := 118140960795 + 1695011 * 2 ^ 59
def prefixEnd_1695011 : Nat := 4983230072969 + 3 ^ 40 * 1695011 * 2
def baseEnd_1695011 : Nat := 580236905105448663578195

theorem tailTrace_1695011 : CollatzResearch.WordTrace tailWord_1695011 prefixEnd_1695011 580236905105448663578195 := by
  unfold tailWord_1695011
  simp only [CollatzResearch.WordTrace]
  refine ⟨61822130062272106676844887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41214753374848071117896591 61822130062272106676844887)
  ·
    refine ⟨92733195093408160015267331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61822130062272106676844887 92733195093408160015267331)
    ·
      refine ⟨139099792640112240022900997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92733195093408160015267331 139099792640112240022900997)
      ·
        refine ⟨26081211120021045004293937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139099792640112240022900997 26081211120021045004293937)
        ·
          refine ⟨19560908340015783753220453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26081211120021045004293937 19560908340015783753220453)
          ·
            refine ⟨3667670313752959453728835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19560908340015783753220453 3667670313752959453728835)
            ·
              refine ⟨5501505470629439180593253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667670313752959453728835 5501505470629439180593253)
              ·
                refine ⟨1031532275743019846361235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5501505470629439180593253 1031532275743019846361235)
                ·
                  refine ⟨1547298413614529769541853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031532275743019846361235 1547298413614529769541853)
                  ·
                    refine ⟨580236905105448663578195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547298413614529769541853 580236905105448663578195)
                    ·
                      rfl

theorem cell22_1695011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 3].length) (baseStart_1695011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695011 prefixEnd_1695011 := by exact prefixLift 1695011
  have htrace : WordTrace (prefixWord ++ tailWord_1695011) baseStart_1695011 baseEnd_1695011 := by
    simpa [prefixWord, tailWord_1695011, baseEnd_1695011] using wordTrace_append hprefix tailTrace_1695011
  have hstable : (prefixWord ++ tailWord_1695011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695011).length < 2 ^ (prefixWord ++ tailWord_1695011).sum := by decide
  have hdescent : baseEnd_1695011 < baseStart_1695011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695054 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1695054 : Nat := 118140960795 + 1695054 * 2 ^ 59
def prefixEnd_1695054 : Nat := 4983230072969 + 3 ^ 40 * 1695054 * 2
def baseEnd_1695054 : Nat := 580251624884210884753063

theorem tailTrace_1695054 : CollatzResearch.WordTrace tailWord_1695054 prefixEnd_1695054 580251624884210884753063 := by
  unfold tailWord_1695054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727962300139540627582527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41215798934077550013773477 7727962300139540627582527)
  ·
    refine ⟨11591943450209310941373791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727962300139540627582527 11591943450209310941373791)
    ·
      refine ⟨17387915175313966412060687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11591943450209310941373791 17387915175313966412060687)
      ·
        refine ⟨26081872762970949618091031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17387915175313966412060687 26081872762970949618091031)
        ·
          refine ⟨39122809144456424427136547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26081872762970949618091031 39122809144456424427136547)
          ·
            refine ⟨58684213716684636640704821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39122809144456424427136547 58684213716684636640704821)
            ·
              refine ⟨5501645035939184685066077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58684213716684636640704821 5501645035939184685066077)
              ·
                refine ⟨2063116888477194256899779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5501645035939184685066077 2063116888477194256899779)
                ·
                  refine ⟨3094675332715791385349669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063116888477194256899779 3094675332715791385349669)
                  ·
                    refine ⟨580251624884210884753063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094675332715791385349669 580251624884210884753063)
                    ·
                      rfl

theorem cell22_1695054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1695054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695054 prefixEnd_1695054 := by exact prefixLift 1695054
  have htrace : WordTrace (prefixWord ++ tailWord_1695054) baseStart_1695054 baseEnd_1695054 := by
    simpa [prefixWord, tailWord_1695054, baseEnd_1695054] using wordTrace_append hprefix tailTrace_1695054
  have hstable : (prefixWord ++ tailWord_1695054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695054).length < 2 ^ (prefixWord ++ tailWord_1695054).sum := by decide
  have hdescent : baseEnd_1695054 < baseStart_1695054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695062 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1695062 : Nat := 118140960795 + 1695062 * 2 ^ 59
def prefixEnd_1695062 : Nat := 4983230072969 + 3 ^ 40 * 1695062 * 2
def baseEnd_1695062 : Nat := 580254363447701530553039

theorem tailTrace_1695062 : CollatzResearch.WordTrace tailWord_1695062 prefixEnd_1695062 580254363447701530553039 := by
  unfold tailWord_1695062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863999386567958899184465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41215993456724894924634293 3863999386567958899184465)
  ·
    refine ⟨2897999539925969174388349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3863999386567958899184465 2897999539925969174388349)
    ·
      refine ⟨1086749827472238440395631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2897999539925969174388349 1086749827472238440395631)
      ·
        refine ⟨1630124741208357660593447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086749827472238440395631 1630124741208357660593447)
        ·
          refine ⟨2445187111812536490890171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630124741208357660593447 2445187111812536490890171)
          ·
            refine ⟨3667780667718804736335257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445187111812536490890171 3667780667718804736335257)
            ·
              refine ⟨2750835500789103552251443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667780667718804736335257 2750835500789103552251443)
              ·
                refine ⟨4126253251183655328377165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750835500789103552251443 4126253251183655328377165)
                ·
                  refine ⟨1547344969193870748141437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4126253251183655328377165 1547344969193870748141437)
                  ·
                    refine ⟨580254363447701530553039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547344969193870748141437 580254363447701530553039)
                    ·
                      rfl

theorem cell22_1695062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1695062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695062 prefixEnd_1695062 := by exact prefixLift 1695062
  have htrace : WordTrace (prefixWord ++ tailWord_1695062) baseStart_1695062 baseEnd_1695062 := by
    simpa [prefixWord, tailWord_1695062, baseEnd_1695062] using wordTrace_append hprefix tailTrace_1695062
  have hstable : (prefixWord ++ tailWord_1695062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695062).length < 2 ^ (prefixWord ++ tailWord_1695062).sum := by decide
  have hdescent : baseEnd_1695062 < baseStart_1695062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695084 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1695084 : Nat := 118140960795 + 1695084 * 2 ^ 59
def prefixEnd_1695084 : Nat := 4983230072969 + 3 ^ 40 * 1695084 * 2
def baseEnd_1695084 : Nat := 580261894497300806502971

theorem tailTrace_1695084 : CollatzResearch.WordTrace tailWord_1695084 prefixEnd_1695084 580261894497300806502971 := by
  unfold tailWord_1695084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30912396295503820072126153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41216528394005093429501537 30912396295503820072126153)
  ·
    refine ⟨23184297221627865054094615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30912396295503820072126153 23184297221627865054094615)
    ·
      refine ⟨34776445832441797581141923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23184297221627865054094615 34776445832441797581141923)
      ·
        refine ⟨52164668748662696371712885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34776445832441797581141923 52164668748662696371712885)
        ·
          refine ⟨4890437695187127784848083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52164668748662696371712885 4890437695187127784848083)
          ·
            refine ⟨7335656542780691677272125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890437695187127784848083 7335656542780691677272125)
            ·
              refine ⟨2750871203542759378977047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7335656542780691677272125 2750871203542759378977047)
              ·
                refine ⟨4126306805314139068465571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750871203542759378977047 4126306805314139068465571)
                ·
                  refine ⟨6189460207971208602698357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126306805314139068465571 6189460207971208602698357)
                  ·
                    refine ⟨580261894497300806502971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6189460207971208602698357 580261894497300806502971)
                    ·
                      rfl

theorem cell22_1695084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1695084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695084 prefixEnd_1695084 := by exact prefixLift 1695084
  have htrace : WordTrace (prefixWord ++ tailWord_1695084) baseStart_1695084 baseEnd_1695084 := by
    simpa [prefixWord, tailWord_1695084, baseEnd_1695084] using wordTrace_append hprefix tailTrace_1695084
  have hstable : (prefixWord ++ tailWord_1695084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695084).length < 2 ^ (prefixWord ++ tailWord_1695084).sum := by decide
  have hdescent : baseEnd_1695084 < baseStart_1695084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695127 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1695127 : Nat := 118140960795 + 1695127 * 2 ^ 59
def prefixEnd_1695127 : Nat := 4983230072969 + 3 ^ 40 * 1695127 * 2
def baseEnd_1695127 : Nat := 580276614276063027677839

theorem tailTrace_1695127 : CollatzResearch.WordTrace tailWord_1695127 prefixEnd_1695127 580276614276063027677839 := by
  unfold tailWord_1695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨61826360929851858488067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41217573953234572325378423 61826360929851858488067635)
  ·
    refine ⟨92739541394777787732101453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61826360929851858488067635 92739541394777787732101453)
    ·
      refine ⟨34777328023041670399538045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92739541394777787732101453 34777328023041670399538045)
      ·
        refine ⟨13041498008640626399826767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34777328023041670399538045 13041498008640626399826767)
        ·
          refine ⟨19562247012960939599740151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13041498008640626399826767 19562247012960939599740151)
          ·
            refine ⟨29343370519441409399610227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19562247012960939599740151 29343370519441409399610227)
            ·
              refine ⟨44015055779162114099415341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29343370519441409399610227 44015055779162114099415341)
              ·
                refine ⟨16505645917185792787280753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44015055779162114099415341 16505645917185792787280753)
                ·
                  refine ⟨12379234437889344590460565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16505645917185792787280753 12379234437889344590460565)
                  ·
                    refine ⟨580276614276063027677839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12379234437889344590460565 580276614276063027677839)
                    ·
                      rfl

theorem cell22_1695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1695127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695127 prefixEnd_1695127 := by exact prefixLift 1695127
  have htrace : WordTrace (prefixWord ++ tailWord_1695127) baseStart_1695127 baseEnd_1695127 := by
    simpa [prefixWord, tailWord_1695127, baseEnd_1695127] using wordTrace_append hprefix tailTrace_1695127
  have hstable : (prefixWord ++ tailWord_1695127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695127).length < 2 ^ (prefixWord ++ tailWord_1695127).sum := by decide
  have hdescent : baseEnd_1695127 < baseStart_1695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695180 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_1695180 : Nat := 118140960795 + 1695180 * 2 ^ 59
def prefixEnd_1695180 : Nat := 4983230072969 + 3 ^ 40 * 1695180 * 2
def baseEnd_1695180 : Nat := 580294757259188556102677

theorem tailTrace_1695180 : CollatzResearch.WordTrace tailWord_1695180 prefixEnd_1695180 580294757259188556102677 := by
  unfold tailWord_1695180
  simp only [CollatzResearch.WordTrace]
  refine ⟨30914146999329924269873497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41218862665773232359831329 30914146999329924269873497)
  ·
    refine ⟨23185610249497443202405123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30914146999329924269873497 23185610249497443202405123)
    ·
      refine ⟨34778415374246164803607685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23185610249497443202405123 34778415374246164803607685)
      ·
        refine ⟨6520952882671155900676441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34778415374246164803607685 6520952882671155900676441)
        ·
          refine ⟨4890714662003366925507331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6520952882671155900676441 4890714662003366925507331)
          ·
            refine ⟨7336071993005050388260997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890714662003366925507331 7336071993005050388260997)
            ·
              refine ⟨1375513498688446947798937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7336071993005050388260997 1375513498688446947798937)
              ·
                refine ⟨1031635124016335210849203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375513498688446947798937 1031635124016335210849203)
                ·
                  refine ⟨1547452686024502816273805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031635124016335210849203 1547452686024502816273805)
                  ·
                    refine ⟨580294757259188556102677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547452686024502816273805 580294757259188556102677)
                    ·
                      rfl

theorem cell22_1695180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_1695180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695180 prefixEnd_1695180 := by exact prefixLift 1695180
  have htrace : WordTrace (prefixWord ++ tailWord_1695180) baseStart_1695180 baseEnd_1695180 := by
    simpa [prefixWord, tailWord_1695180, baseEnd_1695180] using wordTrace_append hprefix tailTrace_1695180
  have hstable : (prefixWord ++ tailWord_1695180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695180).length < 2 ^ (prefixWord ++ tailWord_1695180).sum := by decide
  have hdescent : baseEnd_1695180 < baseStart_1695180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695189 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1695189 : Nat := 118140960795 + 1695189 * 2 ^ 59
def prefixEnd_1695189 : Nat := 4983230072969 + 3 ^ 40 * 1695189 * 2
def baseEnd_1695189 : Nat := 580297838143115532627649

theorem tailTrace_1695189 : CollatzResearch.WordTrace tailWord_1695189 prefixEnd_1695189 580297838143115532627649 := by
  unfold tailWord_1695189
  simp only [CollatzResearch.WordTrace]
  refine ⟨61828622255627243076824621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41219081503751495384549747 61828622255627243076824621)
  ·
    refine ⟨23185733345860216153809233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61828622255627243076824621 23185733345860216153809233)
    ·
      refine ⟨17389300009395162115356925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23185733345860216153809233 17389300009395162115356925)
      ·
        refine ⟨6520987503523185793258847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17389300009395162115356925 6520987503523185793258847)
        ·
          refine ⟨9781481255284778689888271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520987503523185793258847 9781481255284778689888271)
          ·
            refine ⟨14672221882927168034832407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781481255284778689888271 14672221882927168034832407)
            ·
              refine ⟨22008332824390752052248611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14672221882927168034832407 22008332824390752052248611)
              ·
                refine ⟨33012499236586128078372917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22008332824390752052248611 33012499236586128078372917)
                ·
                  refine ⟨3094921803429949507347461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33012499236586128078372917 3094921803429949507347461)
                  ·
                    refine ⟨580297838143115532627649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094921803429949507347461 580297838143115532627649)
                    ·
                      rfl

theorem cell22_1695189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1695189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695189 prefixEnd_1695189 := by exact prefixLift 1695189
  have htrace : WordTrace (prefixWord ++ tailWord_1695189) baseStart_1695189 baseEnd_1695189 := by
    simpa [prefixWord, tailWord_1695189, baseEnd_1695189] using wordTrace_append hprefix tailTrace_1695189
  have hstable : (prefixWord ++ tailWord_1695189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695189).length < 2 ^ (prefixWord ++ tailWord_1695189).sum := by decide
  have hdescent : baseEnd_1695189 < baseStart_1695189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695266 : List Nat := [3, 3, 1, 1, 1, 1, 6, 6]
def baseStart_1695266 : Nat := 118140960795 + 1695266 * 2 ^ 59
def prefixEnd_1695266 : Nat := 4983230072969 + 3 ^ 40 * 1695266 * 2
def baseEnd_1695266 : Nat := 64480466312968110939157

theorem tailTrace_1695266 : CollatzResearch.WordTrace tailWord_1695266 prefixEnd_1695266 64480466312968110939157 := by
  unfold tailWord_1695266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457857669087071306844413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41220953784232190151585101 15457857669087071306844413)
  ·
    refine ⟨5796696625907651740066655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15457857669087071306844413 5796696625907651740066655)
    ·
      refine ⟨8695044938861477610099983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796696625907651740066655 8695044938861477610099983)
      ·
        refine ⟨13042567408292216415149975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695044938861477610099983 13042567408292216415149975)
        ·
          refine ⟨19563851112438324622724963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042567408292216415149975 19563851112438324622724963)
          ·
            refine ⟨29345776668657486934087445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19563851112438324622724963 29345776668657486934087445)
            ·
              refine ⟨1375583281343319700035349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29345776668657486934087445 1375583281343319700035349)
              ·
                refine ⟨64480466312968110939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1375583281343319700035349 64480466312968110939157)
                ·
                  rfl

theorem cell22_1695266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_1695266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695266 prefixEnd_1695266 := by exact prefixLift 1695266
  have htrace : WordTrace (prefixWord ++ tailWord_1695266) baseStart_1695266 baseEnd_1695266 := by
    simpa [prefixWord, tailWord_1695266, baseEnd_1695266] using wordTrace_append hprefix tailTrace_1695266
  have hstable : (prefixWord ++ tailWord_1695266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695266).length < 2 ^ (prefixWord ++ tailWord_1695266).sum := by decide
  have hdescent : baseEnd_1695266 < baseStart_1695266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695272 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_1695272 : Nat := 118140960795 + 1695272 * 2 ^ 59
def prefixEnd_1695272 : Nat := 4983230072969 + 3 ^ 40 * 1695272 * 2
def baseEnd_1695272 : Nat := 193442083579776994267465

theorem tailTrace_1695272 : CollatzResearch.WordTrace tailWord_1695272 prefixEnd_1695272 193442083579776994267465 := by
  unfold tailWord_1695272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30915824757163274126048035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41221099676217698834730713 30915824757163274126048035)
  ·
    refine ⟨46373737135744911189072053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30915824757163274126048035 46373737135744911189072053)
    ·
      refine ⟨4347537856476085423975505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46373737135744911189072053 4347537856476085423975505)
      ·
        refine ⟨3260653392357064067981629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4347537856476085423975505 3260653392357064067981629)
        ·
          refine ⟨1222745022133899025493111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3260653392357064067981629 1222745022133899025493111)
          ·
            refine ⟨1834117533200848538239667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222745022133899025493111 1834117533200848538239667)
            ·
              refine ⟨2751176299801272807359501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834117533200848538239667 2751176299801272807359501)
              ·
                refine ⟨1031691112425477302759813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2751176299801272807359501 1031691112425477302759813)
                ·
                  refine ⟨193442083579776994267465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031691112425477302759813 193442083579776994267465)
                  ·
                    rfl

theorem cell22_1695272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_1695272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695272 prefixEnd_1695272 := by exact prefixLift 1695272
  have htrace : WordTrace (prefixWord ++ tailWord_1695272) baseStart_1695272 baseEnd_1695272 := by
    simpa [prefixWord, tailWord_1695272, baseEnd_1695272] using wordTrace_append hprefix tailTrace_1695272
  have hstable : (prefixWord ++ tailWord_1695272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695272).length < 2 ^ (prefixWord ++ tailWord_1695272).sum := by decide
  have hdescent : baseEnd_1695272 < baseStart_1695272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
