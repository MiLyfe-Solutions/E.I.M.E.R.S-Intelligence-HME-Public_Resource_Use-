import V185TrunkScan19Chunk024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_250115 : List Nat := [1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_250115 : Nat := 118140960795 + 250115 * 2 ^ 59
def prefixEnd_250115 : Nat := 4983230072969 + 3 ^ 40 * 250115 * 2
def baseEnd_250115 : Nat := 76106200829270611918369

theorem tailTrace_250115 : CollatzResearch.WordTrace tailWord_250115 prefixEnd_250115 76106200829270611918369 := by
  unfold tailWord_250115
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122443488883546086295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6081628992589030724197199 9122443488883546086295799)
  ·
    refine ⟨13683665233325319129443699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9122443488883546086295799 13683665233325319129443699)
    ·
      refine ⟨20525497849987978694165549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683665233325319129443699 20525497849987978694165549)
      ·
        refine ⟨7697061693745492010312081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20525497849987978694165549 7697061693745492010312081)
        ·
          refine ⟨5772796270309119007734061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697061693745492010312081 5772796270309119007734061)
          ·
            refine ⟨2164798601365919627900273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5772796270309119007734061 2164798601365919627900273)
            ·
              refine ⟨1623598951024439720925205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164798601365919627900273 1623598951024439720925205)
              ·
                refine ⟨76106200829270611918369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1623598951024439720925205 76106200829270611918369)
                ·
                  rfl

theorem cell19_250115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_250115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250115 prefixEnd_250115 := by exact prefixLift 250115
  have htrace : WordTrace (prefixWord ++ tailWord_250115) baseStart_250115 baseEnd_250115 := by
    simpa [prefixWord, tailWord_250115, baseEnd_250115] using wordTrace_append hprefix tailTrace_250115
  have hstable : (prefixWord ++ tailWord_250115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250115).length < 2 ^ (prefixWord ++ tailWord_250115).sum := by decide
  have hdescent : baseEnd_250115 < baseStart_250115 := by decide
  rcases family_descends (prefixWord ++ tailWord_250115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250149 : List Nat := [1, 3, 1, 2, 6, 1, 5]
def baseStart_250149 : Nat := 118140960795 + 250149 * 2 ^ 59
def prefixEnd_250149 : Nat := 4983230072969 + 3 ^ 40 * 250149 * 2
def baseEnd_250149 : Nat := 25372182171189535720907

theorem tailTrace_250149 : CollatzResearch.WordTrace tailWord_250149 prefixEnd_250149 25372182171189535720907 := by
  unfold tailWord_250149
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123683570760369893033501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6082455713840246595355667 9123683570760369893033501)
  ·
    refine ⟨3421381339035138709887563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9123683570760369893033501 3421381339035138709887563)
    ·
      refine ⟨5132072008552708064831345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421381339035138709887563 5132072008552708064831345)
      ·
        refine ⟨3849054006414531048623509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5132072008552708064831345 3849054006414531048623509)
        ·
          refine ⟨180424406550681142904227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3849054006414531048623509 180424406550681142904227)
          ·
            refine ⟨270636609826021714356341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180424406550681142904227 270636609826021714356341)
            ·
              refine ⟨25372182171189535720907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270636609826021714356341 25372182171189535720907)
              ·
                rfl

theorem cell19_250149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_250149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250149 prefixEnd_250149 := by exact prefixLift 250149
  have htrace : WordTrace (prefixWord ++ tailWord_250149) baseStart_250149 baseEnd_250149 := by
    simpa [prefixWord, tailWord_250149, baseEnd_250149] using wordTrace_append hprefix tailTrace_250149
  have hstable : (prefixWord ++ tailWord_250149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250149).length < 2 ^ (prefixWord ++ tailWord_250149).sum := by decide
  have hdescent : baseEnd_250149 < baseStart_250149 := by decide
  rcases family_descends (prefixWord ++ tailWord_250149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250170 : List Nat := [3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_250170 : Nat := 118140960795 + 250170 * 2 ^ 59
def prefixEnd_250170 : Nat := 4983230072969 + 3 ^ 40 * 250170 * 2
def baseEnd_250170 : Nat := 76122936495046780695997

theorem tailTrace_250170 : CollatzResearch.WordTrace tailWord_250170 prefixEnd_250170 76122936495046780695997 := by
  unfold tailWord_250170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281112375921072619886991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6082966335789526986365309 2281112375921072619886991)
  ·
    refine ⟨3421668563881608929830487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281112375921072619886991 3421668563881608929830487)
    ·
      refine ⟨5132502845822413394745731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421668563881608929830487 5132502845822413394745731)
      ·
        refine ⟨7698754268733620092118597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132502845822413394745731 7698754268733620092118597)
        ·
          refine ⟨1443516425387553767272237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7698754268733620092118597 1443516425387553767272237)
          ·
            refine ⟨541318659520332662727089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1443516425387553767272237 541318659520332662727089)
            ·
              refine ⟨405988994640249497045317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541318659520332662727089 405988994640249497045317)
              ·
                refine ⟨76122936495046780695997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405988994640249497045317 76122936495046780695997)
                ·
                  rfl

theorem cell19_250170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_250170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250170 prefixEnd_250170 := by exact prefixLift 250170
  have htrace : WordTrace (prefixWord ++ tailWord_250170) baseStart_250170 baseEnd_250170 := by
    simpa [prefixWord, tailWord_250170, baseEnd_250170] using wordTrace_append hprefix tailTrace_250170
  have hstable : (prefixWord ++ tailWord_250170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250170).length < 2 ^ (prefixWord ++ tailWord_250170).sum := by decide
  have hdescent : baseEnd_250170 < baseStart_250170 := by decide
  rcases family_descends (prefixWord ++ tailWord_250170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250208 : List Nat := [2, 1, 1, 3, 6, 6]
def baseStart_250208 : Nat := 118140960795 + 250208 * 2 ^ 59
def prefixEnd_250208 : Nat := 4983230072969 + 3 ^ 40 * 250208 * 2
def baseEnd_250208 : Nat := 8459388813185994650161

theorem tailTrace_250208 : CollatzResearch.WordTrace tailWord_250208 prefixEnd_250208 8459388813185994650161 := by
  unfold tailWord_250208
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562917738773311484715639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6083890318364415312954185 4562917738773311484715639)
  ·
    refine ⟨6844376608159967227073459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562917738773311484715639 6844376608159967227073459)
    ·
      refine ⟨10266564912239950840610189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844376608159967227073459 10266564912239950840610189)
      ·
        refine ⟨3849961842089981565228821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10266564912239950840610189 3849961842089981565228821)
        ·
          refine ⟨180466961347967885870101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3849961842089981565228821 180466961347967885870101)
          ·
            refine ⟨8459388813185994650161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180466961347967885870101 8459388813185994650161)
            ·
              rfl

theorem cell19_250208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_250208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250208 prefixEnd_250208 := by exact prefixLift 250208
  have htrace : WordTrace (prefixWord ++ tailWord_250208) baseStart_250208 baseEnd_250208 := by
    simpa [prefixWord, tailWord_250208, baseEnd_250208] using wordTrace_append hprefix tailTrace_250208
  have hstable : (prefixWord ++ tailWord_250208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250208).length < 2 ^ (prefixWord ++ tailWord_250208).sum := by decide
  have hdescent : baseEnd_250208 < baseStart_250208 := by decide
  rcases family_descends (prefixWord ++ tailWord_250208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250301 : List Nat := [1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_250301 : Nat := 118140960795 + 250301 * 2 ^ 59
def prefixEnd_250301 : Nat := 4983230072969 + 3 ^ 40 * 250301 * 2
def baseEnd_250301 : Nat := 76162797808077291784529

theorem tailTrace_250301 : CollatzResearch.WordTrace tailWord_250301 prefixEnd_250301 76162797808077291784529 := by
  unfold tailWord_250301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129227466209699852566757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6086151644139799901711171 9129227466209699852566757)
  ·
    refine ⟨1711730149914318722356267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9129227466209699852566757 1711730149914318722356267)
    ·
      refine ⟨2567595224871478083534401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711730149914318722356267 2567595224871478083534401)
      ·
        refine ⟨1925696418653608562650801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567595224871478083534401 1925696418653608562650801)
        ·
          refine ⟨1444272313990206421988101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925696418653608562650801 1444272313990206421988101)
          ·
            refine ⟨270801058873163704122769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1444272313990206421988101 270801058873163704122769)
            ·
              refine ⟨203100794154872778092077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270801058873163704122769 203100794154872778092077)
              ·
                refine ⟨76162797808077291784529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203100794154872778092077 76162797808077291784529)
                ·
                  rfl

theorem cell19_250301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_250301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250301 prefixEnd_250301 := by exact prefixLift 250301
  have htrace : WordTrace (prefixWord ++ tailWord_250301) baseStart_250301 baseEnd_250301 := by
    simpa [prefixWord, tailWord_250301, baseEnd_250301] using wordTrace_append hprefix tailTrace_250301
  have hstable : (prefixWord ++ tailWord_250301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250301).length < 2 ^ (prefixWord ++ tailWord_250301).sum := by decide
  have hdescent : baseEnd_250301 < baseStart_250301 := by decide
  rcases family_descends (prefixWord ++ tailWord_250301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250493 : List Nat := [1, 4, 1, 1, 5, 2, 5]
def baseStart_250493 : Nat := 118140960795 + 250493 * 2 ^ 59
def prefixEnd_250493 : Nat := 4983230072969 + 3 ^ 40 * 250493 * 2
def baseEnd_250493 : Nat := 25407073498625911839113

theorem tailTrace_250493 : CollatzResearch.WordTrace tailWord_250493 prefixEnd_250493 25407073498625911839113 := by
  unfold tailWord_250493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136230281514116643556133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6090820187676077762370755 9136230281514116643556133)
  ·
    refine ⟨1713043177783896870666775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9136230281514116643556133 1713043177783896870666775)
    ·
      refine ⟨2569564766675845306000163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713043177783896870666775 2569564766675845306000163)
      ·
        refine ⟨3854347150013767959000245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569564766675845306000163 3854347150013767959000245)
        ·
          refine ⟨361345045313790746156273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3854347150013767959000245 361345045313790746156273)
          ·
            refine ⟨271008783985343059617205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361345045313790746156273 271008783985343059617205)
            ·
              refine ⟨25407073498625911839113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271008783985343059617205 25407073498625911839113)
              ·
                rfl

theorem cell19_250493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_250493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250493 prefixEnd_250493 := by exact prefixLift 250493
  have htrace : WordTrace (prefixWord ++ tailWord_250493) baseStart_250493 baseEnd_250493 := by
    simpa [prefixWord, tailWord_250493, baseEnd_250493] using wordTrace_append hprefix tailTrace_250493
  have hstable : (prefixWord ++ tailWord_250493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250493).length < 2 ^ (prefixWord ++ tailWord_250493).sum := by decide
  have hdescent : baseEnd_250493 < baseStart_250493 := by decide
  rcases family_descends (prefixWord ++ tailWord_250493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250550 : List Nat := [5, 1, 3, 1, 9]
def baseStart_250550 : Nat := 118140960795 + 250550 * 2 ^ 59
def prefixEnd_250550 : Nat := 4983230072969 + 3 ^ 40 * 250550 * 2
def baseEnd_250550 : Nat := 2823650545604388601871

theorem tailTrace_250550 : CollatzResearch.WordTrace tailWord_250550 prefixEnd_250550 2823650545604388601871 := by
  unfold tailWord_250550
  simp only [CollatzResearch.WordTrace]
  refine ⟨571144327644225961148819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6092206161538410252254069 571144327644225961148819)
  ·
    refine ⟨856716491466338941723229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571144327644225961148819 856716491466338941723229)
    ·
      refine ⟨321268684299877103146211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 856716491466338941723229 321268684299877103146211)
      ·
        refine ⟨481903026449815654719317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321268684299877103146211 481903026449815654719317)
        ·
          refine ⟨2823650545604388601871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 481903026449815654719317 2823650545604388601871)
          ·
            rfl

theorem cell19_250550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_250550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250550 prefixEnd_250550 := by exact prefixLift 250550
  have htrace : WordTrace (prefixWord ++ tailWord_250550) baseStart_250550 baseEnd_250550 := by
    simpa [prefixWord, tailWord_250550, baseEnd_250550] using wordTrace_append hprefix tailTrace_250550
  have hstable : (prefixWord ++ tailWord_250550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250550).length < 2 ^ (prefixWord ++ tailWord_250550).sum := by decide
  have hdescent : baseEnd_250550 < baseStart_250550 := by decide
  rcases family_descends (prefixWord ++ tailWord_250550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250628 : List Nat := [2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_250628 : Nat := 118140960795 + 250628 * 2 ^ 59
def prefixEnd_250628 : Nat := 4983230072969 + 3 ^ 40 * 250628 * 2
def baseEnd_250628 : Nat := 76262298948237422516971

theorem tailTrace_250628 : CollatzResearch.WordTrace tailWord_250628 prefixEnd_250628 76262298948237422516971 := by
  unfold tailWord_250628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570577068012517349860269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6094102757350023133147025 4570577068012517349860269)
  ·
    refine ⟨1713966400504694006197601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4570577068012517349860269 1713966400504694006197601)
    ·
      refine ⟨1285474800378520504648201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1713966400504694006197601 1285474800378520504648201)
      ·
        refine ⟨964106100283890378486151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285474800378520504648201 964106100283890378486151)
        ·
          refine ⟨1446159150425835567729227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964106100283890378486151 1446159150425835567729227)
          ·
            refine ⟨2169238725638753351593841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446159150425835567729227 2169238725638753351593841)
            ·
              refine ⟨1626929044229065013695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169238725638753351593841 1626929044229065013695381)
              ·
                refine ⟨76262298948237422516971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1626929044229065013695381 76262298948237422516971)
                ·
                  rfl

theorem cell19_250628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_250628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250628 prefixEnd_250628 := by exact prefixLift 250628
  have htrace : WordTrace (prefixWord ++ tailWord_250628) baseStart_250628 baseEnd_250628 := by
    simpa [prefixWord, tailWord_250628, baseEnd_250628] using wordTrace_append hprefix tailTrace_250628
  have hstable : (prefixWord ++ tailWord_250628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250628).length < 2 ^ (prefixWord ++ tailWord_250628).sum := by decide
  have hdescent : baseEnd_250628 < baseStart_250628 := by decide
  rcases family_descends (prefixWord ++ tailWord_250628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250744 : List Nat := [2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_250744 : Nat := 118140960795 + 250744 * 2 ^ 59
def prefixEnd_250744 : Nat := 4983230072969 + 3 ^ 40 * 250744 * 2
def baseEnd_250744 : Nat := 76297595988783523938877

theorem tailTrace_250744 : CollatzResearch.WordTrace tailWord_250744 prefixEnd_250744 76297595988783523938877 := by
  unfold tailWord_250744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572692501802393255471643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6096923335736524340628857 4572692501802393255471643)
  ·
    refine ⟨6859038752703589883207465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572692501802393255471643 6859038752703589883207465)
    ·
      refine ⟨5144279064527692412405599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6859038752703589883207465 5144279064527692412405599)
      ·
        refine ⟨7716418596791538618608399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144279064527692412405599 7716418596791538618608399)
        ·
          refine ⟨11574627895187307927912599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716418596791538618608399 11574627895187307927912599)
          ·
            refine ⟨17361941842780961891868899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11574627895187307927912599 17361941842780961891868899)
            ·
              refine ⟨26042912764171442837803349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17361941842780961891868899 26042912764171442837803349)
              ·
                refine ⟨76297595988783523938877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26042912764171442837803349 76297595988783523938877)
                ·
                  rfl

theorem cell19_250744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_250744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250744 prefixEnd_250744 := by exact prefixLift 250744
  have htrace : WordTrace (prefixWord ++ tailWord_250744) baseStart_250744 baseEnd_250744 := by
    simpa [prefixWord, tailWord_250744, baseEnd_250744] using wordTrace_append hprefix tailTrace_250744
  have hstable : (prefixWord ++ tailWord_250744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250744).length < 2 ^ (prefixWord ++ tailWord_250744).sum := by decide
  have hdescent : baseEnd_250744 < baseStart_250744 := by decide
  rcases family_descends (prefixWord ++ tailWord_250744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250759 : List Nat := [1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_250759 : Nat := 118140960795 + 250759 * 2 ^ 59
def prefixEnd_250759 : Nat := 4983230072969 + 3 ^ 40 * 250759 * 2
def baseEnd_250759 : Nat := 76302160261267933605503

theorem tailTrace_250759 : CollatzResearch.WordTrace tailWord_250759 prefixEnd_250759 76302160261267933605503 := by
  unfold tailWord_250759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145932098550444072739331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097288065700296048492887 9145932098550444072739331)
  ·
    refine ⟨13718898147825666109108997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145932098550444072739331 13718898147825666109108997)
    ·
      refine ⟨2572293402717312395457937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13718898147825666109108997 2572293402717312395457937)
      ·
        refine ⟨1929220052037984296593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2572293402717312395457937 1929220052037984296593453)
        ·
          refine ⟨723457519514244111222545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1929220052037984296593453 723457519514244111222545)
          ·
            refine ⟨542593139635683083416909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723457519514244111222545 542593139635683083416909)
            ·
              refine ⟨203472427363381156281341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542593139635683083416909 203472427363381156281341)
              ·
                refine ⟨76302160261267933605503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203472427363381156281341 76302160261267933605503)
                ·
                  rfl

theorem cell19_250759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_250759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250759 prefixEnd_250759 := by exact prefixLift 250759
  have htrace : WordTrace (prefixWord ++ tailWord_250759) baseStart_250759 baseEnd_250759 := by
    simpa [prefixWord, tailWord_250759, baseEnd_250759] using wordTrace_append hprefix tailTrace_250759
  have hstable : (prefixWord ++ tailWord_250759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250759).length < 2 ^ (prefixWord ++ tailWord_250759).sum := by decide
  have hdescent : baseEnd_250759 < baseStart_250759 := by decide
  rcases family_descends (prefixWord ++ tailWord_250759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250763 : List Nat := [1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_250763 : Nat := 118140960795 + 250763 * 2 ^ 59
def prefixEnd_250763 : Nat := 4983230072969 + 3 ^ 40 * 250763 * 2
def baseEnd_250763 : Nat := 76303377400597109516603

theorem tailTrace_250763 : CollatzResearch.WordTrace tailWord_250763 prefixEnd_250763 76303377400597109516603 := by
  unfold tailWord_250763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9146077990535952755884943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097385327023968503923295 9146077990535952755884943)
  ·
    refine ⟨13719116985803929133827415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9146077990535952755884943 13719116985803929133827415)
    ·
      refine ⟨20578675478705893700741123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13719116985803929133827415 20578675478705893700741123)
      ·
        refine ⟨30868013218058840551111685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20578675478705893700741123 30868013218058840551111685)
        ·
          refine ⟨5787752478386032603333441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30868013218058840551111685 5787752478386032603333441)
          ·
            refine ⟨4340814358789524452500081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787752478386032603333441 4340814358789524452500081)
            ·
              refine ⟨3255610769092143339375061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340814358789524452500081 3255610769092143339375061)
              ·
                refine ⟨76303377400597109516603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3255610769092143339375061 76303377400597109516603)
                ·
                  rfl

theorem cell19_250763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_250763 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250763 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250763 prefixEnd_250763 := by exact prefixLift 250763
  have htrace : WordTrace (prefixWord ++ tailWord_250763) baseStart_250763 baseEnd_250763 := by
    simpa [prefixWord, tailWord_250763, baseEnd_250763] using wordTrace_append hprefix tailTrace_250763
  have hstable : (prefixWord ++ tailWord_250763).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250763).length < 2 ^ (prefixWord ++ tailWord_250763).sum := by decide
  have hdescent : baseEnd_250763 < baseStart_250763 := by decide
  rcases family_descends (prefixWord ++ tailWord_250763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250816 : List Nat := [2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_250816 : Nat := 118140960795 + 250816 * 2 ^ 59
def prefixEnd_250816 : Nat := 4983230072969 + 3 ^ 40 * 250816 * 2
def baseEnd_250816 : Nat := 76319504496708690338681

theorem tailTrace_250816 : CollatzResearch.WordTrace tailWord_250816 prefixEnd_250816 76319504496708690338681 := by
  unfold tailWord_250816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574005529671971403782151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6098674039562628538376201 4574005529671971403782151)
  ·
    refine ⟨6861008294507957105673227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574005529671971403782151 6861008294507957105673227)
    ·
      refine ⟨10291512441761935658509841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861008294507957105673227 10291512441761935658509841)
      ·
        refine ⟨7718634331321451743882381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10291512441761935658509841 7718634331321451743882381)
        ·
          refine ⟨2894487874245544403955893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7718634331321451743882381 2894487874245544403955893)
          ·
            refine ⟨271358238210519787870865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2894487874245544403955893 271358238210519787870865)
            ·
              refine ⟨203518678657889840903149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271358238210519787870865 203518678657889840903149)
              ·
                refine ⟨76319504496708690338681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203518678657889840903149 76319504496708690338681)
                ·
                  rfl

theorem cell19_250816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_250816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250816 prefixEnd_250816 := by exact prefixLift 250816
  have htrace : WordTrace (prefixWord ++ tailWord_250816) baseStart_250816 baseEnd_250816 := by
    simpa [prefixWord, tailWord_250816, baseEnd_250816] using wordTrace_append hprefix tailTrace_250816
  have hstable : (prefixWord ++ tailWord_250816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250816).length < 2 ^ (prefixWord ++ tailWord_250816).sum := by decide
  have hdescent : baseEnd_250816 < baseStart_250816 := by decide
  rcases family_descends (prefixWord ++ tailWord_250816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250829 : List Nat := [1, 6, 3, 1, 2, 1, 5]
def baseStart_250829 : Nat := 118140960795 + 250829 * 2 ^ 59
def prefixEnd_250829 : Nat := 4983230072969 + 3 ^ 40 * 250829 * 2
def baseEnd_250829 : Nat := 25441153399842837349919

theorem tailTrace_250829 : CollatzResearch.WordTrace tailWord_250829 prefixEnd_250829 25441153399842837349919 := by
  unfold tailWord_250829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148485208296846027787541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098990138864564018525027 9148485208296846027787541)
  ·
    refine ⟨428835244138914657552541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9148485208296846027787541 428835244138914657552541)
    ·
      refine ⟨160813216552092996582203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428835244138914657552541 160813216552092996582203)
      ·
        refine ⟨241219824828139494873305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160813216552092996582203 241219824828139494873305)
        ·
          refine ⟨180914868621104621154979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241219824828139494873305 180914868621104621154979)
          ·
            refine ⟨271372302931656931732469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180914868621104621154979 271372302931656931732469)
            ·
              refine ⟨25441153399842837349919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271372302931656931732469 25441153399842837349919)
              ·
                rfl

theorem cell19_250829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_250829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250829 prefixEnd_250829 := by exact prefixLift 250829
  have htrace : WordTrace (prefixWord ++ tailWord_250829) baseStart_250829 baseEnd_250829 := by
    simpa [prefixWord, tailWord_250829, baseEnd_250829] using wordTrace_append hprefix tailTrace_250829
  have hstable : (prefixWord ++ tailWord_250829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250829).length < 2 ^ (prefixWord ++ tailWord_250829).sum := by decide
  have hdescent : baseEnd_250829 < baseStart_250829 := by decide
  rcases family_descends (prefixWord ++ tailWord_250829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250909 : List Nat := [1, 4, 2, 2, 4, 1, 1, 4]
def baseStart_250909 : Nat := 118140960795 + 250909 * 2 ^ 59
def prefixEnd_250909 : Nat := 4983230072969 + 3 ^ 40 * 250909 * 2
def baseEnd_250909 : Nat := 76347802986112030271761

theorem tailTrace_250909 : CollatzResearch.WordTrace tailWord_250909 prefixEnd_250909 76347802986112030271761 := by
  unfold tailWord_250909
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151403048007019690699781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6100935365338013127133187 9151403048007019690699781)
  ·
    refine ⟨1715888071501316192006209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9151403048007019690699781 1715888071501316192006209)
    ·
      refine ⟨1286916053625987144004657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715888071501316192006209 1286916053625987144004657)
      ·
        refine ⟨965187040219490358003493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286916053625987144004657 965187040219490358003493)
        ·
          refine ⟨180972570041154442125655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 965187040219490358003493 180972570041154442125655)
          ·
            refine ⟨271458855061731663188483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180972570041154442125655 271458855061731663188483)
            ·
              refine ⟨407188282592597494782725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271458855061731663188483 407188282592597494782725)
              ·
                refine ⟨76347802986112030271761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407188282592597494782725 76347802986112030271761)
                ·
                  rfl

theorem cell19_250909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_250909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250909 prefixEnd_250909 := by exact prefixLift 250909
  have htrace : WordTrace (prefixWord ++ tailWord_250909) baseStart_250909 baseEnd_250909 := by
    simpa [prefixWord, tailWord_250909, baseEnd_250909] using wordTrace_append hprefix tailTrace_250909
  have hstable : (prefixWord ++ tailWord_250909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250909).length < 2 ^ (prefixWord ++ tailWord_250909).sum := by decide
  have hdescent : baseEnd_250909 < baseStart_250909 := by decide
  rcases family_descends (prefixWord ++ tailWord_250909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250913 : List Nat := [1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_250913 : Nat := 118140960795 + 250913 * 2 ^ 59
def prefixEnd_250913 : Nat := 4983230072969 + 3 ^ 40 * 250913 * 2
def baseEnd_250913 : Nat := 76349020125441206182861

theorem tailTrace_250913 : CollatzResearch.WordTrace tailWord_250913 prefixEnd_250913 76349020125441206182861 := by
  unfold tailWord_250913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151548939992528373845393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6101032626661685582563595 9151548939992528373845393)
  ·
    refine ⟨6863661704994396280384045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9151548939992528373845393 6863661704994396280384045)
    ·
      refine ⟨2573873139372898605144017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6863661704994396280384045 2573873139372898605144017)
      ·
        refine ⟨1930404854529673953858013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573873139372898605144017 1930404854529673953858013)
        ·
          refine ⟨723901820448627732696755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930404854529673953858013 723901820448627732696755)
          ·
            refine ⟨1085852730672941599045133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723901820448627732696755 1085852730672941599045133)
            ·
              refine ⟨407194774002353099641925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085852730672941599045133 407194774002353099641925)
              ·
                refine ⟨76349020125441206182861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407194774002353099641925 76349020125441206182861)
                ·
                  rfl

theorem cell19_250913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_250913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250913 prefixEnd_250913 := by exact prefixLift 250913
  have htrace : WordTrace (prefixWord ++ tailWord_250913) baseStart_250913 baseEnd_250913 := by
    simpa [prefixWord, tailWord_250913, baseEnd_250913] using wordTrace_append hprefix tailTrace_250913
  have hstable : (prefixWord ++ tailWord_250913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250913).length < 2 ^ (prefixWord ++ tailWord_250913).sum := by decide
  have hdescent : baseEnd_250913 < baseStart_250913 := by decide
  rcases family_descends (prefixWord ++ tailWord_250913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250989 : List Nat := [1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_250989 : Nat := 118140960795 + 250989 * 2 ^ 59
def prefixEnd_250989 : Nat := 4983230072969 + 3 ^ 40 * 250989 * 2
def baseEnd_250989 : Nat := 76372145772695548493765

theorem tailTrace_250989 : CollatzResearch.WordTrace tailWord_250989 prefixEnd_250989 76372145772695548493765 := by
  unfold tailWord_250989
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154320887717193353612021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6102880591811462235741347 9154320887717193353612021)
  ·
    refine ⟨858217583223486876901127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9154320887717193353612021 858217583223486876901127)
    ·
      refine ⟨1287326374835230315351691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858217583223486876901127 1287326374835230315351691)
      ·
        refine ⟨1930989562252845473027537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287326374835230315351691 1930989562252845473027537)
        ·
          refine ⟨1448242171689634104770653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930989562252845473027537 1448242171689634104770653)
          ·
            refine ⟨543090814383612789288995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1448242171689634104770653 543090814383612789288995)
            ·
              refine ⟨814636221575419183933493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543090814383612789288995 814636221575419183933493)
              ·
                refine ⟨76372145772695548493765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814636221575419183933493 76372145772695548493765)
                ·
                  rfl

theorem cell19_250989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_250989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250989 prefixEnd_250989 := by exact prefixLift 250989
  have htrace : WordTrace (prefixWord ++ tailWord_250989) baseStart_250989 baseEnd_250989 := by
    simpa [prefixWord, tailWord_250989, baseEnd_250989] using wordTrace_append hprefix tailTrace_250989
  have hstable : (prefixWord ++ tailWord_250989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250989).length < 2 ^ (prefixWord ++ tailWord_250989).sum := by decide
  have hdescent : baseEnd_250989 < baseStart_250989 := by decide
  rcases family_descends (prefixWord ++ tailWord_250989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250991 : List Nat := [1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_250991 : Nat := 118140960795 + 250991 * 2 ^ 59
def prefixEnd_250991 : Nat := 4983230072969 + 3 ^ 40 * 250991 * 2
def baseEnd_250991 : Nat := 76372754342360136449315

theorem tailTrace_250991 : CollatzResearch.WordTrace tailWord_250991 prefixEnd_250991 76372754342360136449315 := by
  unfold tailWord_250991
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154393833709947695184827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6102929222473298463456551 9154393833709947695184827)
  ·
    refine ⟨13731590750564921542777241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9154393833709947695184827 13731590750564921542777241)
    ·
      refine ⟨10298693062923691157082931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13731590750564921542777241 10298693062923691157082931)
      ·
        refine ⟨15448039594385536735624397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298693062923691157082931 15448039594385536735624397)
        ·
          refine ⟨5793014847894576275859149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448039594385536735624397 5793014847894576275859149)
          ·
            refine ⟨2172380567960466103447181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5793014847894576275859149 2172380567960466103447181)
            ·
              refine ⟨814642712985174788792693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2172380567960466103447181 814642712985174788792693)
              ·
                refine ⟨76372754342360136449315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814642712985174788792693 76372754342360136449315)
                ·
                  rfl

theorem cell19_250991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_250991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250991 prefixEnd_250991 := by exact prefixLift 250991
  have htrace : WordTrace (prefixWord ++ tailWord_250991) baseStart_250991 baseEnd_250991 := by
    simpa [prefixWord, tailWord_250991, baseEnd_250991] using wordTrace_append hprefix tailTrace_250991
  have hstable : (prefixWord ++ tailWord_250991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250991).length < 2 ^ (prefixWord ++ tailWord_250991).sum := by decide
  have hdescent : baseEnd_250991 < baseStart_250991 := by decide
  rcases family_descends (prefixWord ++ tailWord_250991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251122 : List Nat := [3, 2, 1, 3, 3, 1, 6]
def baseStart_251122 : Nat := 118140960795 + 251122 * 2 ^ 59
def prefixEnd_251122 : Nat := 4983230072969 + 3 ^ 40 * 251122 * 2
def baseEnd_251122 : Nat := 25470871885130215845949

theorem tailTrace_251122 : CollatzResearch.WordTrace tailWord_251122 prefixEnd_251122 25470871885130215845949 := by
  unfold tailWord_251122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289792949058839267050905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6106114530823571378802413 2289792949058839267050905)
  ·
    refine ⟨1717344711794129450288179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2289792949058839267050905 1717344711794129450288179)
    ·
      refine ⟨2576017067691194175432269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717344711794129450288179 2576017067691194175432269)
      ·
        refine ⟨966006400384197815787101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2576017067691194175432269 966006400384197815787101)
        ·
          refine ⟨362252400144074180920163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966006400384197815787101 362252400144074180920163)
          ·
            refine ⟨543378600216111271380245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362252400144074180920163 543378600216111271380245)
            ·
              refine ⟨25470871885130215845949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543378600216111271380245 25470871885130215845949)
              ·
                rfl

theorem cell19_251122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_251122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251122 prefixEnd_251122 := by exact prefixLift 251122
  have htrace : WordTrace (prefixWord ++ tailWord_251122) baseStart_251122 baseEnd_251122 := by
    simpa [prefixWord, tailWord_251122, baseEnd_251122] using wordTrace_append hprefix tailTrace_251122
  have hstable : (prefixWord ++ tailWord_251122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251122).length < 2 ^ (prefixWord ++ tailWord_251122).sum := by decide
  have hdescent : baseEnd_251122 < baseStart_251122 := by decide
  rcases family_descends (prefixWord ++ tailWord_251122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251154 : List Nat := [3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_251154 : Nat := 118140960795 + 251154 * 2 ^ 59
def prefixEnd_251154 : Nat := 4983230072969 + 3 ^ 40 * 251154 * 2
def baseEnd_251154 : Nat := 76422352770024054826649

theorem tailTrace_251154 : CollatzResearch.WordTrace tailWord_251154 prefixEnd_251154 76422352770024054826649 := by
  unfold tailWord_251154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290084733029856633342129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6106892621412951022245677 2290084733029856633342129)
  ·
    refine ⟨1717563549772392475006597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2290084733029856633342129 1717563549772392475006597)
    ·
      refine ⟨322043165582323589063737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1717563549772392475006597 322043165582323589063737)
      ·
        refine ⟨241532374186742691797803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322043165582323589063737 241532374186742691797803)
        ·
          refine ⟨362298561280114037696705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241532374186742691797803 362298561280114037696705)
          ·
            refine ⟨271723920960085528272529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362298561280114037696705 271723920960085528272529)
            ·
              refine ⟨203792940720064146204397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271723920960085528272529 203792940720064146204397)
              ·
                refine ⟨76422352770024054826649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203792940720064146204397 76422352770024054826649)
                ·
                  rfl

theorem cell19_251154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_251154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251154 prefixEnd_251154 := by exact prefixLift 251154
  have htrace : WordTrace (prefixWord ++ tailWord_251154) baseStart_251154 baseEnd_251154 := by
    simpa [prefixWord, tailWord_251154, baseEnd_251154] using wordTrace_append hprefix tailTrace_251154
  have hstable : (prefixWord ++ tailWord_251154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251154).length < 2 ^ (prefixWord ++ tailWord_251154).sum := by decide
  have hdescent : baseEnd_251154 < baseStart_251154 := by decide
  rcases family_descends (prefixWord ++ tailWord_251154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251160 : List Nat := [2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_251160 : Nat := 118140960795 + 251160 * 2 ^ 59
def prefixEnd_251160 : Nat := 4983230072969 + 3 ^ 40 * 251160 * 2
def baseEnd_251160 : Nat := 76424178479017818693299

theorem tailTrace_251160 : CollatzResearch.WordTrace tailWord_251160 prefixEnd_251160 76424178479017818693299 := by
  unfold tailWord_251160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580278885048844779043467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6107038513398459705391289 4580278885048844779043467)
  ·
    refine ⟨6870418327573267168565201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580278885048844779043467 6870418327573267168565201)
    ·
      refine ⟨5152813745679950376423901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6870418327573267168565201 5152813745679950376423901)
      ·
        refine ⟨1932305154629981391158963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5152813745679950376423901 1932305154629981391158963)
        ·
          refine ⟨2898457731944972086738445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932305154629981391158963 2898457731944972086738445)
          ·
            refine ⟨1086921649479364532526917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2898457731944972086738445 1086921649479364532526917)
            ·
              refine ⟨203797809277380849848797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1086921649479364532526917 203797809277380849848797)
              ·
                refine ⟨76424178479017818693299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203797809277380849848797 76424178479017818693299)
                ·
                  rfl

theorem cell19_251160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_251160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251160 prefixEnd_251160 := by exact prefixLift 251160
  have htrace : WordTrace (prefixWord ++ tailWord_251160) baseStart_251160 baseEnd_251160 := by
    simpa [prefixWord, tailWord_251160, baseEnd_251160] using wordTrace_append hprefix tailTrace_251160
  have hstable : (prefixWord ++ tailWord_251160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251160).length < 2 ^ (prefixWord ++ tailWord_251160).sum := by decide
  have hdescent : baseEnd_251160 < baseStart_251160 := by decide
  rcases family_descends (prefixWord ++ tailWord_251160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251198 : List Nat := [4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_251198 : Nat := 118140960795 + 251198 * 2 ^ 59
def prefixEnd_251198 : Nat := 4983230072969 + 3 ^ 40 * 251198 * 2
def baseEnd_251198 : Nat := 76435741302644989848751

theorem tailTrace_251198 : CollatzResearch.WordTrace tailWord_251198 prefixEnd_251198 76435741302644989848751 := by
  unfold tailWord_251198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145242967995002755996281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6107962495973348031980165 1145242967995002755996281)
  ·
    refine ⟨858932225996252066997211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1145242967995002755996281 858932225996252066997211)
    ·
      refine ⟨1288398338994378100495817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858932225996252066997211 1288398338994378100495817)
      ·
        refine ⟨966298754245783575371863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1288398338994378100495817 966298754245783575371863)
        ·
          refine ⟨1449448131368675363057795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966298754245783575371863 1449448131368675363057795)
          ·
            refine ⟨2174172197053013044586693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449448131368675363057795 2174172197053013044586693)
            ·
              refine ⟨407657286947439945860005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2174172197053013044586693 407657286947439945860005)
              ·
                refine ⟨76435741302644989848751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407657286947439945860005 76435741302644989848751)
                ·
                  rfl

theorem cell19_251198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_251198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251198 prefixEnd_251198 := by exact prefixLift 251198
  have htrace : WordTrace (prefixWord ++ tailWord_251198) baseStart_251198 baseEnd_251198 := by
    simpa [prefixWord, tailWord_251198, baseEnd_251198] using wordTrace_append hprefix tailTrace_251198
  have hstable : (prefixWord ++ tailWord_251198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251198).length < 2 ^ (prefixWord ++ tailWord_251198).sum := by decide
  have hdescent : baseEnd_251198 < baseStart_251198 := by decide
  rcases family_descends (prefixWord ++ tailWord_251198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251200 : List Nat := [2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_251200 : Nat := 118140960795 + 251200 * 2 ^ 59
def prefixEnd_251200 : Nat := 4983230072969 + 3 ^ 40 * 251200 * 2
def baseEnd_251200 : Nat := 76436349872309577804301

theorem tailTrace_251200 : CollatzResearch.WordTrace tailWord_251200 prefixEnd_251200 76436349872309577804301 := by
  unfold tailWord_251200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581008344976388194771527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6108011126635184259695369 4581008344976388194771527)
  ·
    refine ⟨6871512517464582292157291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581008344976388194771527 6871512517464582292157291)
    ·
      refine ⟨10307268776196873438235937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871512517464582292157291 10307268776196873438235937)
      ·
        refine ⟨7730451582147655078676953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307268776196873438235937 7730451582147655078676953)
        ·
          refine ⟨5797838686610741309007715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7730451582147655078676953 5797838686610741309007715)
          ·
            refine ⟨8696758029916111963511573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797838686610741309007715 8696758029916111963511573)
            ·
              refine ⟨407660532652317748289605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8696758029916111963511573 407660532652317748289605)
              ·
                refine ⟨76436349872309577804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407660532652317748289605 76436349872309577804301)
                ·
                  rfl

theorem cell19_251200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_251200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251200 prefixEnd_251200 := by exact prefixLift 251200
  have htrace : WordTrace (prefixWord ++ tailWord_251200) baseStart_251200 baseEnd_251200 := by
    simpa [prefixWord, tailWord_251200, baseEnd_251200] using wordTrace_append hprefix tailTrace_251200
  have hstable : (prefixWord ++ tailWord_251200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251200).length < 2 ^ (prefixWord ++ tailWord_251200).sum := by decide
  have hdescent : baseEnd_251200 < baseStart_251200 := by decide
  rcases family_descends (prefixWord ++ tailWord_251200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251253 : List Nat := [1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_251253 : Nat := 118140960795 + 251253 * 2 ^ 59
def prefixEnd_251253 : Nat := 4983230072969 + 3 ^ 40 * 251253 * 2
def baseEnd_251253 : Nat := 76452476968421158626379

theorem tailTrace_251253 : CollatzResearch.WordTrace tailWord_251253 prefixEnd_251253 76452476968421158626379 := by
  unfold tailWord_251253
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163949758760766441222413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109299839173844294148275 9163949758760766441222413)
  ·
    refine ⟨3436481159535287415458405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9163949758760766441222413 3436481159535287415458405)
    ·
      refine ⟨644340217412866390398451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3436481159535287415458405 644340217412866390398451)
      ·
        refine ⟨966510326119299585597677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644340217412866390398451 966510326119299585597677)
        ·
          refine ⟨362441372294737344599129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966510326119299585597677 362441372294737344599129)
          ·
            refine ⟨271831029221053008449347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362441372294737344599129 271831029221053008449347)
            ·
              refine ⟨407746543831579512674021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271831029221053008449347 407746543831579512674021)
              ·
                refine ⟨76452476968421158626379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407746543831579512674021 76452476968421158626379)
                ·
                  rfl

theorem cell19_251253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_251253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251253 prefixEnd_251253 := by exact prefixLift 251253
  have htrace : WordTrace (prefixWord ++ tailWord_251253) baseStart_251253 baseEnd_251253 := by
    simpa [prefixWord, tailWord_251253, baseEnd_251253] using wordTrace_append hprefix tailTrace_251253
  have hstable : (prefixWord ++ tailWord_251253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251253).length < 2 ^ (prefixWord ++ tailWord_251253).sum := by decide
  have hdescent : baseEnd_251253 < baseStart_251253 := by decide
  rcases family_descends (prefixWord ++ tailWord_251253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251257 : List Nat := [1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_251257 : Nat := 118140960795 + 251257 * 2 ^ 59
def prefixEnd_251257 : Nat := 4983230072969 + 3 ^ 40 * 251257 * 2
def baseEnd_251257 : Nat := 76453694107750334537479

theorem tailTrace_251257 : CollatzResearch.WordTrace tailWord_251257 prefixEnd_251257 76453694107750334537479 := by
  unfold tailWord_251257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164095650746275124368025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109397100497516749578683 9164095650746275124368025)
  ·
    refine ⟨6873071738059706343276019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164095650746275124368025 6873071738059706343276019)
    ·
      refine ⟨10309607607089559514914029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873071738059706343276019 10309607607089559514914029)
      ·
        refine ⟨3866102852658584818092761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10309607607089559514914029 3866102852658584818092761)
        ·
          refine ⟨2899577139493938613569571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866102852658584818092761 2899577139493938613569571)
          ·
            refine ⟨4349365709240907920354357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899577139493938613569571 4349365709240907920354357)
            ·
              refine ⟨407753035241335117533221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4349365709240907920354357 407753035241335117533221)
              ·
                refine ⟨76453694107750334537479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407753035241335117533221 76453694107750334537479)
                ·
                  rfl

theorem cell19_251257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_251257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251257 prefixEnd_251257 := by exact prefixLift 251257
  have htrace : WordTrace (prefixWord ++ tailWord_251257) baseStart_251257 baseEnd_251257 := by
    simpa [prefixWord, tailWord_251257, baseEnd_251257] using wordTrace_append hprefix tailTrace_251257
  have hstable : (prefixWord ++ tailWord_251257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251257).length < 2 ^ (prefixWord ++ tailWord_251257).sum := by decide
  have hdescent : baseEnd_251257 < baseStart_251257 := by decide
  rcases family_descends (prefixWord ++ tailWord_251257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251295 : List Nat := [1, 1, 2, 5, 1, 3, 6]
def baseStart_251295 : Nat := 118140960795 + 251295 * 2 ^ 59
def prefixEnd_251295 : Nat := 4983230072969 + 3 ^ 40 * 251295 * 2
def baseEnd_251295 : Nat := 25488418977125835230977

theorem tailTrace_251295 : CollatzResearch.WordTrace tailWord_251295 prefixEnd_251295 25488418977125835230977 := by
  unfold tailWord_251295
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165481624608607614251339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6110321083072405076167559 9165481624608607614251339)
  ·
    refine ⟨13748222436912911421377009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9165481624608607614251339 13748222436912911421377009)
    ·
      refine ⟨10311166827684683566032757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13748222436912911421377009 10311166827684683566032757)
      ·
        refine ⟨966671890095439084315571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10311166827684683566032757 966671890095439084315571)
        ·
          refine ⟨1450007835143158626473357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966671890095439084315571 1450007835143158626473357)
          ·
            refine ⟨543752938178684484927509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1450007835143158626473357 543752938178684484927509)
            ·
              refine ⟨25488418977125835230977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543752938178684484927509 25488418977125835230977)
              ·
                rfl

theorem cell19_251295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_251295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251295 prefixEnd_251295 := by exact prefixLift 251295
  have htrace : WordTrace (prefixWord ++ tailWord_251295) baseStart_251295 baseEnd_251295 := by
    simpa [prefixWord, tailWord_251295, baseEnd_251295] using wordTrace_append hprefix tailTrace_251295
  have hstable : (prefixWord ++ tailWord_251295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251295).length < 2 ^ (prefixWord ++ tailWord_251295).sum := by decide
  have hdescent : baseEnd_251295 < baseStart_251295 := by decide
  rcases family_descends (prefixWord ++ tailWord_251295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251348 : List Nat := [2, 4, 1, 2, 4, 1, 5]
def baseStart_251348 : Nat := 118140960795 + 251348 * 2 ^ 59
def prefixEnd_251348 : Nat := 4983230072969 + 3 ^ 40 * 251348 * 2
def baseEnd_251348 : Nat := 25493794675829695505003

theorem tailTrace_251348 : CollatzResearch.WordTrace tailWord_251348 prefixEnd_251348 25493794675829695505003 := by
  unfold tailWord_251348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583707346708298832965349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6111609795611065110620465 4583707346708298832965349)
  ·
    refine ⟨859445127507806031181003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4583707346708298832965349 859445127507806031181003)
    ·
      refine ⟨1289167691261709046771505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859445127507806031181003 1289167691261709046771505)
      ·
        refine ⟨966875768446281785078629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289167691261709046771505 966875768446281785078629)
        ·
          refine ⟨181289206583677834702243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 966875768446281785078629 181289206583677834702243)
          ·
            refine ⟨271933809875516752053365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181289206583677834702243 271933809875516752053365)
            ·
              refine ⟨25493794675829695505003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271933809875516752053365 25493794675829695505003)
              ·
                rfl

theorem cell19_251348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_251348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251348 prefixEnd_251348 := by exact prefixLift 251348
  have htrace : WordTrace (prefixWord ++ tailWord_251348) baseStart_251348 baseEnd_251348 := by
    simpa [prefixWord, tailWord_251348, baseEnd_251348] using wordTrace_append hprefix tailTrace_251348
  have hstable : (prefixWord ++ tailWord_251348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251348).length < 2 ^ (prefixWord ++ tailWord_251348).sum := by decide
  have hdescent : baseEnd_251348 < baseStart_251348 := by decide
  rcases family_descends (prefixWord ++ tailWord_251348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251350 : List Nat := [5, 2, 1, 1, 1, 2, 7]
def baseStart_251350 : Nat := 118140960795 + 251350 * 2 ^ 59
def prefixEnd_251350 : Nat := 4983230072969 + 3 ^ 40 * 251350 * 2
def baseEnd_251350 : Nat := 25493997532384558156853

theorem tailTrace_251350 : CollatzResearch.WordTrace tailWord_251350 prefixEnd_251350 25493997532384558156853 := by
  unfold tailWord_251350
  simp only [CollatzResearch.WordTrace]
  refine ⟨572967977463084500468969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6111658426272901338335669 572967977463084500468969)
  ·
    refine ⟨429725983097313375351727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 572967977463084500468969 429725983097313375351727)
    ·
      refine ⟨644588974645970063027591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429725983097313375351727 644588974645970063027591)
      ·
        refine ⟨966883461968955094541387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644588974645970063027591 966883461968955094541387)
        ·
          refine ⟨1450325192953432641812081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966883461968955094541387 1450325192953432641812081)
          ·
            refine ⟨1087743894715074481359061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450325192953432641812081 1087743894715074481359061)
            ·
              refine ⟨25493997532384558156853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1087743894715074481359061 25493997532384558156853)
              ·
                rfl

theorem cell19_251350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_251350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251350 prefixEnd_251350 := by exact prefixLift 251350
  have htrace : WordTrace (prefixWord ++ tailWord_251350) baseStart_251350 baseEnd_251350 := by
    simpa [prefixWord, tailWord_251350, baseEnd_251350] using wordTrace_append hprefix tailTrace_251350
  have hstable : (prefixWord ++ tailWord_251350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251350).length < 2 ^ (prefixWord ++ tailWord_251350).sum := by decide
  have hdescent : baseEnd_251350 < baseStart_251350 := by decide
  rcases family_descends (prefixWord ++ tailWord_251350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251405 : List Nat := [1, 7, 1, 1, 2, 7]
def baseStart_251405 : Nat := 118140960795 + 251405 * 2 ^ 59
def prefixEnd_251405 : Nat := 4983230072969 + 3 ^ 40 * 251405 * 2
def baseEnd_251405 : Nat := 8499858695881093694243

theorem tailTrace_251405 : CollatzResearch.WordTrace tailWord_251405 prefixEnd_251405 8499858695881093694243 := by
  unfold tailWord_251405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169493654210096400755669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6112995769473397600503779 9169493654210096400755669)
  ·
    refine ⟨214910007520549134392711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9169493654210096400755669 214910007520549134392711)
    ·
      refine ⟨322365011280823701589067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214910007520549134392711 322365011280823701589067)
      ·
        refine ⟨483547516921235552383601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322365011280823701589067 483547516921235552383601)
        ·
          refine ⟨362660637690926664287701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483547516921235552383601 362660637690926664287701)
          ·
            refine ⟨8499858695881093694243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 362660637690926664287701 8499858695881093694243)
            ·
              rfl

theorem cell19_251405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_251405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251405 prefixEnd_251405 := by exact prefixLift 251405
  have htrace : WordTrace (prefixWord ++ tailWord_251405) baseStart_251405 baseEnd_251405 := by
    simpa [prefixWord, tailWord_251405, baseEnd_251405] using wordTrace_append hprefix tailTrace_251405
  have hstable : (prefixWord ++ tailWord_251405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251405).length < 2 ^ (prefixWord ++ tailWord_251405).sum := by decide
  have hdescent : baseEnd_251405 < baseStart_251405 := by decide
  rcases family_descends (prefixWord ++ tailWord_251405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251411 : List Nat := [1, 1, 1, 2, 1, 13]
def baseStart_251411 : Nat := 118140960795 + 251411 * 2 ^ 59
def prefixEnd_251411 : Nat := 4983230072969 + 3 ^ 40 * 251411 * 2
def baseEnd_251411 : Nat := 8500061552435956346093

theorem tailTrace_251411 : CollatzResearch.WordTrace tailWord_251411 prefixEnd_251411 8500061552435956346093 := by
  unfold tailWord_251411
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169712492188359425474087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6113141661458906283649391 9169712492188359425474087)
  ·
    refine ⟨13754568738282539138211131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9169712492188359425474087 13754568738282539138211131)
    ·
      refine ⟨20631853107423808707316697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13754568738282539138211131 20631853107423808707316697)
      ·
        refine ⟨15473889830567856530487523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20631853107423808707316697 15473889830567856530487523)
        ·
          refine ⟨23210834745851784795731285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15473889830567856530487523 23210834745851784795731285)
          ·
            refine ⟨8500061552435956346093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23210834745851784795731285 8500061552435956346093)
            ·
              rfl

theorem cell19_251411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_251411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251411 prefixEnd_251411 := by exact prefixLift 251411
  have htrace : WordTrace (prefixWord ++ tailWord_251411) baseStart_251411 baseEnd_251411 := by
    simpa [prefixWord, tailWord_251411, baseEnd_251411] using wordTrace_append hprefix tailTrace_251411
  have hstable : (prefixWord ++ tailWord_251411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251411).length < 2 ^ (prefixWord ++ tailWord_251411).sum := by decide
  have hdescent : baseEnd_251411 < baseStart_251411 := by decide
  rcases family_descends (prefixWord ++ tailWord_251411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251445 : List Nat := [1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_251445 : Nat := 118140960795 + 251445 * 2 ^ 59
def prefixEnd_251445 : Nat := 4983230072969 + 3 ^ 40 * 251445 * 2
def baseEnd_251445 : Nat := 76510899656221602359189

theorem tailTrace_251445 : CollatzResearch.WordTrace tailWord_251445 prefixEnd_251445 76510899656221602359189 := by
  unfold tailWord_251445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170952574065183232211789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6113968382710122154807859 9170952574065183232211789)
  ·
    refine ⟨3439107215274443712079421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9170952574065183232211789 3439107215274443712079421)
    ·
      refine ⟨1289665205727916392029783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3439107215274443712079421 1289665205727916392029783)
      ·
        refine ⟨1934497808591874588044675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289665205727916392029783 1934497808591874588044675)
        ·
          refine ⟨2901746712887811882067013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934497808591874588044675 2901746712887811882067013)
          ·
            refine ⟨544077508666464727887565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2901746712887811882067013 544077508666464727887565)
            ·
              refine ⟨204029065749924272957837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544077508666464727887565 204029065749924272957837)
              ·
                refine ⟨76510899656221602359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204029065749924272957837 76510899656221602359189)
                ·
                  rfl

theorem cell19_251445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_251445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251445 prefixEnd_251445 := by exact prefixLift 251445
  have htrace : WordTrace (prefixWord ++ tailWord_251445) baseStart_251445 baseEnd_251445 := by
    simpa [prefixWord, tailWord_251445, baseEnd_251445] using wordTrace_append hprefix tailTrace_251445
  have hstable : (prefixWord ++ tailWord_251445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251445).length < 2 ^ (prefixWord ++ tailWord_251445).sum := by decide
  have hdescent : baseEnd_251445 < baseStart_251445 := by decide
  rcases family_descends (prefixWord ++ tailWord_251445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251462 : List Nat := [6, 1, 1, 1, 3, 1, 6]
def baseStart_251462 : Nat := 118140960795 + 251462 * 2 ^ 59
def prefixEnd_251462 : Nat := 4983230072969 + 3 ^ 40 * 251462 * 2
def baseEnd_251462 : Nat := 25505357499456866660455

theorem tailTrace_251462 : CollatzResearch.WordTrace tailWord_251462 prefixEnd_251462 25505357499456866660455 := by
  unfold tailWord_251462
  simp only [CollatzResearch.WordTrace]
  refine ⟨286611644218862347986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6114381743335730090387093 286611644218862347986895)
  ·
    refine ⟨429917466328293521980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286611644218862347986895 429917466328293521980343)
    ·
      refine ⟨644876199492440282970515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429917466328293521980343 644876199492440282970515)
      ·
        refine ⟨967314299238660424455773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644876199492440282970515 967314299238660424455773)
        ·
          refine ⟨362742862214497659170915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967314299238660424455773 362742862214497659170915)
          ·
            refine ⟨544114293321746488756373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362742862214497659170915 544114293321746488756373)
            ·
              refine ⟨25505357499456866660455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 544114293321746488756373 25505357499456866660455)
              ·
                rfl

theorem cell19_251462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_251462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251462 prefixEnd_251462 := by exact prefixLift 251462
  have htrace : WordTrace (prefixWord ++ tailWord_251462) baseStart_251462 baseEnd_251462 := by
    simpa [prefixWord, tailWord_251462, baseEnd_251462] using wordTrace_append hprefix tailTrace_251462
  have hstable : (prefixWord ++ tailWord_251462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251462).length < 2 ^ (prefixWord ++ tailWord_251462).sum := by decide
  have hdescent : baseEnd_251462 < baseStart_251462 := by decide
  rcases family_descends (prefixWord ++ tailWord_251462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251502 : List Nat := [4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_251502 : Nat := 118140960795 + 251502 * 2 ^ 59
def prefixEnd_251502 : Nat := 4983230072969 + 3 ^ 40 * 251502 * 2
def baseEnd_251502 : Nat := 76528243891662359092367

theorem tailTrace_251502 : CollatzResearch.WordTrace tailWord_251502 prefixEnd_251502 76528243891662359092367 := by
  unfold tailWord_251502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146628941857335245879595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6115354356572454644691173 1146628941857335245879595)
  ·
    refine ⟨1719943412786002868819393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146628941857335245879595 1719943412786002868819393)
    ·
      refine ⟨1289957559589502151614545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719943412786002868819393 1289957559589502151614545)
      ·
        refine ⟨967468169692126613710909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289957559589502151614545 967468169692126613710909)
        ·
          refine ⟨362800563634547480141591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967468169692126613710909 362800563634547480141591)
          ·
            refine ⟨544200845451821220212387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362800563634547480141591 544200845451821220212387)
            ·
              refine ⟨816301268177731830318581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544200845451821220212387 816301268177731830318581)
              ·
                refine ⟨76528243891662359092367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816301268177731830318581 76528243891662359092367)
                ·
                  rfl

theorem cell19_251502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_251502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251502 prefixEnd_251502 := by exact prefixLift 251502
  have htrace : WordTrace (prefixWord ++ tailWord_251502) baseStart_251502 baseEnd_251502 := by
    simpa [prefixWord, tailWord_251502, baseEnd_251502] using wordTrace_append hprefix tailTrace_251502
  have hstable : (prefixWord ++ tailWord_251502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251502).length < 2 ^ (prefixWord ++ tailWord_251502).sum := by decide
  have hdescent : baseEnd_251502 < baseStart_251502 := by decide
  rcases family_descends (prefixWord ++ tailWord_251502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251504 : List Nat := [2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_251504 : Nat := 118140960795 + 251504 * 2 ^ 59
def prefixEnd_251504 : Nat := 4983230072969 + 3 ^ 40 * 251504 * 2
def baseEnd_251504 : Nat := 76528852461326947047917

theorem tailTrace_251504 : CollatzResearch.WordTrace tailWord_251504 prefixEnd_251504 76528852461326947047917 := by
  unfold tailWord_251504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586552240425718154304783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6115402987234290872406377 4586552240425718154304783)
  ·
    refine ⟨6879828360638577231457175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586552240425718154304783 6879828360638577231457175)
    ·
      refine ⟨10319742540957865847185763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879828360638577231457175 10319742540957865847185763)
      ·
        refine ⟨15479613811436798770778645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319742540957865847185763 15479613811436798770778645)
        ·
          refine ⟨725606897411099942380249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15479613811436798770778645 725606897411099942380249)
          ·
            refine ⟨544205173058324956785187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725606897411099942380249 544205173058324956785187)
            ·
              refine ⟨816307759587487435177781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544205173058324956785187 816307759587487435177781)
              ·
                refine ⟨76528852461326947047917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816307759587487435177781 76528852461326947047917)
                ·
                  rfl

theorem cell19_251504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_251504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251504 prefixEnd_251504 := by exact prefixLift 251504
  have htrace : WordTrace (prefixWord ++ tailWord_251504) baseStart_251504 baseEnd_251504 := by
    simpa [prefixWord, tailWord_251504, baseEnd_251504] using wordTrace_append hprefix tailTrace_251504
  have hstable : (prefixWord ++ tailWord_251504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251504).length < 2 ^ (prefixWord ++ tailWord_251504).sum := by decide
  have hdescent : baseEnd_251504 < baseStart_251504 := by decide
  rcases family_descends (prefixWord ++ tailWord_251504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251715 : List Nat := [1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_251715 : Nat := 118140960795 + 251715 * 2 ^ 59
def prefixEnd_251715 : Nat := 4983230072969 + 3 ^ 40 * 251715 * 2
def baseEnd_251715 : Nat := 76593056560940976358453

theorem tailTrace_251715 : CollatzResearch.WordTrace tailWord_251715 prefixEnd_251715 76593056560940976358453 := by
  unfold tailWord_251715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180800283087019344540599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6120533522058012896360399 9180800283087019344540599)
  ·
    refine ⟨13771200424630529016810899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9180800283087019344540599 13771200424630529016810899)
    ·
      refine ⟨20656800636945793525216349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13771200424630529016810899 20656800636945793525216349)
      ·
        refine ⟨7746300238854672571956131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20656800636945793525216349 7746300238854672571956131)
        ·
          refine ⟨11619450358282008857934197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746300238854672571956131 11619450358282008857934197)
          ·
            refine ⟨1089323471088938330431331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11619450358282008857934197 1089323471088938330431331)
            ·
              refine ⟨1633985206633407495646997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089323471088938330431331 1633985206633407495646997)
              ·
                refine ⟨76593056560940976358453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1633985206633407495646997 76593056560940976358453)
                ·
                  rfl

theorem cell19_251715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_251715 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251715 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251715 prefixEnd_251715 := by exact prefixLift 251715
  have htrace : WordTrace (prefixWord ++ tailWord_251715) baseStart_251715 baseEnd_251715 := by
    simpa [prefixWord, tailWord_251715, baseEnd_251715] using wordTrace_append hprefix tailTrace_251715
  have hstable : (prefixWord ++ tailWord_251715).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251715).length < 2 ^ (prefixWord ++ tailWord_251715).sum := by decide
  have hdescent : baseEnd_251715 < baseStart_251715 := by decide
  rcases family_descends (prefixWord ++ tailWord_251715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251732 : List Nat := [2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_251732 : Nat := 118140960795 + 251732 * 2 ^ 59
def prefixEnd_251732 : Nat := 4983230072969 + 3 ^ 40 * 251732 * 2
def baseEnd_251732 : Nat := 76598229403089973980629

theorem tailTrace_251732 : CollatzResearch.WordTrace tailWord_251732 prefixEnd_251732 76598229403089973980629 := by
  unfold tailWord_251732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590710162012715623954725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6120946882683620831939633 4590710162012715623954725)
  ·
    refine ⟨860758155377384179491511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4590710162012715623954725 860758155377384179491511)
    ·
      refine ⟨1291137233066076269237267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860758155377384179491511 1291137233066076269237267)
      ·
        refine ⟨1936705849599114403855901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291137233066076269237267 1936705849599114403855901)
        ·
          refine ⟨726264693599667901445963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1936705849599114403855901 726264693599667901445963)
          ·
            refine ⟨1089397040399501852168945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726264693599667901445963 1089397040399501852168945)
            ·
              refine ⟨817047780299626389126709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089397040399501852168945 817047780299626389126709)
              ·
                refine ⟨76598229403089973980629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 817047780299626389126709 76598229403089973980629)
                ·
                  rfl

theorem cell19_251732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_251732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251732 prefixEnd_251732 := by exact prefixLift 251732
  have htrace : WordTrace (prefixWord ++ tailWord_251732) baseStart_251732 baseEnd_251732 := by
    simpa [prefixWord, tailWord_251732, baseEnd_251732] using wordTrace_append hprefix tailTrace_251732
  have hstable : (prefixWord ++ tailWord_251732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251732).length < 2 ^ (prefixWord ++ tailWord_251732).sum := by decide
  have hdescent : baseEnd_251732 < baseStart_251732 := by decide
  rcases family_descends (prefixWord ++ tailWord_251732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251766 : List Nat := [5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_251766 : Nat := 118140960795 + 251766 * 2 ^ 59
def prefixEnd_251766 : Nat := 4983230072969 + 3 ^ 40 * 251766 * 2
def baseEnd_251766 : Nat := 76608575087387969224981

theorem tailTrace_251766 : CollatzResearch.WordTrace tailWord_251766 prefixEnd_251766 76608575087387969224981 := by
  unfold tailWord_251766
  simp only [CollatzResearch.WordTrace]
  refine ⟨573916275368890940915447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6121773603934836703098101 573916275368890940915447)
  ·
    refine ⟨860874413053336411373171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573916275368890940915447 860874413053336411373171)
    ·
      refine ⟨1291311619580004617059757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860874413053336411373171 1291311619580004617059757)
      ·
        refine ⟨484241857342501731397409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1291311619580004617059757 484241857342501731397409)
        ·
          refine ⟨363181393006876298548057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484241857342501731397409 363181393006876298548057)
          ·
            refine ⟨272386044755157223911043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363181393006876298548057 272386044755157223911043)
            ·
              refine ⟨408579067132735835866565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272386044755157223911043 408579067132735835866565)
              ·
                refine ⟨76608575087387969224981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408579067132735835866565 76608575087387969224981)
                ·
                  rfl

theorem cell19_251766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_251766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251766 prefixEnd_251766 := by exact prefixLift 251766
  have htrace : WordTrace (prefixWord ++ tailWord_251766) baseStart_251766 baseEnd_251766 := by
    simpa [prefixWord, tailWord_251766, baseEnd_251766] using wordTrace_append hprefix tailTrace_251766
  have hstable : (prefixWord ++ tailWord_251766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251766).length < 2 ^ (prefixWord ++ tailWord_251766).sum := by decide
  have hdescent : baseEnd_251766 < baseStart_251766 := by decide
  rcases family_descends (prefixWord ++ tailWord_251766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251865 : List Nat := [1, 2, 1, 2, 6, 2, 5]
def baseStart_251865 : Nat := 118140960795 + 251865 * 2 ^ 59
def prefixEnd_251865 : Nat := 4983230072969 + 3 ^ 40 * 251865 * 2
def baseEnd_251865 : Nat := 25546233095261691008237

theorem tailTrace_251865 : CollatzResearch.WordTrace tailWord_251865 prefixEnd_251865 25546233095261691008237 := by
  unfold tailWord_251865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9186271232543594962501049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6124180821695729975000699 9186271232543594962501049)
  ·
    refine ⟨6889703424407696221875787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9186271232543594962501049 6889703424407696221875787)
    ·
      refine ⟨10334555136611544332813681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889703424407696221875787 10334555136611544332813681)
      ·
        refine ⟨7750916352458658249610261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10334555136611544332813681 7750916352458658249610261)
        ·
          refine ⟨363324204021499605450481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7750916352458658249610261 363324204021499605450481)
          ·
            refine ⟨272493153016124704087861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363324204021499605450481 272493153016124704087861)
            ·
              refine ⟨25546233095261691008237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272493153016124704087861 25546233095261691008237)
              ·
                rfl

theorem cell19_251865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_251865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251865 prefixEnd_251865 := by exact prefixLift 251865
  have htrace : WordTrace (prefixWord ++ tailWord_251865) baseStart_251865 baseEnd_251865 := by
    simpa [prefixWord, tailWord_251865, baseEnd_251865] using wordTrace_append hprefix tailTrace_251865
  have hstable : (prefixWord ++ tailWord_251865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251865).length < 2 ^ (prefixWord ++ tailWord_251865).sum := by decide
  have hdescent : baseEnd_251865 < baseStart_251865 := by decide
  rcases family_descends (prefixWord ++ tailWord_251865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251905 : List Nat := [1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_251905 : Nat := 118140960795 + 251905 * 2 ^ 59
def prefixEnd_251905 : Nat := 4983230072969 + 3 ^ 40 * 251905 * 2
def baseEnd_251905 : Nat := 76650870679076832135713

theorem tailTrace_251905 : CollatzResearch.WordTrace tailWord_251905 prefixEnd_251905 76650870679076832135713 := by
  unfold tailWord_251905
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187730152398681793957169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6125153434932454529304779 9187730152398681793957169)
  ·
    refine ⟨6890797614299011345467877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9187730152398681793957169 6890797614299011345467877)
    ·
      refine ⟨1292024552681064627275227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6890797614299011345467877 1292024552681064627275227)
      ·
        refine ⟨1938036829021596940912841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292024552681064627275227 1938036829021596940912841)
        ·
          refine ⟨1453527621766197705684631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938036829021596940912841 1453527621766197705684631)
          ·
            refine ⟨2180291432649296558526947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453527621766197705684631 2180291432649296558526947)
            ·
              refine ⟨3270437148973944837790421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180291432649296558526947 3270437148973944837790421)
              ·
                refine ⟨76650870679076832135713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3270437148973944837790421 76650870679076832135713)
                ·
                  rfl

theorem cell19_251905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_251905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251905 prefixEnd_251905 := by exact prefixLift 251905
  have htrace : WordTrace (prefixWord ++ tailWord_251905) baseStart_251905 baseEnd_251905 := by
    simpa [prefixWord, tailWord_251905, baseEnd_251905] using wordTrace_append hprefix tailTrace_251905
  have hstable : (prefixWord ++ tailWord_251905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251905).length < 2 ^ (prefixWord ++ tailWord_251905).sum := by decide
  have hdescent : baseEnd_251905 < baseStart_251905 := by decide
  rcases family_descends (prefixWord ++ tailWord_251905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251922 : List Nat := [3, 2, 5, 9]
def baseStart_251922 : Nat := 118140960795 + 251922 * 2 ^ 59
def prefixEnd_251922 : Nat := 4983230072969 + 3 ^ 40 * 251922 * 2
def baseEnd_251922 : Nat := 946370907669454688369

theorem tailTrace_251922 : CollatzResearch.WordTrace tailWord_251922 prefixEnd_251922 946370907669454688369 := by
  unfold tailWord_251922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297087548334273424331505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6125566795558062464884013 2297087548334273424331505)
  ·
    refine ⟨1722815661250705068248629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297087548334273424331505 1722815661250705068248629)
    ·
      refine ⟨161513968242253600148309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1722815661250705068248629 161513968242253600148309)
      ·
        refine ⟨946370907669454688369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 161513968242253600148309 946370907669454688369)
        ·
          rfl

theorem cell19_251922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 9].length) (baseStart_251922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251922 prefixEnd_251922 := by exact prefixLift 251922
  have htrace : WordTrace (prefixWord ++ tailWord_251922) baseStart_251922 baseEnd_251922 := by
    simpa [prefixWord, tailWord_251922, baseEnd_251922] using wordTrace_append hprefix tailTrace_251922
  have hstable : (prefixWord ++ tailWord_251922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251922).length < 2 ^ (prefixWord ++ tailWord_251922).sum := by decide
  have hdescent : baseEnd_251922 < baseStart_251922 := by decide
  rcases family_descends (prefixWord ++ tailWord_251922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251941 : List Nat := [1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_251941 : Nat := 118140960795 + 251941 * 2 ^ 59
def prefixEnd_251941 : Nat := 4983230072969 + 3 ^ 40 * 251941 * 2
def baseEnd_251941 : Nat := 76661824933039415335615

theorem tailTrace_251941 : CollatzResearch.WordTrace tailWord_251941 prefixEnd_251941 76661824933039415335615 := by
  unfold tailWord_251941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189043180268259942267677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6126028786845506628178451 9189043180268259942267677)
  ·
    refine ⟨3445891192600597478350379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9189043180268259942267677 3445891192600597478350379)
    ·
      refine ⟨5168836788900896217525569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445891192600597478350379 5168836788900896217525569)
      ·
        refine ⟨3876627591675672163144177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5168836788900896217525569 3876627591675672163144177)
        ·
          refine ⟨2907470693756754122358133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876627591675672163144177 2907470693756754122358133)
          ·
            refine ⟨272575377539695698971075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2907470693756754122358133 272575377539695698971075)
            ·
              refine ⟨408863066309543548456613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272575377539695698971075 408863066309543548456613)
              ·
                refine ⟨76661824933039415335615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408863066309543548456613 76661824933039415335615)
                ·
                  rfl

theorem cell19_251941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_251941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251941 prefixEnd_251941 := by exact prefixLift 251941
  have htrace : WordTrace (prefixWord ++ tailWord_251941) baseStart_251941 baseEnd_251941 := by
    simpa [prefixWord, tailWord_251941, baseEnd_251941] using wordTrace_append hprefix tailTrace_251941
  have hstable : (prefixWord ++ tailWord_251941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251941).length < 2 ^ (prefixWord ++ tailWord_251941).sum := by decide
  have hdescent : baseEnd_251941 < baseStart_251941 := by decide
  rcases family_descends (prefixWord ++ tailWord_251941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251956 : List Nat := [2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_251956 : Nat := 118140960795 + 251956 * 2 ^ 59
def prefixEnd_251956 : Nat := 4983230072969 + 3 ^ 40 * 251956 * 2
def baseEnd_251956 : Nat := 76666389205523825002241

theorem tailTrace_251956 : CollatzResearch.WordTrace tailWord_251956 prefixEnd_251956 76666389205523825002241 := by
  unfold tailWord_251956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594795137606958752031861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6126393516809278336042481 4594795137606958752031861)
  ·
    refine ⟨430762044150652383002987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4594795137606958752031861 430762044150652383002987)
    ·
      refine ⟨646143066225978574504481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430762044150652383002987 646143066225978574504481)
      ·
        refine ⟨484607299669483930878361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646143066225978574504481 484607299669483930878361)
        ·
          refine ⟨363455474752112948158771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484607299669483930878361 363455474752112948158771)
          ·
            refine ⟨545183212128169422238157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363455474752112948158771 545183212128169422238157)
            ·
              refine ⟨204443704548063533339309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545183212128169422238157 204443704548063533339309)
              ·
                refine ⟨76666389205523825002241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204443704548063533339309 76666389205523825002241)
                ·
                  rfl

theorem cell19_251956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_251956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251956 prefixEnd_251956 := by exact prefixLift 251956
  have htrace : WordTrace (prefixWord ++ tailWord_251956) baseStart_251956 baseEnd_251956 := by
    simpa [prefixWord, tailWord_251956, baseEnd_251956] using wordTrace_append hprefix tailTrace_251956
  have hstable : (prefixWord ++ tailWord_251956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251956).length < 2 ^ (prefixWord ++ tailWord_251956).sum := by decide
  have hdescent : baseEnd_251956 < baseStart_251956 := by decide
  rcases family_descends (prefixWord ++ tailWord_251956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251958 : List Nat := [5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_251958 : Nat := 118140960795 + 251958 * 2 ^ 59
def prefixEnd_251958 : Nat := 4983230072969 + 3 ^ 40 * 251958 * 2
def baseEnd_251958 : Nat := 76666997775188412957791

theorem tailTrace_251958 : CollatzResearch.WordTrace tailWord_251958 prefixEnd_251958 76666997775188412957791 := by
  unfold tailWord_251958
  simp only [CollatzResearch.WordTrace]
  refine ⟨574353951325416990352283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6126442147471114563757685 574353951325416990352283)
  ·
    refine ⟨861530926988125485528425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574353951325416990352283 861530926988125485528425)
    ·
      refine ⟨646148195241094114146319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861530926988125485528425 646148195241094114146319)
      ·
        refine ⟨969222292861641171219479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646148195241094114146319 969222292861641171219479)
        ·
          refine ⟨1453833439292461756829219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969222292861641171219479 1453833439292461756829219)
          ·
            refine ⟨2180750158938692635243829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453833439292461756829219 2180750158938692635243829)
            ·
              refine ⟨204445327400502434554109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2180750158938692635243829 204445327400502434554109)
              ·
                refine ⟨76666997775188412957791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204445327400502434554109 76666997775188412957791)
                ·
                  rfl

theorem cell19_251958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_251958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_251958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_251958 prefixEnd_251958 := by exact prefixLift 251958
  have htrace : WordTrace (prefixWord ++ tailWord_251958) baseStart_251958 baseEnd_251958 := by
    simpa [prefixWord, tailWord_251958, baseEnd_251958] using wordTrace_append hprefix tailTrace_251958
  have hstable : (prefixWord ++ tailWord_251958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251958).length < 2 ^ (prefixWord ++ tailWord_251958).sum := by decide
  have hdescent : baseEnd_251958 < baseStart_251958 := by decide
  rcases family_descends (prefixWord ++ tailWord_251958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252055 : List Nat := [1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_252055 : Nat := 118140960795 + 252055 * 2 ^ 59
def prefixEnd_252055 : Nat := 4983230072969 + 3 ^ 40 * 252055 * 2
def baseEnd_252055 : Nat := 76696513403920928801971

theorem tailTrace_252055 : CollatzResearch.WordTrace tailWord_252055 prefixEnd_252055 76696513403920928801971 := by
  unfold tailWord_252055
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193201101855257411917619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6128800734570171607945079 9193201101855257411917619)
  ·
    refine ⟨13789801652782886117876429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9193201101855257411917619 13789801652782886117876429)
    ·
      refine ⟨5171175619793582294203661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13789801652782886117876429 5171175619793582294203661)
      ·
        refine ⟨1939190857422593360326373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5171175619793582294203661 1939190857422593360326373)
        ·
          refine ⟨363598285766736255061195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1939190857422593360326373 363598285766736255061195)
          ·
            refine ⟨545397428650104382591793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363598285766736255061195 545397428650104382591793)
            ·
              refine ⟨409048071487578286943845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545397428650104382591793 409048071487578286943845)
              ·
                refine ⟨76696513403920928801971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409048071487578286943845 76696513403920928801971)
                ·
                  rfl

theorem cell19_252055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_252055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252055 prefixEnd_252055 := by exact prefixLift 252055
  have htrace : WordTrace (prefixWord ++ tailWord_252055) baseStart_252055 baseEnd_252055 := by
    simpa [prefixWord, tailWord_252055, baseEnd_252055] using wordTrace_append hprefix tailTrace_252055
  have hstable : (prefixWord ++ tailWord_252055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252055).length < 2 ^ (prefixWord ++ tailWord_252055).sum := by decide
  have hdescent : baseEnd_252055 < baseStart_252055 := by decide
  rcases family_descends (prefixWord ++ tailWord_252055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252108 : List Nat := [2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_252108 : Nat := 118140960795 + 252108 * 2 ^ 59
def prefixEnd_252108 : Nat := 4983230072969 + 3 ^ 40 * 252108 * 2
def baseEnd_252108 : Nat := 76712640500032509624049

theorem tailTrace_252108 : CollatzResearch.WordTrace tailWord_252108 prefixEnd_252108 76712640500032509624049 := by
  unfold tailWord_252108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597567085331623731798489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6130089447108831642397985 4597567085331623731798489)
  ·
    refine ⟨3448175313998717798848867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4597567085331623731798489 3448175313998717798848867)
    ·
      refine ⟨5172262970998076698273301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448175313998717798848867 5172262970998076698273301)
      ·
        refine ⟨242449826765534845231561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5172262970998076698273301 242449826765534845231561)
        ·
          refine ⟨181837370074151133923671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242449826765534845231561 181837370074151133923671)
          ·
            refine ⟨272756055111226700885507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181837370074151133923671 272756055111226700885507)
            ·
              refine ⟨409134082666840051328261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272756055111226700885507 409134082666840051328261)
              ·
                refine ⟨76712640500032509624049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409134082666840051328261 76712640500032509624049)
                ·
                  rfl

theorem cell19_252108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_252108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252108 prefixEnd_252108 := by exact prefixLift 252108
  have htrace : WordTrace (prefixWord ++ tailWord_252108) baseStart_252108 baseEnd_252108 := by
    simpa [prefixWord, tailWord_252108, baseEnd_252108] using wordTrace_append hprefix tailTrace_252108
  have hstable : (prefixWord ++ tailWord_252108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252108).length < 2 ^ (prefixWord ++ tailWord_252108).sum := by decide
  have hdescent : baseEnd_252108 < baseStart_252108 := by decide
  rcases family_descends (prefixWord ++ tailWord_252108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252186 : List Nat := [3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_252186 : Nat := 118140960795 + 252186 * 2 ^ 59
def prefixEnd_252186 : Nat := 4983230072969 + 3 ^ 40 * 252186 * 2
def baseEnd_252186 : Nat := 76736374716951439890503

theorem tailTrace_252186 : CollatzResearch.WordTrace tailWord_252186 prefixEnd_252186 76736374716951439890503 := by
  unfold tailWord_252186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299494766095166696234103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6131986042920444523290941 2299494766095166696234103)
  ·
    refine ⟨3449242149142750044351155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299494766095166696234103 3449242149142750044351155)
    ·
      refine ⟨5173863223714125066526733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449242149142750044351155 5173863223714125066526733)
      ·
        refine ⟨1940198708892796899947525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5173863223714125066526733 1940198708892796899947525)
        ·
          refine ⟨363787257917399418740161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1940198708892796899947525 363787257917399418740161)
          ·
            refine ⟨272840443438049564055121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363787257917399418740161 272840443438049564055121)
            ·
              refine ⟨204630332578537173041341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272840443438049564055121 204630332578537173041341)
              ·
                refine ⟨76736374716951439890503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204630332578537173041341 76736374716951439890503)
                ·
                  rfl

theorem cell19_252186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_252186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252186 prefixEnd_252186 := by exact prefixLift 252186
  have htrace : WordTrace (prefixWord ++ tailWord_252186) baseStart_252186 baseEnd_252186 := by
    simpa [prefixWord, tailWord_252186, baseEnd_252186] using wordTrace_append hprefix tailTrace_252186
  have hstable : (prefixWord ++ tailWord_252186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252186).length < 2 ^ (prefixWord ++ tailWord_252186).sum := by decide
  have hdescent : baseEnd_252186 < baseStart_252186 := by decide
  rcases family_descends (prefixWord ++ tailWord_252186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252205 : List Nat := [1, 5, 3, 1, 2, 2, 5]
def baseStart_252205 : Nat := 118140960795 + 252205 * 2 ^ 59
def prefixEnd_252205 : Nat := 4983230072969 + 3 ^ 40 * 252205 * 2
def baseEnd_252205 : Nat := 25580718709588341822743

theorem tailTrace_252205 : CollatzResearch.WordTrace tailWord_252205 prefixEnd_252205 25580718709588341822743 := by
  unfold tailWord_252205
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198672051311833029878069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6132448034207888686585379 9198672051311833029878069)
  ·
    refine ⟨862375504810484346551069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9198672051311833029878069 862375504810484346551069)
    ·
      refine ⟨323390814303931629956651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862375504810484346551069 323390814303931629956651)
      ·
        refine ⟨485086221455897444934977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323390814303931629956651 485086221455897444934977)
        ·
          refine ⟨363814666091923083701233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485086221455897444934977 363814666091923083701233)
          ·
            refine ⟨272860999568942312775925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363814666091923083701233 272860999568942312775925)
            ·
              refine ⟨25580718709588341822743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272860999568942312775925 25580718709588341822743)
              ·
                rfl

theorem cell19_252205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_252205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252205 prefixEnd_252205 := by exact prefixLift 252205
  have htrace : WordTrace (prefixWord ++ tailWord_252205) baseStart_252205 baseEnd_252205 := by
    simpa [prefixWord, tailWord_252205, baseEnd_252205] using wordTrace_append hprefix tailTrace_252205
  have hstable : (prefixWord ++ tailWord_252205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252205).length < 2 ^ (prefixWord ++ tailWord_252205).sum := by decide
  have hdescent : baseEnd_252205 < baseStart_252205 := by decide
  rcases family_descends (prefixWord ++ tailWord_252205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252266 : List Nat := [3, 1, 3, 3, 1, 8]
def baseStart_252266 : Nat := 118140960795 + 252266 * 2 ^ 59
def prefixEnd_252266 : Nat := 4983230072969 + 3 ^ 40 * 252266 * 2
def baseEnd_252266 : Nat := 8528968611503884234723

theorem tailTrace_252266 : CollatzResearch.WordTrace tailWord_252266 prefixEnd_252266 8528968611503884234723 := by
  unfold tailWord_252266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300224226022710111962163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6133931269393893631899101 2300224226022710111962163)
  ·
    refine ⟨3450336339034065167943245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300224226022710111962163 3450336339034065167943245)
    ·
      refine ⟨1293876127137774437978717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3450336339034065167943245 1293876127137774437978717)
      ·
        refine ⟨485203547676665414242019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1293876127137774437978717 485203547676665414242019)
        ·
          refine ⟨727805321514998121363029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485203547676665414242019 727805321514998121363029)
          ·
            refine ⟨8528968611503884234723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 727805321514998121363029 8528968611503884234723)
            ·
              rfl

theorem cell19_252266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_252266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252266 prefixEnd_252266 := by exact prefixLift 252266
  have htrace : WordTrace (prefixWord ++ tailWord_252266) baseStart_252266 baseEnd_252266 := by
    simpa [prefixWord, tailWord_252266, baseEnd_252266] using wordTrace_append hprefix tailTrace_252266
  have hstable : (prefixWord ++ tailWord_252266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252266).length < 2 ^ (prefixWord ++ tailWord_252266).sum := by decide
  have hdescent : baseEnd_252266 < baseStart_252266 := by decide
  rcases family_descends (prefixWord ++ tailWord_252266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252268 : List Nat := [2, 2, 1, 1, 13]
def baseStart_252268 : Nat := 118140960795 + 252268 * 2 ^ 59
def prefixEnd_252268 : Nat := 4983230072969 + 3 ^ 40 * 252268 * 2
def baseEnd_252268 : Nat := 2843012076785168372891

theorem tailTrace_252268 : CollatzResearch.WordTrace tailWord_252268 prefixEnd_252268 2843012076785168372891 := by
  unfold tailWord_252268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4600484925041797394710729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6133979900055729859614305 4600484925041797394710729)
  ·
    refine ⟨3450363693781348046033047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4600484925041797394710729 3450363693781348046033047)
    ·
      refine ⟨5175545540672022069049571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450363693781348046033047 5175545540672022069049571)
      ·
        refine ⟨7763318311008033103574357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175545540672022069049571 7763318311008033103574357)
        ·
          refine ⟨2843012076785168372891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7763318311008033103574357 2843012076785168372891)
          ·
            rfl

theorem cell19_252268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_252268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252268 prefixEnd_252268 := by exact prefixLift 252268
  have htrace : WordTrace (prefixWord ++ tailWord_252268) baseStart_252268 baseEnd_252268 := by
    simpa [prefixWord, tailWord_252268, baseEnd_252268] using wordTrace_append hprefix tailTrace_252268
  have hstable : (prefixWord ++ tailWord_252268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252268).length < 2 ^ (prefixWord ++ tailWord_252268).sum := by decide
  have hdescent : baseEnd_252268 < baseStart_252268 := by decide
  rcases family_descends (prefixWord ++ tailWord_252268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252285 : List Nat := [1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_252285 : Nat := 118140960795 + 252285 * 2 ^ 59
def prefixEnd_252285 : Nat := 4983230072969 + 3 ^ 40 * 252285 * 2
def baseEnd_252285 : Nat := 76766498915348543690233

theorem tailTrace_252285 : CollatzResearch.WordTrace tailWord_252285 prefixEnd_252285 76766498915348543690233 := by
  unfold tailWord_252285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201589891022006692790309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6134393260681337795193539 9201589891022006692790309)
  ·
    refine ⟨1725298104566626254898183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9201589891022006692790309 1725298104566626254898183)
    ·
      refine ⟨2587947156849939382347275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725298104566626254898183 2587947156849939382347275)
      ·
        refine ⟨3881920735274909073520913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587947156849939382347275 3881920735274909073520913)
        ·
          refine ⟨2911440551456181805140685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881920735274909073520913 2911440551456181805140685)
          ·
            refine ⟨1091790206796068176927757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2911440551456181805140685 1091790206796068176927757)
            ·
              refine ⟨409421327548525566347909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091790206796068176927757 409421327548525566347909)
              ·
                refine ⟨76766498915348543690233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409421327548525566347909 76766498915348543690233)
                ·
                  rfl

theorem cell19_252285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_252285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252285 prefixEnd_252285 := by exact prefixLift 252285
  have htrace : WordTrace (prefixWord ++ tailWord_252285) baseStart_252285 baseEnd_252285 := by
    simpa [prefixWord, tailWord_252285, baseEnd_252285] using wordTrace_append hprefix tailTrace_252285
  have hstable : (prefixWord ++ tailWord_252285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252285).length < 2 ^ (prefixWord ++ tailWord_252285).sum := by decide
  have hdescent : baseEnd_252285 < baseStart_252285 := by decide
  rcases family_descends (prefixWord ++ tailWord_252285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252321 : List Nat := [1, 2, 3, 5, 1, 1, 6]
def baseStart_252321 : Nat := 118140960795 + 252321 * 2 ^ 59
def prefixEnd_252321 : Nat := 4983230072969 + 3 ^ 40 * 252321 * 2
def baseEnd_252321 : Nat := 25592484389770375630045

theorem tailTrace_252321 : CollatzResearch.WordTrace tailWord_252321 prefixEnd_252321 25592484389770375630045 := by
  unfold tailWord_252321
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202902918891584841100817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6135268612594389894067211 9202902918891584841100817)
  ·
    refine ⟨6902177189168688630825613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9202902918891584841100817 6902177189168688630825613)
    ·
      refine ⟨2588316445938258236559605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6902177189168688630825613 2588316445938258236559605)
      ·
        refine ⟨242654666806711709677463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2588316445938258236559605 242654666806711709677463)
        ·
          refine ⟨363982000210067564516195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242654666806711709677463 363982000210067564516195)
          ·
            refine ⟨545973000315101346774293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363982000210067564516195 545973000315101346774293)
            ·
              refine ⟨25592484389770375630045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 545973000315101346774293 25592484389770375630045)
              ·
                rfl

theorem cell19_252321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_252321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252321 prefixEnd_252321 := by exact prefixLift 252321
  have htrace : WordTrace (prefixWord ++ tailWord_252321) baseStart_252321 baseEnd_252321 := by
    simpa [prefixWord, tailWord_252321, baseEnd_252321] using wordTrace_append hprefix tailTrace_252321
  have hstable : (prefixWord ++ tailWord_252321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252321).length < 2 ^ (prefixWord ++ tailWord_252321).sum := by decide
  have hdescent : baseEnd_252321 < baseStart_252321 := by decide
  rcases family_descends (prefixWord ++ tailWord_252321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252325 : List Nat := [1, 3, 1, 2, 1, 1, 10]
def baseStart_252325 : Nat := 118140960795 + 252325 * 2 ^ 59
def prefixEnd_252325 : Nat := 4983230072969 + 3 ^ 40 * 252325 * 2
def baseEnd_252325 : Nat := 25592890102880100933745

theorem tailTrace_252325 : CollatzResearch.WordTrace tailWord_252325 prefixEnd_252325 25592890102880100933745 := by
  unfold tailWord_252325
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203048810877093524246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6135365873918062349497619 9203048810877093524246429)
  ·
    refine ⟨3451143304078910071592411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9203048810877093524246429 3451143304078910071592411)
    ·
      refine ⟨5176714956118365107388617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451143304078910071592411 5176714956118365107388617)
      ·
        refine ⟨3882536217088773830541463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176714956118365107388617 3882536217088773830541463)
        ·
          refine ⟨5823804325633160745812195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882536217088773830541463 5823804325633160745812195)
          ·
            refine ⟨8735706488449741118718293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823804325633160745812195 8735706488449741118718293)
            ·
              refine ⟨25592890102880100933745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8735706488449741118718293 25592890102880100933745)
              ·
                rfl

theorem cell19_252325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_252325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252325 prefixEnd_252325 := by exact prefixLift 252325
  have htrace : WordTrace (prefixWord ++ tailWord_252325) baseStart_252325 baseEnd_252325 := by
    simpa [prefixWord, tailWord_252325, baseEnd_252325] using wordTrace_append hprefix tailTrace_252325
  have hstable : (prefixWord ++ tailWord_252325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252325).length < 2 ^ (prefixWord ++ tailWord_252325).sum := by decide
  have hdescent : baseEnd_252325 < baseStart_252325 := by decide
  rcases family_descends (prefixWord ++ tailWord_252325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252344 : List Nat := [2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_252344 : Nat := 118140960795 + 252344 * 2 ^ 59
def prefixEnd_252344 : Nat := 4983230072969 + 3 ^ 40 * 252344 * 2
def baseEnd_252344 : Nat := 76784451720453888378961

theorem tailTrace_252344 : CollatzResearch.WordTrace tailWord_252344 prefixEnd_252344 76784451720453888378961 := by
  unfold tailWord_252344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4601870898904129884594043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6135827865205506512792057 4601870898904129884594043)
  ·
    refine ⟨6902806348356194826891065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4601870898904129884594043 6902806348356194826891065)
    ·
      refine ⟨5177104761267146120168299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6902806348356194826891065 5177104761267146120168299)
      ·
        refine ⟨7765657141900719180252449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177104761267146120168299 7765657141900719180252449)
        ·
          refine ⟨5824242856425539385189337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7765657141900719180252449 5824242856425539385189337)
          ·
            refine ⟨4368182142319154538892003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824242856425539385189337 4368182142319154538892003)
            ·
              refine ⟨6552273213478731808338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368182142319154538892003 6552273213478731808338005)
              ·
                refine ⟨76784451720453888378961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6552273213478731808338005 76784451720453888378961)
                ·
                  rfl

theorem cell19_252344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_252344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252344 prefixEnd_252344 := by exact prefixLift 252344
  have htrace : WordTrace (prefixWord ++ tailWord_252344) baseStart_252344 baseEnd_252344 := by
    simpa [prefixWord, tailWord_252344, baseEnd_252344] using wordTrace_append hprefix tailTrace_252344
  have hstable : (prefixWord ++ tailWord_252344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252344).length < 2 ^ (prefixWord ++ tailWord_252344).sum := by decide
  have hdescent : baseEnd_252344 < baseStart_252344 := by decide
  rcases family_descends (prefixWord ++ tailWord_252344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252353 : List Nat := [1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_252353 : Nat := 118140960795 + 252353 * 2 ^ 59
def prefixEnd_252353 : Nat := 4983230072969 + 3 ^ 40 * 252353 * 2
def baseEnd_252353 : Nat := 76787190283944534178937

theorem tailTrace_252353 : CollatzResearch.WordTrace tailWord_252353 prefixEnd_252353 76787190283944534178937 := by
  unfold tailWord_252353
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204070054775654306265713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6136046703183769537510475 9204070054775654306265713)
  ·
    refine ⟨6903052541081740729699285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9204070054775654306265713 6903052541081740729699285)
    ·
      refine ⟨161790293931603298352327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6903052541081740729699285 161790293931603298352327)
      ·
        refine ⟨242685440897404947528491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161790293931603298352327 242685440897404947528491)
        ·
          refine ⟨364028161346107421292737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242685440897404947528491 364028161346107421292737)
          ·
            refine ⟨273021121009580565969553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364028161346107421292737 273021121009580565969553)
            ·
              refine ⟨204765840757185424477165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273021121009580565969553 204765840757185424477165)
              ·
                refine ⟨76787190283944534178937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204765840757185424477165 76787190283944534178937)
                ·
                  rfl

theorem cell19_252353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_252353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252353 prefixEnd_252353 := by exact prefixLift 252353
  have htrace : WordTrace (prefixWord ++ tailWord_252353) baseStart_252353 baseEnd_252353 := by
    simpa [prefixWord, tailWord_252353, baseEnd_252353] using wordTrace_append hprefix tailTrace_252353
  have hstable : (prefixWord ++ tailWord_252353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252353).length < 2 ^ (prefixWord ++ tailWord_252353).sum := by decide
  have hdescent : baseEnd_252353 < baseStart_252353 := by decide
  rcases family_descends (prefixWord ++ tailWord_252353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252359 : List Nat := [1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_252359 : Nat := 118140960795 + 252359 * 2 ^ 59
def prefixEnd_252359 : Nat := 4983230072969 + 3 ^ 40 * 252359 * 2
def baseEnd_252359 : Nat := 76789015992938298045587

theorem tailTrace_252359 : CollatzResearch.WordTrace tailWord_252359 prefixEnd_252359 76789015992938298045587 := by
  unfold tailWord_252359
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204288892753917330984131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6136192595169278220656087 9204288892753917330984131)
  ·
    refine ⟨13806433339130875996476197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9204288892753917330984131 13806433339130875996476197)
    ·
      refine ⟨2588706251087039249339287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13806433339130875996476197 2588706251087039249339287)
      ·
        refine ⟨3883059376630558874008931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588706251087039249339287 3883059376630558874008931)
        ·
          refine ⟨5824589064945838311013397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883059376630558874008931 5824589064945838311013397)
          ·
            refine ⟨273027612419336170828753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5824589064945838311013397 273027612419336170828753)
            ·
              refine ⟨204770709314502128121565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273027612419336170828753 204770709314502128121565)
              ·
                refine ⟨76789015992938298045587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204770709314502128121565 76789015992938298045587)
                ·
                  rfl

theorem cell19_252359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_252359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252359 prefixEnd_252359 := by exact prefixLift 252359
  have htrace : WordTrace (prefixWord ++ tailWord_252359) baseStart_252359 baseEnd_252359 := by
    simpa [prefixWord, tailWord_252359, baseEnd_252359] using wordTrace_append hprefix tailTrace_252359
  have hstable : (prefixWord ++ tailWord_252359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252359).length < 2 ^ (prefixWord ++ tailWord_252359).sum := by decide
  have hdescent : baseEnd_252359 < baseStart_252359 := by decide
  rcases family_descends (prefixWord ++ tailWord_252359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252361 : List Nat := [1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_252361 : Nat := 118140960795 + 252361 * 2 ^ 59
def prefixEnd_252361 : Nat := 4983230072969 + 3 ^ 40 * 252361 * 2
def baseEnd_252361 : Nat := 76789624562602886001137

theorem tailTrace_252361 : CollatzResearch.WordTrace tailWord_252361 prefixEnd_252361 76789624562602886001137 := by
  unfold tailWord_252361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204361838746671672556937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6136241225831114448371291 9204361838746671672556937)
  ·
    refine ⟨6903271379060003754417703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9204361838746671672556937 6903271379060003754417703)
    ·
      refine ⟨10354907068590005631626555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903271379060003754417703 10354907068590005631626555)
      ·
        refine ⟨15532360602885008447439833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354907068590005631626555 15532360602885008447439833)
        ·
          refine ⟨11649270452163756335579875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15532360602885008447439833 11649270452163756335579875)
          ·
            refine ⟨17473905678245634503369813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649270452163756335579875 17473905678245634503369813)
            ·
              refine ⟨204772332166941029336365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 17473905678245634503369813 204772332166941029336365)
              ·
                refine ⟨76789624562602886001137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204772332166941029336365 76789624562602886001137)
                ·
                  rfl

theorem cell19_252361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_252361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252361 prefixEnd_252361 := by exact prefixLift 252361
  have htrace : WordTrace (prefixWord ++ tailWord_252361) baseStart_252361 baseEnd_252361 := by
    simpa [prefixWord, tailWord_252361, baseEnd_252361] using wordTrace_append hprefix tailTrace_252361
  have hstable : (prefixWord ++ tailWord_252361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252361).length < 2 ^ (prefixWord ++ tailWord_252361).sum := by decide
  have hdescent : baseEnd_252361 < baseStart_252361 := by decide
  rcases family_descends (prefixWord ++ tailWord_252361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252397 : List Nat := [1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_252397 : Nat := 118140960795 + 252397 * 2 ^ 59
def prefixEnd_252397 : Nat := 4983230072969 + 3 ^ 40 * 252397 * 2
def baseEnd_252397 : Nat := 76800578816565469201039

theorem tailTrace_252397 : CollatzResearch.WordTrace tailWord_252397 prefixEnd_252397 76800578816565469201039 := by
  unfold tailWord_252397
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205674866616249820867445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6137116577744166547244963 9205674866616249820867445)
  ·
    refine ⟨863032018745273420706323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9205674866616249820867445 863032018745273420706323)
    ·
      refine ⟨1294548028117910131059485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863032018745273420706323 1294548028117910131059485)
      ·
        refine ⟨485455510544216299147307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1294548028117910131059485 485455510544216299147307)
        ·
          refine ⟨728183265816324448720961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485455510544216299147307 728183265816324448720961)
          ·
            refine ⟨546137449362243336540721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728183265816324448720961 546137449362243336540721)
            ·
              refine ⟨409603087021682502405541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546137449362243336540721 409603087021682502405541)
              ·
                refine ⟨76800578816565469201039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409603087021682502405541 76800578816565469201039)
                ·
                  rfl

theorem cell19_252397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_252397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252397 prefixEnd_252397 := by exact prefixLift 252397
  have htrace : WordTrace (prefixWord ++ tailWord_252397) baseStart_252397 baseEnd_252397 := by
    simpa [prefixWord, tailWord_252397, baseEnd_252397] using wordTrace_append hprefix tailTrace_252397
  have hstable : (prefixWord ++ tailWord_252397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252397).length < 2 ^ (prefixWord ++ tailWord_252397).sum := by decide
  have hdescent : baseEnd_252397 < baseStart_252397 := by decide
  rcases family_descends (prefixWord ++ tailWord_252397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252452 : List Nat := [2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_252452 : Nat := 118140960795 + 252452 * 2 ^ 59
def prefixEnd_252452 : Nat := 4983230072969 + 3 ^ 40 * 252452 * 2
def baseEnd_252452 : Nat := 76817314482341637978667

theorem tailTrace_252452 : CollatzResearch.WordTrace tailWord_252452 prefixEnd_252452 76817314482341637978667 := by
  unfold tailWord_252452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603840440708497107059805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6138453920944662809413073 4603840440708497107059805)
  ·
    refine ⟨1726440165265686415147427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4603840440708497107059805 1726440165265686415147427)
    ·
      refine ⟨2589660247898529622721141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726440165265686415147427 2589660247898529622721141)
      ·
        refine ⟨242780648240487152130107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2589660247898529622721141 242780648240487152130107)
        ·
          refine ⟨364170972360730728195161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242780648240487152130107 364170972360730728195161)
          ·
            refine ⟨273128229270548046146371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364170972360730728195161 273128229270548046146371)
            ·
              refine ⟨409692343905822069219557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273128229270548046146371 409692343905822069219557)
              ·
                refine ⟨76817314482341637978667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409692343905822069219557 76817314482341637978667)
                ·
                  rfl

theorem cell19_252452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_252452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252452 prefixEnd_252452 := by exact prefixLift 252452
  have htrace : WordTrace (prefixWord ++ tailWord_252452) baseStart_252452 baseEnd_252452 := by
    simpa [prefixWord, tailWord_252452, baseEnd_252452] using wordTrace_append hprefix tailTrace_252452
  have hstable : (prefixWord ++ tailWord_252452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252452).length < 2 ^ (prefixWord ++ tailWord_252452).sum := by decide
  have hdescent : baseEnd_252452 < baseStart_252452 := by decide
  rcases family_descends (prefixWord ++ tailWord_252452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252515 : List Nat := [1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_252515 : Nat := 118140960795 + 252515 * 2 ^ 59
def prefixEnd_252515 : Nat := 4983230072969 + 3 ^ 40 * 252515 * 2
def baseEnd_252515 : Nat := 76836484426776158578495

theorem tailTrace_252515 : CollatzResearch.WordTrace tailWord_252515 prefixEnd_252515 76836484426776158578495 := by
  unfold tailWord_252515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209978680188755973662999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6139985786792503982441999 9209978680188755973662999)
  ·
    refine ⟨13814968020283133960494499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9209978680188755973662999 13814968020283133960494499)
    ·
      refine ⟨20722452030424700940741749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814968020283133960494499 20722452030424700940741749)
      ·
        refine ⟨1942729877852315713194539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20722452030424700940741749 1942729877852315713194539)
        ·
          refine ⟨2914094816778473569791809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942729877852315713194539 2914094816778473569791809)
          ·
            refine ⟨2185571112583855177343857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914094816778473569791809 2185571112583855177343857)
            ·
              refine ⟨1639178334437891383007893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185571112583855177343857 1639178334437891383007893)
              ·
                refine ⟨76836484426776158578495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639178334437891383007893 76836484426776158578495)
                ·
                  rfl

theorem cell19_252515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_252515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252515 prefixEnd_252515 := by exact prefixLift 252515
  have htrace : WordTrace (prefixWord ++ tailWord_252515) baseStart_252515 baseEnd_252515 := by
    simpa [prefixWord, tailWord_252515, baseEnd_252515] using wordTrace_append hprefix tailTrace_252515
  have hstable : (prefixWord ++ tailWord_252515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252515).length < 2 ^ (prefixWord ++ tailWord_252515).sum := by decide
  have hdescent : baseEnd_252515 < baseStart_252515 := by decide
  rcases family_descends (prefixWord ++ tailWord_252515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252528 : List Nat := [2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_252528 : Nat := 118140960795 + 252528 * 2 ^ 59
def prefixEnd_252528 : Nat := 4983230072969 + 3 ^ 40 * 252528 * 2
def baseEnd_252528 : Nat := 76840440129595980289571

theorem tailTrace_252528 : CollatzResearch.WordTrace tailWord_252528 prefixEnd_252528 76840440129595980289571 := by
  unfold tailWord_252528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605226414570829596943119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6140301886094439462590825 4605226414570829596943119)
  ·
    refine ⟨6907839621856244395414679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4605226414570829596943119 6907839621856244395414679)
    ·
      refine ⟨10361759432784366593122019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907839621856244395414679 10361759432784366593122019)
      ·
        refine ⟨15542639149176549889683029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361759432784366593122019 15542639149176549889683029)
        ·
          refine ⟨182140302529412694019723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 15542639149176549889683029 182140302529412694019723)
          ·
            refine ⟨273210453794119041029585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182140302529412694019723 273210453794119041029585)
            ·
              refine ⟨204907840345589280772189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273210453794119041029585 204907840345589280772189)
              ·
                refine ⟨76840440129595980289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204907840345589280772189 76840440129595980289571)
                ·
                  rfl

theorem cell19_252528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_252528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252528 prefixEnd_252528 := by exact prefixLift 252528
  have htrace : WordTrace (prefixWord ++ tailWord_252528) baseStart_252528 baseEnd_252528 := by
    simpa [prefixWord, tailWord_252528, baseEnd_252528] using wordTrace_append hprefix tailTrace_252528
  have hstable : (prefixWord ++ tailWord_252528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252528).length < 2 ^ (prefixWord ++ tailWord_252528).sum := by decide
  have hdescent : baseEnd_252528 < baseStart_252528 := by decide
  rcases family_descends (prefixWord ++ tailWord_252528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252589 : List Nat := [1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_252589 : Nat := 118140960795 + 252589 * 2 ^ 59
def prefixEnd_252589 : Nat := 4983230072969 + 3 ^ 40 * 252589 * 2
def baseEnd_252589 : Nat := 76859001504365912933849

theorem tailTrace_252589 : CollatzResearch.WordTrace tailWord_252589 prefixEnd_252589 76859001504365912933849 := by
  unfold tailWord_252589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212677681920666611856821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6141785121280444407904547 9212677681920666611856821)
  ·
    refine ⟨863688532680062494861577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9212677681920666611856821 863688532680062494861577)
    ·
      refine ⟨647766399510046871146183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863688532680062494861577 647766399510046871146183)
      ·
        refine ⟨971649599265070306719275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647766399510046871146183 971649599265070306719275)
        ·
          refine ⟨1457474398897605460078913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971649599265070306719275 1457474398897605460078913)
          ·
            refine ⟨1093105799173204095059185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457474398897605460078913 1093105799173204095059185)
            ·
              refine ⟨819829349379903071294389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093105799173204095059185 819829349379903071294389)
              ·
                refine ⟨76859001504365912933849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819829349379903071294389 76859001504365912933849)
                ·
                  rfl

theorem cell19_252589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_252589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252589 prefixEnd_252589 := by exact prefixLift 252589
  have htrace : WordTrace (prefixWord ++ tailWord_252589) baseStart_252589 baseEnd_252589 := by
    simpa [prefixWord, tailWord_252589, baseEnd_252589] using wordTrace_append hprefix tailTrace_252589
  have hstable : (prefixWord ++ tailWord_252589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252589).length < 2 ^ (prefixWord ++ tailWord_252589).sum := by decide
  have hdescent : baseEnd_252589 < baseStart_252589 := by decide
  rcases family_descends (prefixWord ++ tailWord_252589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252591 : List Nat := [1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_252591 : Nat := 118140960795 + 252591 * 2 ^ 59
def prefixEnd_252591 : Nat := 4983230072969 + 3 ^ 40 * 252591 * 2
def baseEnd_252591 : Nat := 76859610074030500889399

theorem tailTrace_252591 : CollatzResearch.WordTrace tailWord_252591 prefixEnd_252591 76859610074030500889399 := by
  unfold tailWord_252591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212750627913420953429627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6141833751942280635619751 9212750627913420953429627)
  ·
    refine ⟨13819125941870131430144441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9212750627913420953429627 13819125941870131430144441)
    ·
      refine ⟨10364344456402598572608331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13819125941870131430144441 10364344456402598572608331)
      ·
        refine ⟨15546516684603897858912497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364344456402598572608331 15546516684603897858912497)
        ·
          refine ⟨11659887513452923394184373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15546516684603897858912497 11659887513452923394184373)
          ·
            refine ⟨1093114454386211568204785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11659887513452923394184373 1093114454386211568204785)
            ·
              refine ⟨819835840789658676153589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093114454386211568204785 819835840789658676153589)
              ·
                refine ⟨76859610074030500889399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819835840789658676153589 76859610074030500889399)
                ·
                  rfl

theorem cell19_252591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_252591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252591 prefixEnd_252591 := by exact prefixLift 252591
  have htrace : WordTrace (prefixWord ++ tailWord_252591) baseStart_252591 baseEnd_252591 := by
    simpa [prefixWord, tailWord_252591, baseEnd_252591] using wordTrace_append hprefix tailTrace_252591
  have hstable : (prefixWord ++ tailWord_252591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252591).length < 2 ^ (prefixWord ++ tailWord_252591).sum := by decide
  have hdescent : baseEnd_252591 < baseStart_252591 := by decide
  rcases family_descends (prefixWord ++ tailWord_252591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252621 : List Nat := [1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_252621 : Nat := 118140960795 + 252621 * 2 ^ 59
def prefixEnd_252621 : Nat := 4983230072969 + 3 ^ 40 * 252621 * 2
def baseEnd_252621 : Nat := 76868738618999320222651

theorem tailTrace_252621 : CollatzResearch.WordTrace tailWord_252621 prefixEnd_252621 76868738618999320222651 := by
  unfold tailWord_252621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213844817804736077021717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6142563211869824051347811 9213844817804736077021717)
  ·
    refine ⟨431898975834597003610393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9213844817804736077021717 431898975834597003610393)
    ·
      refine ⟨323924231875947752707795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431898975834597003610393 323924231875947752707795)
      ·
        refine ⟨485886347813921629061693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323924231875947752707795 485886347813921629061693)
        ·
          refine ⟨182207380430220610898135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485886347813921629061693 182207380430220610898135)
          ·
            refine ⟨273311070645330916347203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182207380430220610898135 273311070645330916347203)
            ·
              refine ⟨409966605967996374520805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273311070645330916347203 409966605967996374520805)
              ·
                refine ⟨76868738618999320222651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409966605967996374520805 76868738618999320222651)
                ·
                  rfl

theorem cell19_252621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_252621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252621 prefixEnd_252621 := by exact prefixLift 252621
  have htrace : WordTrace (prefixWord ++ tailWord_252621) baseStart_252621 baseEnd_252621 := by
    simpa [prefixWord, tailWord_252621, baseEnd_252621] using wordTrace_append hprefix tailTrace_252621
  have hstable : (prefixWord ++ tailWord_252621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252621).length < 2 ^ (prefixWord ++ tailWord_252621).sum := by decide
  have hdescent : baseEnd_252621 < baseStart_252621 := by decide
  rcases family_descends (prefixWord ++ tailWord_252621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252661 : List Nat := [1, 3, 6, 1, 1, 1, 6]
def baseStart_252661 : Nat := 118140960795 + 252661 * 2 ^ 59
def prefixEnd_252661 : Nat := 4983230072969 + 3 ^ 40 * 252661 * 2
def baseEnd_252661 : Nat := 25626970004097026444551

theorem tailTrace_252661 : CollatzResearch.WordTrace tailWord_252661 prefixEnd_252661 25626970004097026444551 := by
  unfold tailWord_252661
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215303737659822908477837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6143535825106548605651891 9215303737659822908477837)
  ·
    refine ⟨3455738901622433590679189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9215303737659822908477837 3455738901622433590679189)
    ·
      refine ⟨161987761013551574563087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3455738901622433590679189 161987761013551574563087)
      ·
        refine ⟨242981641520327361844631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161987761013551574563087 242981641520327361844631)
        ·
          refine ⟨364472462280491042766947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242981641520327361844631 364472462280491042766947)
          ·
            refine ⟨546708693420736564150421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364472462280491042766947 546708693420736564150421)
            ·
              refine ⟨25626970004097026444551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 546708693420736564150421 25626970004097026444551)
              ·
                rfl

theorem cell19_252661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_252661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252661 prefixEnd_252661 := by exact prefixLift 252661
  have htrace : WordTrace (prefixWord ++ tailWord_252661) baseStart_252661 baseEnd_252661 := by
    simpa [prefixWord, tailWord_252661, baseEnd_252661] using wordTrace_append hprefix tailTrace_252661
  have hstable : (prefixWord ++ tailWord_252661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252661).length < 2 ^ (prefixWord ++ tailWord_252661).sum := by decide
  have hdescent : baseEnd_252661 < baseStart_252661 := by decide
  rcases family_descends (prefixWord ++ tailWord_252661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252686 : List Nat := [4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_252686 : Nat := 118140960795 + 252686 * 2 ^ 59
def prefixEnd_252686 : Nat := 4983230072969 + 3 ^ 40 * 252686 * 2
def baseEnd_252686 : Nat := 76888517133098428778029

theorem tailTrace_252686 : CollatzResearch.WordTrace tailWord_252686 prefixEnd_252686 76888517133098428778029 := by
  unfold tailWord_252686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152026945321156522267239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6144143708379501452091941 1152026945321156522267239)
  ·
    refine ⟨1728040417981734783400859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1152026945321156522267239 1728040417981734783400859)
    ·
      refine ⟨2592060626972602175101289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728040417981734783400859 2592060626972602175101289)
      ·
        refine ⟨1944045470229451631325967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592060626972602175101289 1944045470229451631325967)
        ·
          refine ⟨2916068205344177446988951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944045470229451631325967 2916068205344177446988951)
          ·
            refine ⟨4374102308016266170483427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916068205344177446988951 4374102308016266170483427)
            ·
              refine ⟨6561153462024399255725141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374102308016266170483427 6561153462024399255725141)
              ·
                refine ⟨76888517133098428778029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6561153462024399255725141 76888517133098428778029)
                ·
                  rfl

theorem cell19_252686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_252686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252686 prefixEnd_252686 := by exact prefixLift 252686
  have htrace : WordTrace (prefixWord ++ tailWord_252686) baseStart_252686 baseEnd_252686 := by
    simpa [prefixWord, tailWord_252686, baseEnd_252686] using wordTrace_append hprefix tailTrace_252686
  have hstable : (prefixWord ++ tailWord_252686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252686).length < 2 ^ (prefixWord ++ tailWord_252686).sum := by decide
  have hdescent : baseEnd_252686 < baseStart_252686 := by decide
  rcases family_descends (prefixWord ++ tailWord_252686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252701 : List Nat := [1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_252701 : Nat := 118140960795 + 252701 * 2 ^ 59
def prefixEnd_252701 : Nat := 4983230072969 + 3 ^ 40 * 252701 * 2
def baseEnd_252701 : Nat := 76893081405582838444655

theorem tailTrace_252701 : CollatzResearch.WordTrace tailWord_252701 prefixEnd_252701 76893081405582838444655 := by
  unfold tailWord_252701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216762657514909739933957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6144508438343273159955971 9216762657514909739933957)
  ·
    refine ⟨1728142998284045576237617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9216762657514909739933957 1728142998284045576237617)
    ·
      refine ⟨1296107248713034182178213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1728142998284045576237617 1296107248713034182178213)
      ·
        refine ⟨243020109133693909158415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1296107248713034182178213 243020109133693909158415)
        ·
          refine ⟨364530163700540863737623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243020109133693909158415 364530163700540863737623)
          ·
            refine ⟨546795245550811295606435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364530163700540863737623 546795245550811295606435)
            ·
              refine ⟨820192868326216943409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546795245550811295606435 820192868326216943409653)
              ·
                refine ⟨76893081405582838444655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820192868326216943409653 76893081405582838444655)
                ·
                  rfl

theorem cell19_252701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_252701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252701 prefixEnd_252701 := by exact prefixLift 252701
  have htrace : WordTrace (prefixWord ++ tailWord_252701) baseStart_252701 baseEnd_252701 := by
    simpa [prefixWord, tailWord_252701, baseEnd_252701] using wordTrace_append hprefix tailTrace_252701
  have hstable : (prefixWord ++ tailWord_252701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252701).length < 2 ^ (prefixWord ++ tailWord_252701).sum := by decide
  have hdescent : baseEnd_252701 < baseStart_252701 := by decide
  rcases family_descends (prefixWord ++ tailWord_252701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252703 : List Nat := [1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_252703 : Nat := 118140960795 + 252703 * 2 ^ 59
def prefixEnd_252703 : Nat := 4983230072969 + 3 ^ 40 * 252703 * 2
def baseEnd_252703 : Nat := 76893689975247426400205

theorem tailTrace_252703 : CollatzResearch.WordTrace tailWord_252703 prefixEnd_252703 76893689975247426400205 := by
  unfold tailWord_252703
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216835603507664081506763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6144557069005109387671175 9216835603507664081506763)
  ·
    refine ⟨13825253405261496122260145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9216835603507664081506763 13825253405261496122260145)
    ·
      refine ⟨10368940053946122091695109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13825253405261496122260145 10368940053946122091695109)
      ·
        refine ⟨1944176260114897892192833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10368940053946122091695109 1944176260114897892192833)
        ·
          refine ⟨1458132195086173419144625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944176260114897892192833 1458132195086173419144625)
          ·
            refine ⟨1093599146314630064358469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458132195086173419144625 1093599146314630064358469)
            ·
              refine ⟨205049839933993137067213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1093599146314630064358469 205049839933993137067213)
              ·
                refine ⟨76893689975247426400205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205049839933993137067213 76893689975247426400205)
                ·
                  rfl

theorem cell19_252703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_252703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252703 prefixEnd_252703 := by exact prefixLift 252703
  have htrace : WordTrace (prefixWord ++ tailWord_252703) baseStart_252703 baseEnd_252703 := by
    simpa [prefixWord, tailWord_252703, baseEnd_252703] using wordTrace_append hprefix tailTrace_252703
  have hstable : (prefixWord ++ tailWord_252703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252703).length < 2 ^ (prefixWord ++ tailWord_252703).sum := by decide
  have hdescent : baseEnd_252703 < baseStart_252703 := by decide
  rcases family_descends (prefixWord ++ tailWord_252703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252705 : List Nat := [1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_252705 : Nat := 118140960795 + 252705 * 2 ^ 59
def prefixEnd_252705 : Nat := 4983230072969 + 3 ^ 40 * 252705 * 2
def baseEnd_252705 : Nat := 76894298544912014355755

theorem tailTrace_252705 : CollatzResearch.WordTrace tailWord_252705 prefixEnd_252705 76894298544912014355755 := by
  unfold tailWord_252705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216908549500418423079569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6144605699666945615386379 9216908549500418423079569)
  ·
    refine ⟨6912681412125313817309677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9216908549500418423079569 6912681412125313817309677)
    ·
      refine ⟨2592255529546992681491129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6912681412125313817309677 2592255529546992681491129)
      ·
        refine ⟨1944191647160244511118347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592255529546992681491129 1944191647160244511118347)
        ·
          refine ⟨2916287470740366766677521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944191647160244511118347 2916287470740366766677521)
          ·
            refine ⟨2187215603055275075008141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916287470740366766677521 2187215603055275075008141)
            ·
              refine ⟨820205851145728153128053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187215603055275075008141 820205851145728153128053)
              ·
                refine ⟨76894298544912014355755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820205851145728153128053 76894298544912014355755)
                ·
                  rfl

theorem cell19_252705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_252705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252705 prefixEnd_252705 := by exact prefixLift 252705
  have htrace : WordTrace (prefixWord ++ tailWord_252705) baseStart_252705 baseEnd_252705 := by
    simpa [prefixWord, tailWord_252705, baseEnd_252705] using wordTrace_append hprefix tailTrace_252705
  have hstable : (prefixWord ++ tailWord_252705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252705).length < 2 ^ (prefixWord ++ tailWord_252705).sum := by decide
  have hdescent : baseEnd_252705 < baseStart_252705 := by decide
  rcases family_descends (prefixWord ++ tailWord_252705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252762 : List Nat := [3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_252762 : Nat := 118140960795 + 252762 * 2 ^ 59
def prefixEnd_252762 : Nat := 4983230072969 + 3 ^ 40 * 252762 * 2
def baseEnd_252762 : Nat := 76911642780352771088933

theorem tailTrace_252762 : CollatzResearch.WordTrace tailWord_252762 prefixEnd_252762 76911642780352771088933 := by
  unfold tailWord_252762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304746877573479289476135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6145991673529278105269693 2304746877573479289476135)
  ·
    refine ⟨3457120316360218934214203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304746877573479289476135 3457120316360218934214203)
    ·
      refine ⟨5185680474540328401321305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457120316360218934214203 5185680474540328401321305)
      ·
        refine ⟨3889260355905246300990979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5185680474540328401321305 3889260355905246300990979)
        ·
          refine ⟨5833890533857869451486469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889260355905246300990979 5833890533857869451486469)
          ·
            refine ⟨1093854475098350522153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5833890533857869451486469 1093854475098350522153713)
            ·
              refine ⟨820390856323762891615285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093854475098350522153713 820390856323762891615285)
              ·
                refine ⟨76911642780352771088933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820390856323762891615285 76911642780352771088933)
                ·
                  rfl

theorem cell19_252762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_252762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252762 prefixEnd_252762 := by exact prefixLift 252762
  have htrace : WordTrace (prefixWord ++ tailWord_252762) baseStart_252762 baseEnd_252762 := by
    simpa [prefixWord, tailWord_252762, baseEnd_252762] using wordTrace_append hprefix tailTrace_252762
  have hstable : (prefixWord ++ tailWord_252762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252762).length < 2 ^ (prefixWord ++ tailWord_252762).sum := by decide
  have hdescent : baseEnd_252762 < baseStart_252762 := by decide
  rcases family_descends (prefixWord ++ tailWord_252762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252868 : List Nat := [2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_252868 : Nat := 118140960795 + 252868 * 2 ^ 59
def prefixEnd_252868 : Nat := 4983230072969 + 3 ^ 40 * 252868 * 2
def baseEnd_252868 : Nat := 76943896972575932733089

theorem tailTrace_252868 : CollatzResearch.WordTrace tailWord_252868 prefixEnd_252868 76943896972575932733089 := by
  unfold tailWord_252868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611426823954948630631629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6148569098606598174175505 4611426823954948630631629)
  ·
    refine ⟨1729285058983105736486861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4611426823954948630631629 1729285058983105736486861)
    ·
      refine ⟨648481897118664651182573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1729285058983105736486861 648481897118664651182573)
      ·
        refine ⟨243180711419499244193465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648481897118664651182573 243180711419499244193465)
        ·
          refine ⟨182385533564624433145099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243180711419499244193465 182385533564624433145099)
          ·
            refine ⟨273578300346936649717649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182385533564624433145099 273578300346936649717649)
            ·
              refine ⟨205183725260202487288237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273578300346936649717649 205183725260202487288237)
              ·
                refine ⟨76943896972575932733089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205183725260202487288237 76943896972575932733089)
                ·
                  rfl

theorem cell19_252868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_252868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252868 prefixEnd_252868 := by exact prefixLift 252868
  have htrace : WordTrace (prefixWord ++ tailWord_252868) baseStart_252868 baseEnd_252868 := by
    simpa [prefixWord, tailWord_252868, baseEnd_252868] using wordTrace_append hprefix tailTrace_252868
  have hstable : (prefixWord ++ tailWord_252868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252868).length < 2 ^ (prefixWord ++ tailWord_252868).sum := by decide
  have hdescent : baseEnd_252868 < baseStart_252868 := by decide
  rcases family_descends (prefixWord ++ tailWord_252868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252872 : List Nat := [2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_252872 : Nat := 118140960795 + 252872 * 2 ^ 59
def prefixEnd_252872 : Nat := 4983230072969 + 3 ^ 40 * 252872 * 2
def baseEnd_252872 : Nat := 76945114111905108644189

theorem tailTrace_252872 : CollatzResearch.WordTrace tailWord_252872 prefixEnd_252872 76945114111905108644189 := by
  unfold tailWord_252872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611499769947702972204435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6148666359930270629605913 4611499769947702972204435)
  ·
    refine ⟨6917249654921554458306653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611499769947702972204435 6917249654921554458306653)
    ·
      refine ⟨2593968620595582921864995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6917249654921554458306653 2593968620595582921864995)
      ·
        refine ⟨3890952930893374382797493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593968620595582921864995 3890952930893374382797493)
        ·
          refine ⟨364776837271253848387265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3890952930893374382797493 364776837271253848387265)
          ·
            refine ⟨273582627953440386290449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364776837271253848387265 273582627953440386290449)
            ·
              refine ⟨205186970965080289717837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273582627953440386290449 205186970965080289717837)
              ·
                refine ⟨76945114111905108644189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205186970965080289717837 76945114111905108644189)
                ·
                  rfl

theorem cell19_252872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_252872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252872 prefixEnd_252872 := by exact prefixLift 252872
  have htrace : WordTrace (prefixWord ++ tailWord_252872) baseStart_252872 baseEnd_252872 := by
    simpa [prefixWord, tailWord_252872, baseEnd_252872] using wordTrace_append hprefix tailTrace_252872
  have hstable : (prefixWord ++ tailWord_252872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252872).length < 2 ^ (prefixWord ++ tailWord_252872).sum := by decide
  have hdescent : baseEnd_252872 < baseStart_252872 := by decide
  rcases family_descends (prefixWord ++ tailWord_252872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252876 : List Nat := [2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_252876 : Nat := 118140960795 + 252876 * 2 ^ 59
def prefixEnd_252876 : Nat := 4983230072969 + 3 ^ 40 * 252876 * 2
def baseEnd_252876 : Nat := 76946331251234284555289

theorem tailTrace_252876 : CollatzResearch.WordTrace tailWord_252876 prefixEnd_252876 76946331251234284555289 := by
  unfold tailWord_252876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611572715940457313777241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6148763621253943085036321 4611572715940457313777241)
  ·
    refine ⟨3458679536955342985332931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611572715940457313777241 3458679536955342985332931)
    ·
      refine ⟨5188019305433014477999397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458679536955342985332931 5188019305433014477999397)
      ·
        refine ⟨972753619768690214624887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5188019305433014477999397 972753619768690214624887)
        ·
          refine ⟨1459130429653035321937331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972753619768690214624887 1459130429653035321937331)
          ·
            refine ⟨2188695644479552982905997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459130429653035321937331 2188695644479552982905997)
            ·
              refine ⟨820760866679832368589749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2188695644479552982905997 820760866679832368589749)
              ·
                refine ⟨76946331251234284555289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820760866679832368589749 76946331251234284555289)
                ·
                  rfl

theorem cell19_252876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_252876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252876 prefixEnd_252876 := by exact prefixLift 252876
  have htrace : WordTrace (prefixWord ++ tailWord_252876) baseStart_252876 baseEnd_252876 := by
    simpa [prefixWord, tailWord_252876, baseEnd_252876] using wordTrace_append hprefix tailTrace_252876
  have hstable : (prefixWord ++ tailWord_252876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252876).length < 2 ^ (prefixWord ++ tailWord_252876).sum := by decide
  have hdescent : baseEnd_252876 < baseStart_252876 := by decide
  rcases family_descends (prefixWord ++ tailWord_252876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252893 : List Nat := [1, 4, 3, 1, 2, 3, 5]
def baseStart_252893 : Nat := 118140960795 + 252893 * 2 ^ 59
def prefixEnd_252893 : Nat := 4983230072969 + 3 ^ 40 * 252893 * 2
def baseEnd_252893 : Nat := 25650501364461094059155

theorem tailTrace_252893 : CollatzResearch.WordTrace tailWord_252893 prefixEnd_252893 25650501364461094059155 := by
  unfold tailWord_252893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223765472819326530923333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6149176981879551020615555 9223765472819326530923333)
  ·
    refine ⟨1729456026153623724548125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9223765472819326530923333 1729456026153623724548125)
    ·
      refine ⟨648546009807608896705547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1729456026153623724548125 648546009807608896705547)
      ·
        refine ⟨972819014711413345058321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648546009807608896705547 972819014711413345058321)
        ·
          refine ⟨729614261033560008793741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972819014711413345058321 729614261033560008793741)
          ·
            refine ⟨273605347887585003297653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729614261033560008793741 273605347887585003297653)
            ·
              refine ⟨25650501364461094059155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273605347887585003297653 25650501364461094059155)
              ·
                rfl

theorem cell19_252893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_252893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252893 prefixEnd_252893 := by exact prefixLift 252893
  have htrace : WordTrace (prefixWord ++ tailWord_252893) baseStart_252893 baseEnd_252893 := by
    simpa [prefixWord, tailWord_252893, baseEnd_252893] using wordTrace_append hprefix tailTrace_252893
  have hstable : (prefixWord ++ tailWord_252893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252893).length < 2 ^ (prefixWord ++ tailWord_252893).sum := by decide
  have hdescent : baseEnd_252893 < baseStart_252893 := by decide
  rcases family_descends (prefixWord ++ tailWord_252893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252946 : List Nat := [3, 2, 5, 1, 2, 6]
def baseStart_252946 : Nat := 118140960795 + 252946 * 2 ^ 59
def prefixEnd_252946 : Nat := 4983230072969 + 3 ^ 40 * 252946 * 2
def baseEnd_252946 : Nat := 8551959021054984777727

theorem tailTrace_252946 : CollatzResearch.WordTrace tailWord_252946 prefixEnd_252946 8551959021054984777727 := by
  unfold tailWord_252946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306424635406829145650673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6150465694418211055068461 2306424635406829145650673)
  ·
    refine ⟨1729818476555121859238005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2306424635406829145650673 1729818476555121859238005)
    ·
      refine ⟨162170482177042674303563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1729818476555121859238005 162170482177042674303563)
      ·
        refine ⟨243255723265564011455345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162170482177042674303563 243255723265564011455345)
        ·
          refine ⟨182441792449173008591509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243255723265564011455345 182441792449173008591509)
          ·
            refine ⟨8551959021054984777727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182441792449173008591509 8551959021054984777727)
            ·
              rfl

theorem cell19_252946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_252946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252946 prefixEnd_252946 := by exact prefixLift 252946
  have htrace : WordTrace (prefixWord ++ tailWord_252946) baseStart_252946 baseEnd_252946 := by
    simpa [prefixWord, tailWord_252946, baseEnd_252946] using wordTrace_append hprefix tailTrace_252946
  have hstable : (prefixWord ++ tailWord_252946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252946).length < 2 ^ (prefixWord ++ tailWord_252946).sum := by decide
  have hdescent : baseEnd_252946 < baseStart_252946 := by decide
  rcases family_descends (prefixWord ++ tailWord_252946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252967 : List Nat := [1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_252967 : Nat := 118140960795 + 252967 * 2 ^ 59
def prefixEnd_252967 : Nat := 4983230072969 + 3 ^ 40 * 252967 * 2
def baseEnd_252967 : Nat := 76974021170973036532819

theorem tailTrace_252967 : CollatzResearch.WordTrace tailWord_252967 prefixEnd_252967 76974021170973036532819 := by
  unfold tailWord_252967
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226464474551237169117155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6150976316367491446078103 9226464474551237169117155)
  ·
    refine ⟨13839696711826855753675733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226464474551237169117155 13839696711826855753675733)
    ·
      refine ⟨324367891683441931726775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13839696711826855753675733 324367891683441931726775)
      ·
        refine ⟨486551837525162897590163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324367891683441931726775 486551837525162897590163)
        ·
          refine ⟨729827756287744346385245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486551837525162897590163 729827756287744346385245)
          ·
            refine ⟨273685408607904129894467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729827756287744346385245 273685408607904129894467)
            ·
              refine ⟨410528112911856194841701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273685408607904129894467 410528112911856194841701)
              ·
                refine ⟨76974021170973036532819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410528112911856194841701 76974021170973036532819)
                ·
                  rfl

theorem cell19_252967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_252967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252967 prefixEnd_252967 := by exact prefixLift 252967
  have htrace : WordTrace (prefixWord ++ tailWord_252967) baseStart_252967 baseEnd_252967 := by
    simpa [prefixWord, tailWord_252967, baseEnd_252967] using wordTrace_append hprefix tailTrace_252967
  have hstable : (prefixWord ++ tailWord_252967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252967).length < 2 ^ (prefixWord ++ tailWord_252967).sum := by decide
  have hdescent : baseEnd_252967 < baseStart_252967 := by decide
  rcases family_descends (prefixWord ++ tailWord_252967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252988 : List Nat := [2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_252988 : Nat := 118140960795 + 252988 * 2 ^ 59
def prefixEnd_252988 : Nat := 4983230072969 + 3 ^ 40 * 252988 * 2
def baseEnd_252988 : Nat := 76980411152451210066095

theorem tailTrace_252988 : CollatzResearch.WordTrace tailWord_252988 prefixEnd_252988 76980411152451210066095 := by
  unfold tailWord_252988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613615203737578877815809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6151486938316771837087745 4613615203737578877815809)
  ·
    refine ⟨3460211402803184158361857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4613615203737578877815809 3460211402803184158361857)
    ·
      refine ⟨2595158552102388118771393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3460211402803184158361857 2595158552102388118771393)
      ·
        refine ⟨1946368914076791089078545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595158552102388118771393 1946368914076791089078545)
        ·
          refine ⟨1459776685557593316808909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946368914076791089078545 1459776685557593316808909)
          ·
            refine ⟨547416257084097493803341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1459776685557593316808909 547416257084097493803341)
            ·
              refine ⟨205281096406536560176253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547416257084097493803341 205281096406536560176253)
              ·
                refine ⟨76980411152451210066095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205281096406536560176253 76980411152451210066095)
                ·
                  rfl

theorem cell19_252988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_252988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_252988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_252988 prefixEnd_252988 := by exact prefixLift 252988
  have htrace : WordTrace (prefixWord ++ tailWord_252988) baseStart_252988 baseEnd_252988 := by
    simpa [prefixWord, tailWord_252988, baseEnd_252988] using wordTrace_append hprefix tailTrace_252988
  have hstable : (prefixWord ++ tailWord_252988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252988).length < 2 ^ (prefixWord ++ tailWord_252988).sum := by decide
  have hdescent : baseEnd_252988 < baseStart_252988 := by decide
  rcases family_descends (prefixWord ++ tailWord_252988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253064 : List Nat := [2, 1, 3, 4, 2, 2, 5]
def baseStart_253064 : Nat := 118140960795 + 253064 * 2 ^ 59
def prefixEnd_253064 : Nat := 4983230072969 + 3 ^ 40 * 253064 * 2
def baseEnd_253064 : Nat := 25667845599901850792333

theorem tailTrace_253064 : CollatzResearch.WordTrace tailWord_253064 prefixEnd_253064 25667845599901850792333 := by
  unfold tailWord_253064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615001177599911367699123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6153334903466548490265497 4615001177599911367699123)
  ·
    refine ⟨6922501766399867051548685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615001177599911367699123 6922501766399867051548685)
    ·
      refine ⟨2595938162399950144330757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6922501766399867051548685 2595938162399950144330757)
      ·
        refine ⟨486738405449990652062017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2595938162399950144330757 486738405449990652062017)
        ·
          refine ⟨365053804087492989046513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486738405449990652062017 365053804087492989046513)
          ·
            refine ⟨273790353065619741784885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365053804087492989046513 273790353065619741784885)
            ·
              refine ⟨25667845599901850792333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273790353065619741784885 25667845599901850792333)
              ·
                rfl

theorem cell19_253064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_253064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253064 prefixEnd_253064 := by exact prefixLift 253064
  have htrace : WordTrace (prefixWord ++ tailWord_253064) baseStart_253064 baseEnd_253064 := by
    simpa [prefixWord, tailWord_253064, baseEnd_253064] using wordTrace_append hprefix tailTrace_253064
  have hstable : (prefixWord ++ tailWord_253064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253064).length < 2 ^ (prefixWord ++ tailWord_253064).sum := by decide
  have hdescent : baseEnd_253064 < baseStart_253064 := by decide
  rcases family_descends (prefixWord ++ tailWord_253064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253085 : List Nat := [1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_253085 : Nat := 118140960795 + 253085 * 2 ^ 59
def prefixEnd_253085 : Nat := 4983230072969 + 3 ^ 40 * 253085 * 2
def baseEnd_253085 : Nat := 77009926781183725910275

theorem tailTrace_253085 : CollatzResearch.WordTrace tailWord_253085 prefixEnd_253085 77009926781183725910275 := by
  unfold tailWord_253085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230768288123743321912709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6153845525415828881275139 9230768288123743321912709)
  ·
    refine ⟨1730769054023201872858633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9230768288123743321912709 1730769054023201872858633)
    ·
      refine ⟨1298076790517401404643975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730769054023201872858633 1298076790517401404643975)
      ·
        refine ⟨1947115185776102106965963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298076790517401404643975 1947115185776102106965963)
        ·
          refine ⟨2920672778664153160448945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947115185776102106965963 2920672778664153160448945)
          ·
            refine ⟨2190504583998114870336709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920672778664153160448945 2190504583998114870336709)
            ·
              refine ⟨410719609499646538188133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2190504583998114870336709 410719609499646538188133)
              ·
                refine ⟨77009926781183725910275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410719609499646538188133 77009926781183725910275)
                ·
                  rfl

theorem cell19_253085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_253085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253085 prefixEnd_253085 := by exact prefixLift 253085
  have htrace : WordTrace (prefixWord ++ tailWord_253085) baseStart_253085 baseEnd_253085 := by
    simpa [prefixWord, tailWord_253085, baseEnd_253085] using wordTrace_append hprefix tailTrace_253085
  have hstable : (prefixWord ++ tailWord_253085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253085).length < 2 ^ (prefixWord ++ tailWord_253085).sum := by decide
  have hdescent : baseEnd_253085 < baseStart_253085 := by decide
  rcases family_descends (prefixWord ++ tailWord_253085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253180 : List Nat := [2, 2, 2, 1, 5, 1, 6]
def baseStart_253180 : Nat := 118140960795 + 253180 * 2 ^ 59
def prefixEnd_253180 : Nat := 4983230072969 + 3 ^ 40 * 253180 * 2
def baseEnd_253180 : Nat := 25679611280083884599635

theorem tailTrace_253180 : CollatzResearch.WordTrace tailWord_253180 prefixEnd_253180 25679611280083884599635 := by
  unfold tailWord_253180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617116611389787273310497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6156155481853049697747329 4617116611389787273310497)
  ·
    refine ⟨3462837458542340454982873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617116611389787273310497 3462837458542340454982873)
    ·
      refine ⟨2597128093906755341237155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462837458542340454982873 2597128093906755341237155)
      ·
        refine ⟨3895692140860133011855733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597128093906755341237155 3895692140860133011855733)
        ·
          refine ⟨365221138205637469861475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3895692140860133011855733 365221138205637469861475)
          ·
            refine ⟨547831707308456204792213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365221138205637469861475 547831707308456204792213)
            ·
              refine ⟨25679611280083884599635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 547831707308456204792213 25679611280083884599635)
              ·
                rfl

theorem cell19_253180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_253180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253180 prefixEnd_253180 := by exact prefixLift 253180
  have htrace : WordTrace (prefixWord ++ tailWord_253180) baseStart_253180 baseEnd_253180 := by
    simpa [prefixWord, tailWord_253180, baseEnd_253180] using wordTrace_append hprefix tailTrace_253180
  have hstable : (prefixWord ++ tailWord_253180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253180).length < 2 ^ (prefixWord ++ tailWord_253180).sum := by decide
  have hdescent : baseEnd_253180 < baseStart_253180 := by decide
  rcases family_descends (prefixWord ++ tailWord_253180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253201 : List Nat := [1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_253201 : Nat := 118140960795 + 253201 * 2 ^ 59
def prefixEnd_253201 : Nat := 4983230072969 + 3 ^ 40 * 253201 * 2
def baseEnd_253201 : Nat := 77045223821729827332181

theorem tailTrace_253201 : CollatzResearch.WordTrace tailWord_253201 prefixEnd_253201 77045223821729827332181 := by
  unfold tailWord_253201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234999155703495133135457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6156666103802330088756971 9234999155703495133135457)
  ·
    refine ⟨6926249366777621349851593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9234999155703495133135457 6926249366777621349851593)
    ·
      refine ⟨5194687025083216012388695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6926249366777621349851593 5194687025083216012388695)
      ·
        refine ⟨7792030537624824018583043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194687025083216012388695 7792030537624824018583043)
        ·
          refine ⟨11688045806437236027874565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792030537624824018583043 11688045806437236027874565)
          ·
            refine ⟨2191508588706981755226481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11688045806437236027874565 2191508588706981755226481)
            ·
              refine ⟨1643631441530236316419861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191508588706981755226481 1643631441530236316419861)
              ·
                refine ⟨77045223821729827332181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1643631441530236316419861 77045223821729827332181)
                ·
                  rfl

theorem cell19_253201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_253201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253201 prefixEnd_253201 := by exact prefixLift 253201
  have htrace : WordTrace (prefixWord ++ tailWord_253201) baseStart_253201 baseEnd_253201 := by
    simpa [prefixWord, tailWord_253201, baseEnd_253201] using wordTrace_append hprefix tailTrace_253201
  have hstable : (prefixWord ++ tailWord_253201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253201).length < 2 ^ (prefixWord ++ tailWord_253201).sum := by decide
  have hdescent : baseEnd_253201 < baseStart_253201 := by decide
  rcases family_descends (prefixWord ++ tailWord_253201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253214 : List Nat := [4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_253214 : Nat := 118140960795 + 253214 * 2 ^ 59
def prefixEnd_253214 : Nat := 4983230072969 + 3 ^ 40 * 253214 * 2
def baseEnd_253214 : Nat := 77049179524549649043257

theorem tailTrace_253214 : CollatzResearch.WordTrace tailWord_253214 prefixEnd_253214 77049179524549649043257 := by
  unfold tailWord_253214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154434163082049794169837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6156982203104265568905797 1154434163082049794169837)
  ·
    refine ⟨432912811155768672813689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1154434163082049794169837 432912811155768672813689)
    ·
      refine ⟨324684608366826504610267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432912811155768672813689 324684608366826504610267)
      ·
        refine ⟨487026912550239756915401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324684608366826504610267 487026912550239756915401)
        ·
          refine ⟨365270184412679817686551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487026912550239756915401 365270184412679817686551)
          ·
            refine ⟨547905276619019726529827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365270184412679817686551 547905276619019726529827)
            ·
              refine ⟨821857914928529589794741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547905276619019726529827 821857914928529589794741)
              ·
                refine ⟨77049179524549649043257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 821857914928529589794741 77049179524549649043257)
                ·
                  rfl

theorem cell19_253214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_253214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253214 prefixEnd_253214 := by exact prefixLift 253214
  have htrace : WordTrace (prefixWord ++ tailWord_253214) baseStart_253214 baseEnd_253214 := by
    simpa [prefixWord, tailWord_253214, baseEnd_253214] using wordTrace_append hprefix tailTrace_253214
  have hstable : (prefixWord ++ tailWord_253214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253214).length < 2 ^ (prefixWord ++ tailWord_253214).sum := by decide
  have hdescent : baseEnd_253214 < baseStart_253214 := by decide
  rcases family_descends (prefixWord ++ tailWord_253214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253237 : List Nat := [1, 3, 3, 1, 2, 4, 5]
def baseStart_253237 : Nat := 118140960795 + 253237 * 2 ^ 59
def prefixEnd_253237 : Nat := 4983230072969 + 3 ^ 40 * 253237 * 2
def baseEnd_253237 : Nat := 25685392691897470177361

theorem tailTrace_253237 : CollatzResearch.WordTrace tailWord_253237 prefixEnd_253237 25685392691897470177361 := by
  unfold tailWord_253237
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236312183573073281445965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6157541455715382187630643 9236312183573073281445965)
  ·
    refine ⟨3463617068839902480542237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9236312183573073281445965 3463617068839902480542237)
    ·
      refine ⟨1298856400814963430203339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3463617068839902480542237 1298856400814963430203339)
      ·
        refine ⟨1948284601222445145305009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298856400814963430203339 1948284601222445145305009)
        ·
          refine ⟨1461213450916833858978757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948284601222445145305009 1461213450916833858978757)
          ·
            refine ⟨273977522046906348558517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1461213450916833858978757 273977522046906348558517)
            ·
              refine ⟨25685392691897470177361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273977522046906348558517 25685392691897470177361)
              ·
                rfl

theorem cell19_253237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_253237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253237 prefixEnd_253237 := by exact prefixLift 253237
  have htrace : WordTrace (prefixWord ++ tailWord_253237) baseStart_253237 baseEnd_253237 := by
    simpa [prefixWord, tailWord_253237, baseEnd_253237] using wordTrace_append hprefix tailTrace_253237
  have hstable : (prefixWord ++ tailWord_253237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253237).length < 2 ^ (prefixWord ++ tailWord_253237).sum := by decide
  have hdescent : baseEnd_253237 < baseStart_253237 := by decide
  rcases family_descends (prefixWord ++ tailWord_253237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253294 : List Nat := [4, 1, 2, 4, 8]
def baseStart_253294 : Nat := 118140960795 + 253294 * 2 ^ 59
def prefixEnd_253294 : Nat := 4983230072969 + 3 ^ 40 * 253294 * 2
def baseEnd_253294 : Nat := 2854574900412339528343

theorem tailTrace_253294 : CollatzResearch.WordTrace tailWord_253294 prefixEnd_253294 2854574900412339528343 := by
  unfold tailWord_253294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154798893045821502033867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6158927429577714677513957 1154798893045821502033867)
  ·
    refine ⟨1732198339568732253050801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1154798893045821502033867 1732198339568732253050801)
    ·
      refine ⟨1299148754676549189788101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732198339568732253050801 1299148754676549189788101)
      ·
        refine ⟨243590391501852973085269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1299148754676549189788101 243590391501852973085269)
        ·
          refine ⟨2854574900412339528343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 243590391501852973085269 2854574900412339528343)
          ·
            rfl

theorem cell19_253294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_253294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253294 prefixEnd_253294 := by exact prefixLift 253294
  have htrace : WordTrace (prefixWord ++ tailWord_253294) baseStart_253294 baseEnd_253294 := by
    simpa [prefixWord, tailWord_253294, baseEnd_253294] using wordTrace_append hprefix tailTrace_253294
  have hstable : (prefixWord ++ tailWord_253294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253294).length < 2 ^ (prefixWord ++ tailWord_253294).sum := by decide
  have hdescent : baseEnd_253294 < baseStart_253294 := by decide
  rcases family_descends (prefixWord ++ tailWord_253294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253448 : List Nat := [2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_253448 : Nat := 118140960795 + 253448 * 2 ^ 59
def prefixEnd_253448 : Nat := 4983230072969 + 3 ^ 40 * 253448 * 2
def baseEnd_253448 : Nat := 77120382175306439842619

theorem tailTrace_253448 : CollatzResearch.WordTrace tailWord_253448 prefixEnd_253448 77120382175306439842619 := by
  unfold tailWord_253448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622003992904328158688499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6162671990539104211584665 4622003992904328158688499)
  ·
    refine ⟨6933005989356492238032749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622003992904328158688499 6933005989356492238032749)
    ·
      refine ⟨2599877246008684589262281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6933005989356492238032749 2599877246008684589262281)
      ·
        refine ⟨1949907934506513441946711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2599877246008684589262281 1949907934506513441946711)
        ·
          refine ⟨2924861901759770162920067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949907934506513441946711 2924861901759770162920067)
          ·
            refine ⟨4387292852639655244380101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924861901759770162920067 4387292852639655244380101)
            ·
              refine ⟨822617409869935358321269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4387292852639655244380101 822617409869935358321269)
              ·
                refine ⟨77120382175306439842619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 822617409869935358321269 77120382175306439842619)
                ·
                  rfl

theorem cell19_253448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_253448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253448 prefixEnd_253448 := by exact prefixLift 253448
  have htrace : WordTrace (prefixWord ++ tailWord_253448) baseStart_253448 baseEnd_253448 := by
    simpa [prefixWord, tailWord_253448, baseEnd_253448] using wordTrace_append hprefix tailTrace_253448
  have hstable : (prefixWord ++ tailWord_253448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253448).length < 2 ^ (prefixWord ++ tailWord_253448).sum := by decide
  have hdescent : baseEnd_253448 < baseStart_253448 := by decide
  rcases family_descends (prefixWord ++ tailWord_253448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253480 : List Nat := [2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_253480 : Nat := 118140960795 + 253480 * 2 ^ 59
def prefixEnd_253480 : Nat := 4983230072969 + 3 ^ 40 * 253480 * 2
def baseEnd_253480 : Nat := 77130119289939847131421

theorem tailTrace_253480 : CollatzResearch.WordTrace tailWord_253480 prefixEnd_253480 77130119289939847131421 := by
  unfold tailWord_253480
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622587560846362891270947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6163450081128483855027929 4622587560846362891270947)
  ·
    refine ⟨6933881341269544336906421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622587560846362891270947 6933881341269544336906421)
    ·
      refine ⟨650051375744019781584977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6933881341269544336906421 650051375744019781584977)
      ·
        refine ⟨487538531808014836188733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650051375744019781584977 487538531808014836188733)
        ·
          refine ⟨182826949428005563570775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487538531808014836188733 182826949428005563570775)
          ·
            refine ⟨274240424142008345356163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182826949428005563570775 274240424142008345356163)
            ·
              refine ⟨411360636213012518034245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274240424142008345356163 411360636213012518034245)
              ·
                refine ⟨77130119289939847131421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411360636213012518034245 77130119289939847131421)
                ·
                  rfl

theorem cell19_253480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_253480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253480 prefixEnd_253480 := by exact prefixLift 253480
  have htrace : WordTrace (prefixWord ++ tailWord_253480) baseStart_253480 baseEnd_253480 := by
    simpa [prefixWord, tailWord_253480, baseEnd_253480] using wordTrace_append hprefix tailTrace_253480
  have hstable : (prefixWord ++ tailWord_253480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253480).length < 2 ^ (prefixWord ++ tailWord_253480).sum := by decide
  have hdescent : baseEnd_253480 < baseStart_253480 := by decide
  rcases family_descends (prefixWord ++ tailWord_253480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253501 : List Nat := [1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_253501 : Nat := 118140960795 + 253501 * 2 ^ 59
def prefixEnd_253501 : Nat := 4983230072969 + 3 ^ 40 * 253501 * 2
def baseEnd_253501 : Nat := 77136509271418020664697

theorem tailTrace_253501 : CollatzResearch.WordTrace tailWord_253501 prefixEnd_253501 77136509271418020664697 := by
  unfold tailWord_253501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245941054616646369056357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6163960703077764246037571 9245941054616646369056357)
  ·
    refine ⟨1733613947740621194198067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9245941054616646369056357 1733613947740621194198067)
    ·
      refine ⟨2600420921610931791297101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733613947740621194198067 2600420921610931791297101)
      ·
        refine ⟨975157845604099421736413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2600420921610931791297101 975157845604099421736413)
        ·
          refine ⟨365684192101537283151155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 975157845604099421736413 365684192101537283151155)
          ·
            refine ⟨548526288152305924726733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365684192101537283151155 548526288152305924726733)
            ·
              refine ⟨205697358057114721772525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548526288152305924726733 205697358057114721772525)
              ·
                refine ⟨77136509271418020664697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205697358057114721772525 77136509271418020664697)
                ·
                  rfl

theorem cell19_253501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_253501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253501 prefixEnd_253501 := by exact prefixLift 253501
  have htrace : WordTrace (prefixWord ++ tailWord_253501) baseStart_253501 baseEnd_253501 := by
    simpa [prefixWord, tailWord_253501, baseEnd_253501] using wordTrace_append hprefix tailTrace_253501
  have hstable : (prefixWord ++ tailWord_253501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253501).length < 2 ^ (prefixWord ++ tailWord_253501).sum := by decide
  have hdescent : baseEnd_253501 < baseStart_253501 := by decide
  rcases family_descends (prefixWord ++ tailWord_253501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253503 : List Nat := [1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_253503 : Nat := 118140960795 + 253503 * 2 ^ 59
def prefixEnd_253503 : Nat := 4983230072969 + 3 ^ 40 * 253503 * 2
def baseEnd_253503 : Nat := 77137117841082608620247

theorem tailTrace_253503 : CollatzResearch.WordTrace tailWord_253503 prefixEnd_253503 77137117841082608620247 := by
  unfold tailWord_253503
  simp only [CollatzResearch.WordTrace]
  refine ⟨9246014000609400710629163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6164009333739600473752775 9246014000609400710629163)
  ·
    refine ⟨13869021000914101065943745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9246014000609400710629163 13869021000914101065943745)
    ·
      refine ⟨10401765750685575799457809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13869021000914101065943745 10401765750685575799457809)
      ·
        refine ⟨7801324313014181849593357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401765750685575799457809 7801324313014181849593357)
        ·
          refine ⟨2925496617380318193597509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7801324313014181849593357 2925496617380318193597509)
          ·
            refine ⟨548530615758809661299533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2925496617380318193597509 548530615758809661299533)
            ·
              refine ⟨205698980909553622987325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548530615758809661299533 205698980909553622987325)
              ·
                refine ⟨77137117841082608620247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205698980909553622987325 77137117841082608620247)
                ·
                  rfl

theorem cell19_253503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_253503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253503 prefixEnd_253503 := by exact prefixLift 253503
  have htrace : WordTrace (prefixWord ++ tailWord_253503) baseStart_253503 baseEnd_253503 := by
    simpa [prefixWord, tailWord_253503, baseEnd_253503] using wordTrace_append hprefix tailTrace_253503
  have hstable : (prefixWord ++ tailWord_253503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253503).length < 2 ^ (prefixWord ++ tailWord_253503).sum := by decide
  have hdescent : baseEnd_253503 < baseStart_253503 := by decide
  rcases family_descends (prefixWord ++ tailWord_253503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253524 : List Nat := [2, 4, 1, 1, 1, 2, 8]
def baseStart_253524 : Nat := 118140960795 + 253524 * 2 ^ 59
def prefixEnd_253524 : Nat := 4983230072969 + 3 ^ 40 * 253524 * 2
def baseEnd_253524 : Nat := 25714502607520260717841

theorem tailTrace_253524 : CollatzResearch.WordTrace tailWord_253524 prefixEnd_253524 25714502607520260717841 := by
  unfold tailWord_253524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623389966766660648571813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6164519955688880864762417 4623389966766660648571813)
  ·
    refine ⟨866885618768748871607215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4623389966766660648571813 866885618768748871607215)
    ·
      refine ⟨1300328428153123307410823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866885618768748871607215 1300328428153123307410823)
      ·
        refine ⟨1950492642229684961116235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300328428153123307410823 1950492642229684961116235)
        ·
          refine ⟨2925738963344527441674353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950492642229684961116235 2925738963344527441674353)
          ·
            refine ⟨2194304222508395581255765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2925738963344527441674353 2194304222508395581255765)
            ·
              refine ⟨25714502607520260717841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2194304222508395581255765 25714502607520260717841)
              ·
                rfl

theorem cell19_253524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_253524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253524 prefixEnd_253524 := by exact prefixLift 253524
  have htrace : WordTrace (prefixWord ++ tailWord_253524) baseStart_253524 baseEnd_253524 := by
    simpa [prefixWord, tailWord_253524, baseEnd_253524] using wordTrace_append hprefix tailTrace_253524
  have hstable : (prefixWord ++ tailWord_253524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253524).length < 2 ^ (prefixWord ++ tailWord_253524).sum := by decide
  have hdescent : baseEnd_253524 < baseStart_253524 := by decide
  rcases family_descends (prefixWord ++ tailWord_253524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253558 : List Nat := [5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_253558 : Nat := 118140960795 + 253558 * 2 ^ 59
def prefixEnd_253558 : Nat := 4983230072969 + 3 ^ 40 * 253558 * 2
def baseEnd_253558 : Nat := 77153853506858777397875

theorem tailTrace_253558 : CollatzResearch.WordTrace tailWord_253558 prefixEnd_253558 77153853506858777397875 := by
  unfold tailWord_253558
  simp only [CollatzResearch.WordTrace]
  refine ⟨578001250963134068992583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6165346676940096735920885 578001250963134068992583)
  ·
    refine ⟨867001876444701103488875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 578001250963134068992583 867001876444701103488875)
    ·
      refine ⟨1300502814667051655233313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867001876444701103488875 1300502814667051655233313)
      ·
        refine ⟨975377111000288741424985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300502814667051655233313 975377111000288741424985)
        ·
          refine ⟨731532833250216556068739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975377111000288741424985 731532833250216556068739)
          ·
            refine ⟨1097299249875324834103109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731532833250216556068739 1097299249875324834103109)
            ·
              refine ⟨205743609351623406394333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1097299249875324834103109 205743609351623406394333)
              ·
                refine ⟨77153853506858777397875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205743609351623406394333 77153853506858777397875)
                ·
                  rfl

theorem cell19_253558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_253558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253558 prefixEnd_253558 := by exact prefixLift 253558
  have htrace : WordTrace (prefixWord ++ tailWord_253558) baseStart_253558 baseEnd_253558 := by
    simpa [prefixWord, tailWord_253558, baseEnd_253558] using wordTrace_append hprefix tailTrace_253558
  have hstable : (prefixWord ++ tailWord_253558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253558).length < 2 ^ (prefixWord ++ tailWord_253558).sum := by decide
  have hdescent : baseEnd_253558 < baseStart_253558 := by decide
  rcases family_descends (prefixWord ++ tailWord_253558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253598 : List Nat := [4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_253598 : Nat := 118140960795 + 253598 * 2 ^ 59
def prefixEnd_253598 : Nat := 4983230072969 + 3 ^ 40 * 253598 * 2
def baseEnd_253598 : Nat := 77166024900150536508877

theorem tailTrace_253598 : CollatzResearch.WordTrace tailWord_253598 prefixEnd_253598 77166024900150536508877 := by
  unfold tailWord_253598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156184866908153991917181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6166319290176821290224965 1156184866908153991917181)
  ·
    refine ⟨433569325090557746968943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1156184866908153991917181 433569325090557746968943)
    ·
      refine ⟨650353987635836620453415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433569325090557746968943 650353987635836620453415)
      ·
        refine ⟨975530981453754930680123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650353987635836620453415 975530981453754930680123)
        ·
          refine ⟨1463296472180632396020185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975530981453754930680123 1463296472180632396020185)
          ·
            refine ⟨1097472354135474297015139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463296472180632396020185 1097472354135474297015139)
            ·
              refine ⟨1646208531203211445522709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097472354135474297015139 1646208531203211445522709)
              ·
                refine ⟨77166024900150536508877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1646208531203211445522709 77166024900150536508877)
                ·
                  rfl

theorem cell19_253598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_253598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253598 prefixEnd_253598 := by exact prefixLift 253598
  have htrace : WordTrace (prefixWord ++ tailWord_253598) baseStart_253598 baseEnd_253598 := by
    simpa [prefixWord, tailWord_253598, baseEnd_253598] using wordTrace_append hprefix tailTrace_253598
  have hstable : (prefixWord ++ tailWord_253598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253598).length < 2 ^ (prefixWord ++ tailWord_253598).sum := by decide
  have hdescent : baseEnd_253598 < baseStart_253598 := by decide
  rcases family_descends (prefixWord ++ tailWord_253598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253600 : List Nat := [2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_253600 : Nat := 118140960795 + 253600 * 2 ^ 59
def prefixEnd_253600 : Nat := 4983230072969 + 3 ^ 40 * 253600 * 2
def baseEnd_253600 : Nat := 77166633469815124464427

theorem tailTrace_253600 : CollatzResearch.WordTrace tailWord_253600 prefixEnd_253600 77166633469815124464427 := by
  unfold tailWord_253600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624775940628993138455127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6166367920838657517940169 4624775940628993138455127)
  ·
    refine ⟨6937163910943489707682691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624775940628993138455127 6937163910943489707682691)
    ·
      refine ⟨10405745866415234561524037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937163910943489707682691 10405745866415234561524037)
      ·
        refine ⟨1951077349952856480285757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10405745866415234561524037 1951077349952856480285757)
        ·
          refine ⟨731654006232321180107159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1951077349952856480285757 731654006232321180107159)
          ·
            refine ⟨1097481009348481770160739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731654006232321180107159 1097481009348481770160739)
            ·
              refine ⟨1646221514022722655241109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097481009348481770160739 1646221514022722655241109)
              ·
                refine ⟨77166633469815124464427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1646221514022722655241109 77166633469815124464427)
                ·
                  rfl

theorem cell19_253600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_253600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253600 prefixEnd_253600 := by exact prefixLift 253600
  have htrace : WordTrace (prefixWord ++ tailWord_253600) baseStart_253600 baseEnd_253600 := by
    simpa [prefixWord, tailWord_253600, baseEnd_253600] using wordTrace_append hprefix tailTrace_253600
  have hstable : (prefixWord ++ tailWord_253600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253600).length < 2 ^ (prefixWord ++ tailWord_253600).sum := by decide
  have hdescent : baseEnd_253600 < baseStart_253600 := by decide
  rcases family_descends (prefixWord ++ tailWord_253600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253634 : List Nat := [3, 5, 1, 2, 8]
def baseStart_253634 : Nat := 118140960795 + 253634 * 2 ^ 59
def prefixEnd_253634 : Nat := 4983230072969 + 3 ^ 40 * 253634 * 2
def baseEnd_253634 : Nat := 2858406635337522952177

theorem tailTrace_253634 : CollatzResearch.WordTrace tailWord_253634 prefixEnd_253634 2858406635337522952177 := by
  unfold tailWord_253634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312697990783702520911989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6167194642089873389098637 2312697990783702520911989)
  ·
    refine ⟨216815436635972111335499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2312697990783702520911989 216815436635972111335499)
    ·
      refine ⟨325223154953958167003249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216815436635972111335499 325223154953958167003249)
      ·
        refine ⟨243917366215468625252437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325223154953958167003249 243917366215468625252437)
        ·
          refine ⟨2858406635337522952177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 243917366215468625252437 2858406635337522952177)
          ·
            rfl

theorem cell19_253634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_253634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253634 prefixEnd_253634 := by exact prefixLift 253634
  have htrace : WordTrace (prefixWord ++ tailWord_253634) baseStart_253634 baseEnd_253634 := by
    simpa [prefixWord, tailWord_253634, baseEnd_253634] using wordTrace_append hprefix tailTrace_253634
  have hstable : (prefixWord ++ tailWord_253634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253634).length < 2 ^ (prefixWord ++ tailWord_253634).sum := by decide
  have hdescent : baseEnd_253634 < baseStart_253634 := by decide
  rcases family_descends (prefixWord ++ tailWord_253634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253657 : List Nat := [1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_253657 : Nat := 118140960795 + 253657 * 2 ^ 59
def prefixEnd_253657 : Nat := 4983230072969 + 3 ^ 40 * 253657 * 2
def baseEnd_253657 : Nat := 77183977705255881197605

theorem tailTrace_253657 : CollatzResearch.WordTrace tailWord_253657 prefixEnd_253657 77183977705255881197605 := by
  unfold tailWord_253657
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251630842051485011735225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6167753894700990007823483 9251630842051485011735225)
  ·
    refine ⟨6938723131538613758801419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9251630842051485011735225 6938723131538613758801419)
    ·
      refine ⟨10408084697307920638202129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938723131538613758801419 10408084697307920638202129)
      ·
        refine ⟨7806063522980940478651597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10408084697307920638202129 7806063522980940478651597)
        ·
          refine ⟨2927273821117852679494349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7806063522980940478651597 2927273821117852679494349)
          ·
            refine ⟨1097727682919194754810381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2927273821117852679494349 1097727682919194754810381)
            ·
              refine ⟨411647881094698033053893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097727682919194754810381 411647881094698033053893)
              ·
                refine ⟨77183977705255881197605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411647881094698033053893 77183977705255881197605)
                ·
                  rfl

theorem cell19_253657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_253657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253657 prefixEnd_253657 := by exact prefixLift 253657
  have htrace : WordTrace (prefixWord ++ tailWord_253657) baseStart_253657 baseEnd_253657 := by
    simpa [prefixWord, tailWord_253657, baseEnd_253657] using wordTrace_append hprefix tailTrace_253657
  have hstable : (prefixWord ++ tailWord_253657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253657).length < 2 ^ (prefixWord ++ tailWord_253657).sum := by decide
  have hdescent : baseEnd_253657 < baseStart_253657 := by decide
  rcases family_descends (prefixWord ++ tailWord_253657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253733 : List Nat := [1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_253733 : Nat := 118140960795 + 253733 * 2 ^ 59
def prefixEnd_253733 : Nat := 4983230072969 + 3 ^ 40 * 253733 * 2
def baseEnd_253733 : Nat := 77207103352510223508509

theorem tailTrace_253733 : CollatzResearch.WordTrace tailWord_253733 prefixEnd_253733 77207103352510223508509 := by
  unfold tailWord_253733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254402789776149991501853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169601859850766661001235 9254402789776149991501853)
  ·
    refine ⟨3470401046166056246813195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9254402789776149991501853 3470401046166056246813195)
    ·
      refine ⟨5205601569249084370219793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470401046166056246813195 5205601569249084370219793)
      ·
        refine ⟨3904201176936813277664845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5205601569249084370219793 3904201176936813277664845)
        ·
          refine ⟨1464075441351304979124317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3904201176936813277664845 1464075441351304979124317)
          ·
            refine ⟨549028290506739367171619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1464075441351304979124317 549028290506739367171619)
            ·
              refine ⟨823542435760109050757429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549028290506739367171619 823542435760109050757429)
              ·
                refine ⟨77207103352510223508509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823542435760109050757429 77207103352510223508509)
                ·
                  rfl

theorem cell19_253733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_253733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253733 prefixEnd_253733 := by exact prefixLift 253733
  have htrace : WordTrace (prefixWord ++ tailWord_253733) baseStart_253733 baseEnd_253733 := by
    simpa [prefixWord, tailWord_253733, baseEnd_253733] using wordTrace_append hprefix tailTrace_253733
  have hstable : (prefixWord ++ tailWord_253733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253733).length < 2 ^ (prefixWord ++ tailWord_253733).sum := by decide
  have hdescent : baseEnd_253733 < baseStart_253733 := by decide
  rcases family_descends (prefixWord ++ tailWord_253733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253750 : List Nat := [5, 1, 2, 2, 1, 1, 7]
def baseStart_253750 : Nat := 118140960795 + 253750 * 2 ^ 59
def prefixEnd_253750 : Nat := 4983230072969 + 3 ^ 40 * 253750 * 2
def baseEnd_253750 : Nat := 25737425398219740376895

theorem tailTrace_253750 : CollatzResearch.WordTrace tailWord_253750 prefixEnd_253750 25737425398219740376895 := by
  unfold tailWord_253750
  simp only [CollatzResearch.WordTrace]
  refine ⟨578438926919660118429419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6170015220476374596580469 578438926919660118429419)
  ·
    refine ⟨867658390379490177644129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 578438926919660118429419 867658390379490177644129)
    ·
      refine ⟨650743792784617633233097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867658390379490177644129 650743792784617633233097)
      ·
        refine ⟨488057844588463224924823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650743792784617633233097 488057844588463224924823)
        ·
          refine ⟨732086766882694837387235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488057844588463224924823 732086766882694837387235)
          ·
            refine ⟨1098130150324042256080853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732086766882694837387235 1098130150324042256080853)
            ·
              refine ⟨25737425398219740376895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1098130150324042256080853 25737425398219740376895)
              ·
                rfl

theorem cell19_253750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_253750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253750 prefixEnd_253750 := by exact prefixLift 253750
  have htrace : WordTrace (prefixWord ++ tailWord_253750) baseStart_253750 baseEnd_253750 := by
    simpa [prefixWord, tailWord_253750, baseEnd_253750] using wordTrace_append hprefix tailTrace_253750
  have hstable : (prefixWord ++ tailWord_253750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253750).length < 2 ^ (prefixWord ++ tailWord_253750).sum := by decide
  have hdescent : baseEnd_253750 < baseStart_253750 := by decide
  rcases family_descends (prefixWord ++ tailWord_253750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253752 : List Nat := [2, 1, 2, 1, 3, 5, 5]
def baseStart_253752 : Nat := 118140960795 + 253752 * 2 ^ 59
def prefixEnd_253752 : Nat := 4983230072969 + 3 ^ 40 * 253752 * 2
def baseEnd_253752 : Nat := 25737628254774603028745

theorem tailTrace_253752 : CollatzResearch.WordTrace tailWord_253752 prefixEnd_253752 25737628254774603028745 := by
  unfold tailWord_253752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627547888353658118221755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6170063851138210824295673 4627547888353658118221755)
  ·
    refine ⟨6941321832530487177332633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627547888353658118221755 6941321832530487177332633)
    ·
      refine ⟨5205991374397865382999475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6941321832530487177332633 5205991374397865382999475)
      ·
        refine ⟨7808987061596798074499213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205991374397865382999475 7808987061596798074499213)
        ·
          refine ⟨2928370148098799277937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7808987061596798074499213 2928370148098799277937205)
          ·
            refine ⟨274534701384262432306613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2928370148098799277937205 274534701384262432306613)
            ·
              refine ⟨25737628254774603028745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274534701384262432306613 25737628254774603028745)
              ·
                rfl

theorem cell19_253752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_253752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253752 prefixEnd_253752 := by exact prefixLift 253752
  have htrace : WordTrace (prefixWord ++ tailWord_253752) baseStart_253752 baseEnd_253752 := by
    simpa [prefixWord, tailWord_253752, baseEnd_253752] using wordTrace_append hprefix tailTrace_253752
  have hstable : (prefixWord ++ tailWord_253752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253752).length < 2 ^ (prefixWord ++ tailWord_253752).sum := by decide
  have hdescent : baseEnd_253752 < baseStart_253752 := by decide
  rcases family_descends (prefixWord ++ tailWord_253752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253828 : List Nat := [2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_253828 : Nat := 118140960795 + 253828 * 2 ^ 59
def prefixEnd_253828 : Nat := 4983230072969 + 3 ^ 40 * 253828 * 2
def baseEnd_253828 : Nat := 77236010411578151397139

theorem tailTrace_253828 : CollatzResearch.WordTrace tailWord_253828 prefixEnd_253828 77236010411578151397139 := by
  unfold tailWord_253828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628933862215990608105069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6171911816287987477473425 4628933862215990608105069)
  ·
    refine ⟨1735850198330996478039401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4628933862215990608105069 1735850198330996478039401)
    ·
      refine ⟨1301887648748247358529551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735850198330996478039401 1301887648748247358529551)
      ·
        refine ⟨1952831473122371037794327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301887648748247358529551 1952831473122371037794327)
        ·
          refine ⟨2929247209683556556691491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952831473122371037794327 2929247209683556556691491)
          ·
            refine ⟨4393870814525334835037237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929247209683556556691491 4393870814525334835037237)
            ·
              refine ⟨411925388861750140784741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4393870814525334835037237 411925388861750140784741)
              ·
                refine ⟨77236010411578151397139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411925388861750140784741 77236010411578151397139)
                ·
                  rfl

theorem cell19_253828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_253828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253828 prefixEnd_253828 := by exact prefixLift 253828
  have htrace : WordTrace (prefixWord ++ tailWord_253828) baseStart_253828 baseEnd_253828 := by
    simpa [prefixWord, tailWord_253828, baseEnd_253828] using wordTrace_append hprefix tailTrace_253828
  have hstable : (prefixWord ++ tailWord_253828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253828).length < 2 ^ (prefixWord ++ tailWord_253828).sum := by decide
  have hdescent : baseEnd_253828 < baseStart_253828 := by decide
  rcases family_descends (prefixWord ++ tailWord_253828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253849 : List Nat := [1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_253849 : Nat := 118140960795 + 253849 * 2 ^ 59
def prefixEnd_253849 : Nat := 4983230072969 + 3 ^ 40 * 253849 * 2
def baseEnd_253849 : Nat := 77242400393056324930415

theorem tailTrace_253849 : CollatzResearch.WordTrace tailWord_253849 prefixEnd_253849 77242400393056324930415 := by
  unfold tailWord_253849
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258633657355901802724601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6172422438237267868483067 9258633657355901802724601)
  ·
    refine ⟨6943975243016926352043451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9258633657355901802724601 6943975243016926352043451)
    ·
      refine ⟨10415962864525389528065177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943975243016926352043451 10415962864525389528065177)
      ·
        refine ⟨7811972148394042146048883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10415962864525389528065177 7811972148394042146048883)
        ·
          refine ⟨11717958222591063219073325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811972148394042146048883 11717958222591063219073325)
          ·
            refine ⟨4394234333471648707152497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11717958222591063219073325 4394234333471648707152497)
            ·
              refine ⟨3295675750103736530364373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394234333471648707152497 3295675750103736530364373)
              ·
                refine ⟨77242400393056324930415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3295675750103736530364373 77242400393056324930415)
                ·
                  rfl

theorem cell19_253849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_253849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253849 prefixEnd_253849 := by exact prefixLift 253849
  have htrace : WordTrace (prefixWord ++ tailWord_253849) baseStart_253849 baseEnd_253849 := by
    simpa [prefixWord, tailWord_253849, baseEnd_253849] using wordTrace_append hprefix tailTrace_253849
  have hstable : (prefixWord ++ tailWord_253849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253849).length < 2 ^ (prefixWord ++ tailWord_253849).sum := by decide
  have hdescent : baseEnd_253849 < baseStart_253849 := by decide
  rcases family_descends (prefixWord ++ tailWord_253849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253887 : List Nat := [1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_253887 : Nat := 118140960795 + 253887 * 2 ^ 59
def prefixEnd_253887 : Nat := 4983230072969 + 3 ^ 40 * 253887 * 2
def baseEnd_253887 : Nat := 77253963216683496085867

theorem tailTrace_253887 : CollatzResearch.WordTrace tailWord_253887 prefixEnd_253887 77253963216683496085867 := by
  unfold tailWord_253887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9260019631218234292607915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6173346420812156195071943 9260019631218234292607915)
  ·
    refine ⟨13890029446827351438911873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9260019631218234292607915 13890029446827351438911873)
    ·
      refine ⟨10417522085120513579183905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13890029446827351438911873 10417522085120513579183905)
      ·
        refine ⟨7813141563840385184387929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10417522085120513579183905 7813141563840385184387929)
        ·
          refine ⟨5859856172880288888290947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813141563840385184387929 5859856172880288888290947)
          ·
            refine ⟨8789784259320433332436421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859856172880288888290947 8789784259320433332436421)
            ·
              refine ⟨1648084548622581249831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8789784259320433332436421 1648084548622581249831829)
              ·
                refine ⟨77253963216683496085867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1648084548622581249831829 77253963216683496085867)
                ·
                  rfl

theorem cell19_253887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_253887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253887 prefixEnd_253887 := by exact prefixLift 253887
  have htrace : WordTrace (prefixWord ++ tailWord_253887) baseStart_253887 baseEnd_253887 := by
    simpa [prefixWord, tailWord_253887, baseEnd_253887] using wordTrace_append hprefix tailTrace_253887
  have hstable : (prefixWord ++ tailWord_253887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253887).length < 2 ^ (prefixWord ++ tailWord_253887).sum := by decide
  have hdescent : baseEnd_253887 < baseStart_253887 := by decide
  rcases family_descends (prefixWord ++ tailWord_253887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253904 : List Nat := [2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_253904 : Nat := 118140960795 + 253904 * 2 ^ 59
def prefixEnd_253904 : Nat := 4983230072969 + 3 ^ 40 * 253904 * 2
def baseEnd_253904 : Nat := 77259136058832493708043

theorem tailTrace_253904 : CollatzResearch.WordTrace tailWord_253904 prefixEnd_253904 77259136058832493708043 := by
  unfold tailWord_253904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630319836078323097988383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6173759781437764130651177 4630319836078323097988383)
  ·
    refine ⟨6945479754117484646982575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4630319836078323097988383 6945479754117484646982575)
    ·
      refine ⟨10418219631176226970473863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945479754117484646982575 10418219631176226970473863)
      ·
        refine ⟨15627329446764340455710795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418219631176226970473863 15627329446764340455710795)
        ·
          refine ⟨23440994170146510683566193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627329446764340455710795 23440994170146510683566193)
          ·
            refine ⟨17580745627609883012674645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23440994170146510683566193 17580745627609883012674645)
            ·
              refine ⟨206024362823553316554781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 17580745627609883012674645 206024362823553316554781)
              ·
                refine ⟨77259136058832493708043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206024362823553316554781 77259136058832493708043)
                ·
                  rfl

theorem cell19_253904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_253904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253904 prefixEnd_253904 := by exact prefixLift 253904
  have htrace : WordTrace (prefixWord ++ tailWord_253904) baseStart_253904 baseEnd_253904 := by
    simpa [prefixWord, tailWord_253904, baseEnd_253904] using wordTrace_append hprefix tailTrace_253904
  have hstable : (prefixWord ++ tailWord_253904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253904).length < 2 ^ (prefixWord ++ tailWord_253904).sum := by decide
  have hdescent : baseEnd_253904 < baseStart_253904 := by decide
  rcases family_descends (prefixWord ++ tailWord_253904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253923 : List Nat := [1, 1, 1, 6, 1, 4, 5]
def baseStart_253923 : Nat := 118140960795 + 253923 * 2 ^ 59
def prefixEnd_253923 : Nat := 4983230072969 + 3 ^ 40 * 253923 * 2
def baseEnd_253923 : Nat := 25754972490215359761923

theorem tailTrace_253923 : CollatzResearch.WordTrace tailWord_253923 prefixEnd_253923 25754972490215359761923 := by
  unfold tailWord_253923
  simp only [CollatzResearch.WordTrace]
  refine ⟨9261332659087812440918423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6174221772725208293945615 9261332659087812440918423)
  ·
    refine ⟨13891998988631718661377635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9261332659087812440918423 13891998988631718661377635)
    ·
      refine ⟨20837998482947577992066453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891998988631718661377635 20837998482947577992066453)
      ·
        refine ⟨976781178888167718378115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20837998482947577992066453 976781178888167718378115)
        ·
          refine ⟨1465171768332251577567173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976781178888167718378115 1465171768332251577567173)
          ·
            refine ⟨274719706562297170793845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1465171768332251577567173 274719706562297170793845)
            ·
              refine ⟨25754972490215359761923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274719706562297170793845 25754972490215359761923)
              ·
                rfl

theorem cell19_253923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_253923 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253923 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253923 prefixEnd_253923 := by exact prefixLift 253923
  have htrace : WordTrace (prefixWord ++ tailWord_253923) baseStart_253923 baseEnd_253923 := by
    simpa [prefixWord, tailWord_253923, baseEnd_253923] using wordTrace_append hprefix tailTrace_253923
  have hstable : (prefixWord ++ tailWord_253923).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253923).length < 2 ^ (prefixWord ++ tailWord_253923).sum := by decide
  have hdescent : baseEnd_253923 < baseStart_253923 := by decide
  rcases family_descends (prefixWord ++ tailWord_253923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253944 : List Nat := [2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_253944 : Nat := 118140960795 + 253944 * 2 ^ 59
def prefixEnd_253944 : Nat := 4983230072969 + 3 ^ 40 * 253944 * 2
def baseEnd_253944 : Nat := 77271307452124252819045

theorem tailTrace_253944 : CollatzResearch.WordTrace tailWord_253944 prefixEnd_253944 77271307452124252819045 := by
  unfold tailWord_253944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631049296005866513716443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6174732394674488684955257 4631049296005866513716443)
  ·
    refine ⟨6946573944008799770574665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4631049296005866513716443 6946573944008799770574665)
    ·
      refine ⟨5209930458006599827930999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6946573944008799770574665 5209930458006599827930999)
      ·
        refine ⟨7814895687009899741896499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5209930458006599827930999 7814895687009899741896499)
        ·
          refine ⟨11722343530514849612844749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814895687009899741896499 11722343530514849612844749)
          ·
            refine ⟨4395878823943068604816781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11722343530514849612844749 4395878823943068604816781)
            ·
              refine ⟨1648454558978650726806293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4395878823943068604816781 1648454558978650726806293)
              ·
                refine ⟨77271307452124252819045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1648454558978650726806293 77271307452124252819045)
                ·
                  rfl

theorem cell19_253944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_253944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253944 prefixEnd_253944 := by exact prefixLift 253944
  have htrace : WordTrace (prefixWord ++ tailWord_253944) baseStart_253944 baseEnd_253944 := by
    simpa [prefixWord, tailWord_253944, baseEnd_253944] using wordTrace_append hprefix tailTrace_253944
  have hstable : (prefixWord ++ tailWord_253944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253944).length < 2 ^ (prefixWord ++ tailWord_253944).sum := by decide
  have hdescent : baseEnd_253944 < baseStart_253944 := by decide
  rcases family_descends (prefixWord ++ tailWord_253944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253963 : List Nat := [1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_253963 : Nat := 118140960795 + 253963 * 2 ^ 59
def prefixEnd_253963 : Nat := 4983230072969 + 3 ^ 40 * 253963 * 2
def baseEnd_253963 : Nat := 77277088863937838396771

theorem tailTrace_253963 : CollatzResearch.WordTrace tailWord_253963 prefixEnd_253963 77277088863937838396771 := by
  unfold tailWord_253963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262791578942899272374543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6175194385961932848249695 9262791578942899272374543)
  ·
    refine ⟨13894187368414348908561815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9262791578942899272374543 13894187368414348908561815)
    ·
      refine ⟨20841281052621523362842723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894187368414348908561815 20841281052621523362842723)
      ·
        refine ⟨31261921578932285044264085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841281052621523362842723 31261921578932285044264085)
        ·
          refine ⟨1465402574012450861449879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31261921578932285044264085 1465402574012450861449879)
          ·
            refine ⟨2198103861018676292174819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465402574012450861449879 2198103861018676292174819)
            ·
              refine ⟨3297155791528014438262229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198103861018676292174819 3297155791528014438262229)
              ·
                refine ⟨77277088863937838396771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3297155791528014438262229 77277088863937838396771)
                ·
                  rfl

theorem cell19_253963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_253963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_253963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_253963 prefixEnd_253963 := by exact prefixLift 253963
  have htrace : WordTrace (prefixWord ++ tailWord_253963) baseStart_253963 baseEnd_253963 := by
    simpa [prefixWord, tailWord_253963, baseEnd_253963] using wordTrace_append hprefix tailTrace_253963
  have hstable : (prefixWord ++ tailWord_253963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253963).length < 2 ^ (prefixWord ++ tailWord_253963).sum := by decide
  have hdescent : baseEnd_253963 < baseStart_253963 := by decide
  rcases family_descends (prefixWord ++ tailWord_253963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254014 : List Nat := [4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_254014 : Nat := 118140960795 + 254014 * 2 ^ 59
def prefixEnd_254014 : Nat := 4983230072969 + 3 ^ 40 * 254014 * 2
def baseEnd_254014 : Nat := 77292607390384831263299

theorem tailTrace_254014 : CollatzResearch.WordTrace tailWord_254014 prefixEnd_254014 77292607390384831263299 := by
  unfold tailWord_254014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158081462719766872810137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6176434467838756654987397 1158081462719766872810137)
  ·
    refine ⟨868561097039825154607603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158081462719766872810137 868561097039825154607603)
    ·
      refine ⟨1302841645559737731911405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868561097039825154607603 1302841645559737731911405)
      ·
        refine ⟨488565617084901649466777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1302841645559737731911405 488565617084901649466777)
        ·
          refine ⟨366424212813676237100083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488565617084901649466777 366424212813676237100083)
          ·
            refine ⟨549636319220514355650125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366424212813676237100083 549636319220514355650125)
            ·
              refine ⟨206113619707692883368797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549636319220514355650125 206113619707692883368797)
              ·
                refine ⟨77292607390384831263299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206113619707692883368797 77292607390384831263299)
                ·
                  rfl

theorem cell19_254014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_254014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254014 prefixEnd_254014 := by exact prefixLift 254014
  have htrace : WordTrace (prefixWord ++ tailWord_254014) baseStart_254014 baseEnd_254014 := by
    simpa [prefixWord, tailWord_254014, baseEnd_254014] using wordTrace_append hprefix tailTrace_254014
  have hstable : (prefixWord ++ tailWord_254014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254014).length < 2 ^ (prefixWord ++ tailWord_254014).sum := by decide
  have hdescent : baseEnd_254014 < baseStart_254014 := by decide
  rcases family_descends (prefixWord ++ tailWord_254014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254073 : List Nat := [1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_254073 : Nat := 118140960795 + 254073 * 2 ^ 59
def prefixEnd_254073 : Nat := 4983230072969 + 3 ^ 40 * 254073 * 2
def baseEnd_254073 : Nat := 77310560195490175952027

theorem tailTrace_254073 : CollatzResearch.WordTrace tailWord_254073 prefixEnd_254073 77310560195490175952027 := by
  unfold tailWord_254073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266803608544388058878873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6177869072362925372585915 9266803608544388058878873)
  ·
    refine ⟨6950102706408291044159155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9266803608544388058878873 6950102706408291044159155)
    ·
      refine ⟨10425154059612436566238733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950102706408291044159155 10425154059612436566238733)
      ·
        refine ⟨3909432772354663712339525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10425154059612436566238733 3909432772354663712339525)
        ·
          refine ⟨733018644816499446063661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3909432772354663712339525 733018644816499446063661)
          ·
            refine ⟨274881991806187292273873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733018644816499446063661 274881991806187292273873)
            ·
              refine ⟨206161493854640469205405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274881991806187292273873 206161493854640469205405)
              ·
                refine ⟨77310560195490175952027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206161493854640469205405 77310560195490175952027)
                ·
                  rfl

theorem cell19_254073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_254073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254073 prefixEnd_254073 := by exact prefixLift 254073
  have htrace : WordTrace (prefixWord ++ tailWord_254073) baseStart_254073 baseEnd_254073 := by
    simpa [prefixWord, tailWord_254073, baseEnd_254073] using wordTrace_append hprefix tailTrace_254073
  have hstable : (prefixWord ++ tailWord_254073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254073).length < 2 ^ (prefixWord ++ tailWord_254073).sum := by decide
  have hdescent : baseEnd_254073 < baseStart_254073 := by decide
  rcases family_descends (prefixWord ++ tailWord_254073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254113 : List Nat := [1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_254113 : Nat := 118140960795 + 254113 * 2 ^ 59
def prefixEnd_254113 : Nat := 4983230072969 + 3 ^ 40 * 254113 * 2
def baseEnd_254113 : Nat := 77322731588781935063029

theorem tailTrace_254113 : CollatzResearch.WordTrace tailWord_254113 prefixEnd_254113 77322731588781935063029 := by
  unfold tailWord_254113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268262528399474890334993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6178841685599649926889995 9268262528399474890334993)
  ·
    refine ⟨6951196896299606167751245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9268262528399474890334993 6951196896299606167751245)
    ·
      refine ⟨2606698836112352312906717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6951196896299606167751245 2606698836112352312906717)
      ·
        refine ⟨977512063542132117340019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2606698836112352312906717 977512063542132117340019)
        ·
          refine ⟨1466268095313198176010029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977512063542132117340019 1466268095313198176010029)
          ·
            refine ⟨549850535742449316003761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466268095313198176010029 549850535742449316003761)
            ·
              refine ⟨412387901806836987002821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549850535742449316003761 412387901806836987002821)
              ·
                refine ⟨77322731588781935063029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412387901806836987002821 77322731588781935063029)
                ·
                  rfl

theorem cell19_254113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_254113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254113 prefixEnd_254113 := by exact prefixLift 254113
  have htrace : WordTrace (prefixWord ++ tailWord_254113) baseStart_254113 baseEnd_254113 := by
    simpa [prefixWord, tailWord_254113, baseEnd_254113] using wordTrace_append hprefix tailTrace_254113
  have hstable : (prefixWord ++ tailWord_254113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254113).length < 2 ^ (prefixWord ++ tailWord_254113).sum := by decide
  have hdescent : baseEnd_254113 < baseStart_254113 := by decide
  rcases family_descends (prefixWord ++ tailWord_254113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254166 : List Nat := [5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_254166 : Nat := 118140960795 + 254166 * 2 ^ 59
def prefixEnd_254166 : Nat := 4983230072969 + 3 ^ 40 * 254166 * 2
def baseEnd_254166 : Nat := 77338858684893515885107

theorem tailTrace_254166 : CollatzResearch.WordTrace tailWord_254166 prefixEnd_254166 77338858684893515885107 := by
  unfold tailWord_254166
  simp only [CollatzResearch.WordTrace]
  refine ⟨579387224825466558875897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6180130398138309961342901 579387224825466558875897)
  ·
    refine ⟨434540418619099919156923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 579387224825466558875897 434540418619099919156923)
    ·
      refine ⟨651810627928649878735385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434540418619099919156923 651810627928649878735385)
      ·
        refine ⟨488857970946487409051539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651810627928649878735385 488857970946487409051539)
        ·
          refine ⟨733286956419731113577309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488857970946487409051539 733286956419731113577309)
          ·
            refine ⟨274982608657399167591491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733286956419731113577309 274982608657399167591491)
            ·
              refine ⟨412473912986098751387237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274982608657399167591491 412473912986098751387237)
              ·
                refine ⟨77338858684893515885107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412473912986098751387237 77338858684893515885107)
                ·
                  rfl

theorem cell19_254166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_254166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254166 prefixEnd_254166 := by exact prefixLift 254166
  have htrace : WordTrace (prefixWord ++ tailWord_254166) baseStart_254166 baseEnd_254166 := by
    simpa [prefixWord, tailWord_254166, baseEnd_254166] using wordTrace_append hprefix tailTrace_254166
  have hstable : (prefixWord ++ tailWord_254166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254166).length < 2 ^ (prefixWord ++ tailWord_254166).sum := by decide
  have hdescent : baseEnd_254166 < baseStart_254166 := by decide
  rcases family_descends (prefixWord ++ tailWord_254166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254244 : List Nat := [2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_254244 : Nat := 118140960795 + 254244 * 2 ^ 59
def prefixEnd_254244 : Nat := 4983230072969 + 3 ^ 40 * 254244 * 2
def baseEnd_254244 : Nat := 77362592901812446151561

theorem tailTrace_254244 : CollatzResearch.WordTrace tailWord_254244 prefixEnd_254244 77362592901812446151561 := by
  unfold tailWord_254244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636520245462442131676893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6182026993949922842235857 4636520245462442131676893)
  ·
    refine ⟨1738695092048415799378835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4636520245462442131676893 1738695092048415799378835)
    ·
      refine ⟨2608042638072623699068253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738695092048415799378835 2608042638072623699068253)
      ·
        refine ⟨978015989277233887150595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608042638072623699068253 978015989277233887150595)
        ·
          refine ⟨1467023983915850830725893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978015989277233887150595 1467023983915850830725893)
          ·
            refine ⟨275066996984222030761105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1467023983915850830725893 275066996984222030761105)
            ·
              refine ⟨206300247738166523070829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275066996984222030761105 206300247738166523070829)
              ·
                refine ⟨77362592901812446151561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206300247738166523070829 77362592901812446151561)
                ·
                  rfl

theorem cell19_254244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_254244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254244 prefixEnd_254244 := by exact prefixLift 254244
  have htrace : WordTrace (prefixWord ++ tailWord_254244) baseStart_254244 baseEnd_254244 := by
    simpa [prefixWord, tailWord_254244, baseEnd_254244] using wordTrace_append hprefix tailTrace_254244
  have hstable : (prefixWord ++ tailWord_254244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254244).length < 2 ^ (prefixWord ++ tailWord_254244).sum := by decide
  have hdescent : baseEnd_254244 < baseStart_254244 := by decide
  rcases family_descends (prefixWord ++ tailWord_254244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254265 : List Nat := [1, 2, 1, 6, 1, 3, 5]
def baseStart_254265 : Nat := 118140960795 + 254265 * 2 ^ 59
def prefixEnd_254265 : Nat := 4983230072969 + 3 ^ 40 * 254265 * 2
def baseEnd_254265 : Nat := 25789660961096873228279

theorem tailTrace_254265 : CollatzResearch.WordTrace tailWord_254265 prefixEnd_254265 25789660961096873228279 := by
  unfold tailWord_254265
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273806423848804849868249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6182537615899203233245499 9273806423848804849868249)
  ·
    refine ⟨6955354817886603637401187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9273806423848804849868249 6955354817886603637401187)
    ·
      refine ⟨10433032226829905456101781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6955354817886603637401187 10433032226829905456101781)
      ·
        refine ⟨489048385632651818254771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10433032226829905456101781 489048385632651818254771)
        ·
          refine ⟨733572578448977727382157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489048385632651818254771 733572578448977727382157)
          ·
            refine ⟨275089716918366647768309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733572578448977727382157 275089716918366647768309)
            ·
              refine ⟨25789660961096873228279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275089716918366647768309 25789660961096873228279)
              ·
                rfl

theorem cell19_254265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_254265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254265 prefixEnd_254265 := by exact prefixLift 254265
  have htrace : WordTrace (prefixWord ++ tailWord_254265) baseStart_254265 baseEnd_254265 := by
    simpa [prefixWord, tailWord_254265, baseEnd_254265] using wordTrace_append hprefix tailTrace_254265
  have hstable : (prefixWord ++ tailWord_254265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254265).length < 2 ^ (prefixWord ++ tailWord_254265).sum := by decide
  have hdescent : baseEnd_254265 < baseStart_254265 := by decide
  rcases family_descends (prefixWord ++ tailWord_254265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254339 : List Nat := [1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_254339 : Nat := 118140960795 + 254339 * 2 ^ 59
def prefixEnd_254339 : Nat := 4983230072969 + 3 ^ 40 * 254339 * 2
def baseEnd_254339 : Nat := 77391499960880374040191

theorem tailTrace_254339 : CollatzResearch.WordTrace tailWord_254339 prefixEnd_254339 77391499960880374040191 := by
  unfold tailWord_254339
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276505425580715488062071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6184336950387143658708047 9276505425580715488062071)
  ·
    refine ⟨13914758138371073232093107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276505425580715488062071 13914758138371073232093107)
    ·
      refine ⟨20872137207556609848139661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914758138371073232093107 20872137207556609848139661)
      ·
        refine ⟨7827051452833728693052373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20872137207556609848139661 7827051452833728693052373)
        ·
          refine ⟨183446518425790516243415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7827051452833728693052373 183446518425790516243415)
          ·
            refine ⟨275169777638685774365123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183446518425790516243415 275169777638685774365123)
            ·
              refine ⟨412754666458028661547685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275169777638685774365123 412754666458028661547685)
              ·
                refine ⟨77391499960880374040191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412754666458028661547685 77391499960880374040191)
                ·
                  rfl

theorem cell19_254339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_254339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254339 prefixEnd_254339 := by exact prefixLift 254339
  have htrace : WordTrace (prefixWord ++ tailWord_254339) baseStart_254339 baseEnd_254339 := by
    simpa [prefixWord, tailWord_254339, baseEnd_254339] using wordTrace_append hprefix tailTrace_254339
  have hstable : (prefixWord ++ tailWord_254339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254339).length < 2 ^ (prefixWord ++ tailWord_254339).sum := by decide
  have hdescent : baseEnd_254339 < baseStart_254339 := by decide
  rcases family_descends (prefixWord ++ tailWord_254339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254453 : List Nat := [1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_254453 : Nat := 118140960795 + 254453 * 2 ^ 59
def prefixEnd_254453 : Nat := 4983230072969 + 3 ^ 40 * 254453 * 2
def baseEnd_254453 : Nat := 77426188431761887506547

theorem tailTrace_254453 : CollatzResearch.WordTrace tailWord_254453 prefixEnd_254453 77426188431761887506547 := by
  unfold tailWord_254453
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280663347167712957712013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6187108898111808638474675 9280663347167712957712013)
  ·
    refine ⟨3480248755187892359142005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9280663347167712957712013 3480248755187892359142005)
    ·
      refine ⟨326273320798864908669563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3480248755187892359142005 326273320798864908669563)
      ·
        refine ⟨489409981198297363004345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326273320798864908669563 489409981198297363004345)
        ·
          refine ⟨367057485898723022253259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489409981198297363004345 367057485898723022253259)
          ·
            refine ⟨550586228848084533379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367057485898723022253259 550586228848084533379889)
            ·
              refine ⟨412939671636063400034917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550586228848084533379889 412939671636063400034917)
              ·
                refine ⟨77426188431761887506547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412939671636063400034917 77426188431761887506547)
                ·
                  rfl

theorem cell19_254453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_254453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254453 prefixEnd_254453 := by exact prefixLift 254453
  have htrace : WordTrace (prefixWord ++ tailWord_254453) baseStart_254453 baseEnd_254453 := by
    simpa [prefixWord, tailWord_254453, baseEnd_254453] using wordTrace_append hprefix tailTrace_254453
  have hstable : (prefixWord ++ tailWord_254453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254453).length < 2 ^ (prefixWord ++ tailWord_254453).sum := by decide
  have hdescent : baseEnd_254453 < baseStart_254453 := by decide
  rcases family_descends (prefixWord ++ tailWord_254453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254470 : List Nat := [6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_254470 : Nat := 118140960795 + 254470 * 2 ^ 59
def prefixEnd_254470 : Nat := 4983230072969 + 3 ^ 40 * 254470 * 2
def baseEnd_254470 : Nat := 77431361273910885128723

theorem tailTrace_254470 : CollatzResearch.WordTrace tailWord_254470 prefixEnd_254470 77431361273910885128723 := by
  unfold tailWord_254470
  simp only [CollatzResearch.WordTrace]
  refine ⟨290040105878316401908777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6187522258737416574053909 290040105878316401908777)
  ·
    refine ⟨217530079408737301431583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290040105878316401908777 217530079408737301431583)
    ·
      refine ⟨326295119113105952147375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217530079408737301431583 326295119113105952147375)
      ·
        refine ⟨489442678669658928221063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326295119113105952147375 489442678669658928221063)
        ·
          refine ⟨734164018004488392331595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489442678669658928221063 734164018004488392331595)
          ·
            refine ⟨1101246027006732588497393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734164018004488392331595 1101246027006732588497393)
            ·
              refine ⟨825934520255049441373045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101246027006732588497393 825934520255049441373045)
              ·
                refine ⟨77431361273910885128723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 825934520255049441373045 77431361273910885128723)
                ·
                  rfl

theorem cell19_254470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_254470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254470 prefixEnd_254470 := by exact prefixLift 254470
  have htrace : WordTrace (prefixWord ++ tailWord_254470) baseStart_254470 baseEnd_254470 := by
    simpa [prefixWord, tailWord_254470, baseEnd_254470] using wordTrace_append hprefix tailTrace_254470
  have hstable : (prefixWord ++ tailWord_254470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254470).length < 2 ^ (prefixWord ++ tailWord_254470).sum := by decide
  have hdescent : baseEnd_254470 < baseStart_254470 := by decide
  rcases family_descends (prefixWord ++ tailWord_254470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254476 : List Nat := [2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_254476 : Nat := 118140960795 + 254476 * 2 ^ 59
def prefixEnd_254476 : Nat := 4983230072969 + 3 ^ 40 * 254476 * 2
def baseEnd_254476 : Nat := 77433186982904648995373

theorem tailTrace_254476 : CollatzResearch.WordTrace tailWord_254476 prefixEnd_254476 77433186982904648995373 := by
  unfold tailWord_254476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640751113042193942899641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6187668150722925257199521 4640751113042193942899641)
  ·
    refine ⟨3480563334781645457174731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640751113042193942899641 3480563334781645457174731)
    ·
      refine ⟨5220845002172468185762097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480563334781645457174731 5220845002172468185762097)
      ·
        refine ⟨3915633751629351139321573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220845002172468185762097 3915633751629351139321573)
        ·
          refine ⟨734181328430503338622795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3915633751629351139321573 734181328430503338622795)
          ·
            refine ⟨1101271992645755007934193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734181328430503338622795 1101271992645755007934193)
            ·
              refine ⟨825953994484316255950645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101271992645755007934193 825953994484316255950645)
              ·
                refine ⟨77433186982904648995373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 825953994484316255950645 77433186982904648995373)
                ·
                  rfl

theorem cell19_254476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_254476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254476 prefixEnd_254476 := by exact prefixLift 254476
  have htrace : WordTrace (prefixWord ++ tailWord_254476) baseStart_254476 baseEnd_254476 := by
    simpa [prefixWord, tailWord_254476, baseEnd_254476] using wordTrace_append hprefix tailTrace_254476
  have hstable : (prefixWord ++ tailWord_254476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254476).length < 2 ^ (prefixWord ++ tailWord_254476).sum := by decide
  have hdescent : baseEnd_254476 < baseStart_254476 := by decide
  rcases family_descends (prefixWord ++ tailWord_254476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254510 : List Nat := [4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_254510 : Nat := 118140960795 + 254510 * 2 ^ 59
def prefixEnd_254510 : Nat := 4983230072969 + 3 ^ 40 * 254510 * 2
def baseEnd_254510 : Nat := 77443532667202644239725

theorem tailTrace_254510 : CollatzResearch.WordTrace tailWord_254510 prefixEnd_254510 77443532667202644239725 := by
  unfold tailWord_254510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160342788495151461567123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6188494871974141128357989 1160342788495151461567123)
  ·
    refine ⟨1740514182742727192350685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1160342788495151461567123 1740514182742727192350685)
    ·
      refine ⟨652692818528522697131507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1740514182742727192350685 652692818528522697131507)
      ·
        refine ⟨979039227792784045697261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652692818528522697131507 979039227792784045697261)
        ·
          refine ⟨367139710422294017136473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979039227792784045697261 367139710422294017136473)
          ·
            refine ⟨275354782816720512852355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367139710422294017136473 275354782816720512852355)
            ·
              refine ⟨413032174225080769278533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275354782816720512852355 413032174225080769278533)
              ·
                refine ⟨77443532667202644239725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413032174225080769278533 77443532667202644239725)
                ·
                  rfl

theorem cell19_254510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_254510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254510 prefixEnd_254510 := by exact prefixLift 254510
  have htrace : WordTrace (prefixWord ++ tailWord_254510) baseStart_254510 baseEnd_254510 := by
    simpa [prefixWord, tailWord_254510, baseEnd_254510] using wordTrace_append hprefix tailTrace_254510
  have hstable : (prefixWord ++ tailWord_254510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254510).length < 2 ^ (prefixWord ++ tailWord_254510).sum := by decide
  have hdescent : baseEnd_254510 < baseStart_254510 := by decide
  rcases family_descends (prefixWord ++ tailWord_254510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254514 : List Nat := [3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_254514 : Nat := 118140960795 + 254514 * 2 ^ 59
def prefixEnd_254514 : Nat := 4983230072969 + 3 ^ 40 * 254514 * 2
def baseEnd_254514 : Nat := 77444749806531820150825

theorem tailTrace_254514 : CollatzResearch.WordTrace tailWord_254514 prefixEnd_254514 77444749806531820150825 := by
  unfold tailWord_254514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320722049986680093920649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6188592133297813583788397 2320722049986680093920649)
  ·
    refine ⟨1740541537490010070440487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320722049986680093920649 1740541537490010070440487)
    ·
      refine ⟨2610812306235015105660731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740541537490010070440487 2610812306235015105660731)
      ·
        refine ⟨3916218459352522658491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610812306235015105660731 3916218459352522658491097)
        ·
          refine ⟨2937163844514391993868323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916218459352522658491097 2937163844514391993868323)
          ·
            refine ⟨4405745766771587990802485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937163844514391993868323 4405745766771587990802485)
            ·
              refine ⟨413038665634836374137733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4405745766771587990802485 413038665634836374137733)
              ·
                refine ⟨77444749806531820150825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413038665634836374137733 77444749806531820150825)
                ·
                  rfl

theorem cell19_254514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_254514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254514 prefixEnd_254514 := by exact prefixLift 254514
  have htrace : WordTrace (prefixWord ++ tailWord_254514) baseStart_254514 baseEnd_254514 := by
    simpa [prefixWord, tailWord_254514, baseEnd_254514] using wordTrace_append hprefix tailTrace_254514
  have hstable : (prefixWord ++ tailWord_254514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254514).length < 2 ^ (prefixWord ++ tailWord_254514).sum := by decide
  have hdescent : baseEnd_254514 < baseStart_254514 := by decide
  rcases family_descends (prefixWord ++ tailWord_254514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254628 : List Nat := [2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_254628 : Nat := 118140960795 + 254628 * 2 ^ 59
def prefixEnd_254628 : Nat := 4983230072969 + 3 ^ 40 * 254628 * 2
def baseEnd_254628 : Nat := 77479438277413333617181

theorem tailTrace_254628 : CollatzResearch.WordTrace tailWord_254628 prefixEnd_254628 77479438277413333617181 := by
  unfold tailWord_254628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643523060766858922666269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6191364081022478563555025 4643523060766858922666269)
  ·
    refine ⟨1741321147787572095999851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4643523060766858922666269 1741321147787572095999851)
    ·
      refine ⟨2611981721681358143999777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741321147787572095999851 2611981721681358143999777)
      ·
        refine ⟨1958986291261018607999833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2611981721681358143999777 1958986291261018607999833)
        ·
          refine ⟨1469239718445763955999875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958986291261018607999833 1469239718445763955999875)
          ·
            refine ⟨2203859577668645933999813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469239718445763955999875 2203859577668645933999813)
            ·
              refine ⟨413223670812871112624965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2203859577668645933999813 413223670812871112624965)
              ·
                refine ⟨77479438277413333617181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413223670812871112624965 77479438277413333617181)
                ·
                  rfl

theorem cell19_254628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_254628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254628 prefixEnd_254628 := by exact prefixLift 254628
  have htrace : WordTrace (prefixWord ++ tailWord_254628) baseStart_254628 baseEnd_254628 := by
    simpa [prefixWord, tailWord_254628, baseEnd_254628] using wordTrace_append hprefix tailTrace_254628
  have hstable : (prefixWord ++ tailWord_254628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254628).length < 2 ^ (prefixWord ++ tailWord_254628).sum := by decide
  have hdescent : baseEnd_254628 < baseStart_254628 := by decide
  rcases family_descends (prefixWord ++ tailWord_254628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254662 : List Nat := [6, 1, 2, 1, 2, 7]
def baseStart_254662 : Nat := 118140960795 + 254662 * 2 ^ 59
def prefixEnd_254662 : Nat := 4983230072969 + 3 ^ 40 * 254662 * 2
def baseEnd_254662 : Nat := 8609975995745703206837

theorem tailTrace_254662 : CollatzResearch.WordTrace tailWord_254662 prefixEnd_254662 8609975995745703206837 := by
  unfold tailWord_254662
  simp only [CollatzResearch.WordTrace]
  refine ⟨290258943856579426627195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6192190802273694434713493 290258943856579426627195)
  ·
    refine ⟨435388415784869139940793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290258943856579426627195 435388415784869139940793)
    ·
      refine ⟨326541311838651854955595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435388415784869139940793 326541311838651854955595)
      ·
        refine ⟨489811967757977782433393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326541311838651854955595 489811967757977782433393)
        ·
          refine ⟨367358975818483336825045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489811967757977782433393 367358975818483336825045)
          ·
            refine ⟨8609975995745703206837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367358975818483336825045 8609975995745703206837)
            ·
              rfl

theorem cell19_254662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_254662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254662 prefixEnd_254662 := by exact prefixLift 254662
  have htrace : WordTrace (prefixWord ++ tailWord_254662) baseStart_254662 baseEnd_254662 := by
    simpa [prefixWord, tailWord_254662, baseEnd_254662] using wordTrace_append hprefix tailTrace_254662
  have hstable : (prefixWord ++ tailWord_254662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254662).length < 2 ^ (prefixWord ++ tailWord_254662).sum := by decide
  have hdescent : baseEnd_254662 < baseStart_254662 := by decide
  rcases family_descends (prefixWord ++ tailWord_254662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254702 : List Nat := [4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_254702 : Nat := 118140960795 + 254702 * 2 ^ 59
def prefixEnd_254702 : Nat := 4983230072969 + 3 ^ 40 * 254702 * 2
def baseEnd_254702 : Nat := 77501955355003087972535

theorem tailTrace_254702 : CollatzResearch.WordTrace tailWord_254702 prefixEnd_254702 77501955355003087972535 := by
  unfold tailWord_254702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161218140408203560440795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6193163415510418989017573 1161218140408203560440795)
  ·
    refine ⟨1741827210612305340661193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161218140408203560440795 1741827210612305340661193)
    ·
      refine ⟨1306370407959229005495895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1741827210612305340661193 1306370407959229005495895)
      ·
        refine ⟨1959555611938843508243843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306370407959229005495895 1959555611938843508243843)
        ·
          refine ⟨2939333417908265262365765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959555611938843508243843 2939333417908265262365765)
          ·
            refine ⟨551125015857799736693581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2939333417908265262365765 551125015857799736693581)
            ·
              refine ⟨206671880946674901260093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 551125015857799736693581 206671880946674901260093)
              ·
                refine ⟨77501955355003087972535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206671880946674901260093 77501955355003087972535)
                ·
                  rfl

theorem cell19_254702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_254702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254702 prefixEnd_254702 := by exact prefixLift 254702
  have htrace : WordTrace (prefixWord ++ tailWord_254702) baseStart_254702 baseEnd_254702 := by
    simpa [prefixWord, tailWord_254702, baseEnd_254702] using wordTrace_append hprefix tailTrace_254702
  have hstable : (prefixWord ++ tailWord_254702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254702).length < 2 ^ (prefixWord ++ tailWord_254702).sum := by decide
  have hdescent : baseEnd_254702 < baseStart_254702 := by decide
  rcases family_descends (prefixWord ++ tailWord_254702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254704 : List Nat := [2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_254704 : Nat := 118140960795 + 254704 * 2 ^ 59
def prefixEnd_254704 : Nat := 4983230072969 + 3 ^ 40 * 254704 * 2
def baseEnd_254704 : Nat := 77502563924667675928085

theorem tailTrace_254704 : CollatzResearch.WordTrace tailWord_254704 prefixEnd_254704 77502563924667675928085 := by
  unfold tailWord_254704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4644909034629191412549583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6193212046172255216732777 4644909034629191412549583)
  ·
    refine ⟨6967363551943787118824375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4644909034629191412549583 6967363551943787118824375)
    ·
      refine ⟨10451045327915680678236563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967363551943787118824375 10451045327915680678236563)
      ·
        refine ⟨15676567991873521017354845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451045327915680678236563 15676567991873521017354845)
        ·
          refine ⟨5878712996952570381508067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15676567991873521017354845 5878712996952570381508067)
          ·
            refine ⟨8818069495428855572262101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5878712996952570381508067 8818069495428855572262101)
            ·
              refine ⟨206673503799113802474893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8818069495428855572262101 206673503799113802474893)
              ·
                refine ⟨77502563924667675928085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206673503799113802474893 77502563924667675928085)
                ·
                  rfl

theorem cell19_254704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_254704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254704 prefixEnd_254704 := by exact prefixLift 254704
  have htrace : WordTrace (prefixWord ++ tailWord_254704) baseStart_254704 baseEnd_254704 := by
    simpa [prefixWord, tailWord_254704, baseEnd_254704] using wordTrace_append hprefix tailTrace_254704
  have hstable : (prefixWord ++ tailWord_254704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254704).length < 2 ^ (prefixWord ++ tailWord_254704).sum := by decide
  have hdescent : baseEnd_254704 < baseStart_254704 := by decide
  rcases family_descends (prefixWord ++ tailWord_254704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254744 : List Nat := [2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_254744 : Nat := 118140960795 + 254744 * 2 ^ 59
def prefixEnd_254744 : Nat := 4983230072969 + 3 ^ 40 * 254744 * 2
def baseEnd_254744 : Nat := 77514735317959435039087

theorem tailTrace_254744 : CollatzResearch.WordTrace tailWord_254744 prefixEnd_254744 77514735317959435039087 := by
  unfold tailWord_254744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645638494556734828277643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6194184659408979771036857 4645638494556734828277643)
  ·
    refine ⟨6968457741835102242416465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4645638494556734828277643 6968457741835102242416465)
    ·
      refine ⟨5226343306376326681812349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6968457741835102242416465 5226343306376326681812349)
      ·
        refine ⟨1959878739891122505679631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5226343306376326681812349 1959878739891122505679631)
        ·
          refine ⟨2939818109836683758519447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959878739891122505679631 2939818109836683758519447)
          ·
            refine ⟨4409727164755025637779171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939818109836683758519447 4409727164755025637779171)
            ·
              refine ⟨6614590747132538456668757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409727164755025637779171 6614590747132538456668757)
              ·
                refine ⟨77514735317959435039087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6614590747132538456668757 77514735317959435039087)
                ·
                  rfl

theorem cell19_254744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_254744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254744 prefixEnd_254744 := by exact prefixLift 254744
  have htrace : WordTrace (prefixWord ++ tailWord_254744) baseStart_254744 baseEnd_254744 := by
    simpa [prefixWord, tailWord_254744, baseEnd_254744] using wordTrace_append hprefix tailTrace_254744
  have hstable : (prefixWord ++ tailWord_254744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254744).length < 2 ^ (prefixWord ++ tailWord_254744).sum := by decide
  have hdescent : baseEnd_254744 < baseStart_254744 := by decide
  rcases family_descends (prefixWord ++ tailWord_254744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254778 : List Nat := [3, 1, 1, 1, 7, 1, 5]
def baseStart_254778 : Nat := 118140960795 + 254778 * 2 ^ 59
def prefixEnd_254778 : Nat := 4983230072969 + 3 ^ 40 * 254778 * 2
def baseEnd_254778 : Nat := 25841693667419143427813

theorem tailTrace_254778 : CollatzResearch.WordTrace tailWord_254778 prefixEnd_254778 25841693667419143427813 := by
  unfold tailWord_254778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323129267747573365823247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6195011380660195642195325 2323129267747573365823247)
  ·
    refine ⟨3484693901621360048734871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323129267747573365823247 3484693901621360048734871)
    ·
      refine ⟨5227040852432040073102307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484693901621360048734871 5227040852432040073102307)
      ·
        refine ⟨7840561278648060109653461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227040852432040073102307 7840561278648060109653461)
        ·
          refine ⟨183763154968313908820003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7840561278648060109653461 183763154968313908820003)
          ·
            refine ⟨275644732452470863230005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183763154968313908820003 275644732452470863230005)
            ·
              refine ⟨25841693667419143427813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275644732452470863230005 25841693667419143427813)
              ·
                rfl

theorem cell19_254778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_254778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254778 prefixEnd_254778 := by exact prefixLift 254778
  have htrace : WordTrace (prefixWord ++ tailWord_254778) baseStart_254778 baseEnd_254778 := by
    simpa [prefixWord, tailWord_254778, baseEnd_254778] using wordTrace_append hprefix tailTrace_254778
  have hstable : (prefixWord ++ tailWord_254778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254778).length < 2 ^ (prefixWord ++ tailWord_254778).sum := by decide
  have hdescent : baseEnd_254778 < baseStart_254778 := by decide
  rcases family_descends (prefixWord ++ tailWord_254778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254850 : List Nat := [3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_254850 : Nat := 118140960795 + 254850 * 2 ^ 59
def prefixEnd_254850 : Nat := 4983230072969 + 3 ^ 40 * 254850 * 2
def baseEnd_254850 : Nat := 77546989510182596683243

theorem tailTrace_254850 : CollatzResearch.WordTrace tailWord_254850 prefixEnd_254850 77546989510182596683243 := by
  unfold tailWord_254850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323785781682362439978501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6196762084486299839942669 2323785781682362439978501)
  ·
    refine ⟨435709834065442957495969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2323785781682362439978501 435709834065442957495969)
    ·
      refine ⟨326782375549082218121977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435709834065442957495969 326782375549082218121977)
      ·
        refine ⟨245086781661811663591483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326782375549082218121977 245086781661811663591483)
        ·
          refine ⟨367630172492717495387225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245086781661811663591483 367630172492717495387225)
          ·
            refine ⟨275722629369538121540419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367630172492717495387225 275722629369538121540419)
            ·
              refine ⟨413583944054307182310629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275722629369538121540419 413583944054307182310629)
              ·
                refine ⟨77546989510182596683243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413583944054307182310629 77546989510182596683243)
                ·
                  rfl

theorem cell19_254850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_254850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254850 prefixEnd_254850 := by exact prefixLift 254850
  have htrace : WordTrace (prefixWord ++ tailWord_254850) baseStart_254850 baseEnd_254850 := by
    simpa [prefixWord, tailWord_254850, baseEnd_254850] using wordTrace_append hprefix tailTrace_254850
  have hstable : (prefixWord ++ tailWord_254850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254850).length < 2 ^ (prefixWord ++ tailWord_254850).sum := by decide
  have hdescent : baseEnd_254850 < baseStart_254850 := by decide
  rcases family_descends (prefixWord ++ tailWord_254850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254856 : List Nat := [2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_254856 : Nat := 118140960795 + 254856 * 2 ^ 59
def prefixEnd_254856 : Nat := 4983230072969 + 3 ^ 40 * 254856 * 2
def baseEnd_254856 : Nat := 77548815219176360549893

theorem tailTrace_254856 : CollatzResearch.WordTrace tailWord_254856 prefixEnd_254856 77548815219176360549893 := by
  unfold tailWord_254856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647680982353856392316211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6196907976471808523088281 4647680982353856392316211)
  ·
    refine ⟨6971521473530784588474317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647680982353856392316211 6971521473530784588474317)
    ·
      refine ⟨2614320552574044220677869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6971521473530784588474317 2614320552574044220677869)
      ·
        refine ⟨980370207215266582754201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2614320552574044220677869 980370207215266582754201)
        ·
          refine ⟨735277655411449937065651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980370207215266582754201 735277655411449937065651)
          ·
            refine ⟨1102916483117174905598477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735277655411449937065651 1102916483117174905598477)
            ·
              refine ⟨413593681168940589599429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102916483117174905598477 413593681168940589599429)
              ·
                refine ⟨77548815219176360549893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413593681168940589599429 77548815219176360549893)
                ·
                  rfl

theorem cell19_254856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_254856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254856 prefixEnd_254856 := by exact prefixLift 254856
  have htrace : WordTrace (prefixWord ++ tailWord_254856) baseStart_254856 baseEnd_254856 := by
    simpa [prefixWord, tailWord_254856, baseEnd_254856] using wordTrace_append hprefix tailTrace_254856
  have hstable : (prefixWord ++ tailWord_254856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254856).length < 2 ^ (prefixWord ++ tailWord_254856).sum := by decide
  have hdescent : baseEnd_254856 < baseStart_254856 := by decide
  rcases family_descends (prefixWord ++ tailWord_254856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254930 : List Nat := [3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_254930 : Nat := 118140960795 + 254930 * 2 ^ 59
def prefixEnd_254930 : Nat := 4983230072969 + 3 ^ 40 * 254930 * 2
def baseEnd_254930 : Nat := 77571332296766114905247

theorem tailTrace_254930 : CollatzResearch.WordTrace tailWord_254930 prefixEnd_254930 77571332296766114905247 := by
  unfold tailWord_254930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324515241609905855706561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6198707310959748948550829 2324515241609905855706561)
  ·
    refine ⟨1743386431207429391779921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2324515241609905855706561 1743386431207429391779921)
    ·
      refine ⟨1307539823405572043834941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1743386431207429391779921 1307539823405572043834941)
      ·
        refine ⟨490327433777089516438103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1307539823405572043834941 490327433777089516438103)
        ·
          refine ⟨735491150665634274657155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490327433777089516438103 735491150665634274657155)
          ·
            refine ⟨1103236725998451411985733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735491150665634274657155 1103236725998451411985733)
            ·
              refine ⟨206856886124709639747325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1103236725998451411985733 206856886124709639747325)
              ·
                refine ⟨77571332296766114905247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206856886124709639747325 77571332296766114905247)
                ·
                  rfl

theorem cell19_254930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_254930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254930 prefixEnd_254930 := by exact prefixLift 254930
  have htrace : WordTrace (prefixWord ++ tailWord_254930) baseStart_254930 baseEnd_254930 := by
    simpa [prefixWord, tailWord_254930, baseEnd_254930] using wordTrace_append hprefix tailTrace_254930
  have hstable : (prefixWord ++ tailWord_254930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254930).length < 2 ^ (prefixWord ++ tailWord_254930).sum := by decide
  have hdescent : baseEnd_254930 < baseStart_254930 := by decide
  rcases family_descends (prefixWord ++ tailWord_254930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254932 : List Nat := [2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_254932 : Nat := 118140960795 + 254932 * 2 ^ 59
def prefixEnd_254932 : Nat := 4983230072969 + 3 ^ 40 * 254932 * 2
def baseEnd_254932 : Nat := 77571940866430702860797

theorem tailTrace_254932 : CollatzResearch.WordTrace tailWord_254932 prefixEnd_254932 77571940866430702860797 := by
  unfold tailWord_254932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649066956216188882199525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6198755941621585176266033 4649066956216188882199525)
  ·
    refine ⟨871700054290535415412411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4649066956216188882199525 871700054290535415412411)
    ·
      refine ⟨1307550081435803123118617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871700054290535415412411 1307550081435803123118617)
      ·
        refine ⟨980662561076852342338963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307550081435803123118617 980662561076852342338963)
        ·
          refine ⟨1470993841615278513508445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980662561076852342338963 1470993841615278513508445)
          ·
            refine ⟨551622690605729442565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1470993841615278513508445 551622690605729442565667)
            ·
              refine ⟨827434035908594163848501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551622690605729442565667 827434035908594163848501)
              ·
                refine ⟨77571940866430702860797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827434035908594163848501 77571940866430702860797)
                ·
                  rfl

theorem cell19_254932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_254932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254932 prefixEnd_254932 := by exact prefixLift 254932
  have htrace : WordTrace (prefixWord ++ tailWord_254932) baseStart_254932 baseEnd_254932 := by
    simpa [prefixWord, tailWord_254932, baseEnd_254932] using wordTrace_append hprefix tailTrace_254932
  have hstable : (prefixWord ++ tailWord_254932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254932).length < 2 ^ (prefixWord ++ tailWord_254932).sum := by decide
  have hdescent : baseEnd_254932 < baseStart_254932 := by decide
  rcases family_descends (prefixWord ++ tailWord_254932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254949 : List Nat := [1, 3, 1, 6, 1, 2, 5]
def baseStart_254949 : Nat := 118140960795 + 254949 * 2 ^ 59
def prefixEnd_254949 : Nat := 4983230072969 + 3 ^ 40 * 254949 * 2
def baseEnd_254949 : Nat := 25859037902859900160991

theorem tailTrace_254949 : CollatzResearch.WordTrace tailWord_254949 prefixEnd_254949 25859037902859900160991 := by
  unfold tailWord_254949
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298753953370789667767901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6199169302247193111845267 9298753953370789667767901)
  ·
    refine ⟨3487032732514046125412963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9298753953370789667767901 3487032732514046125412963)
    ·
      refine ⟨5230549098771069188119445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487032732514046125412963 5230549098771069188119445)
      ·
        refine ⟨245181989004893868193099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5230549098771069188119445 245181989004893868193099)
        ·
          refine ⟨367772983507340802289649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245181989004893868193099 367772983507340802289649)
          ·
            refine ⟨275829737630505601717237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367772983507340802289649 275829737630505601717237)
            ·
              refine ⟨25859037902859900160991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275829737630505601717237 25859037902859900160991)
              ·
                rfl

theorem cell19_254949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_254949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254949 prefixEnd_254949 := by exact prefixLift 254949
  have htrace : WordTrace (prefixWord ++ tailWord_254949) baseStart_254949 baseEnd_254949 := by
    simpa [prefixWord, tailWord_254949, baseEnd_254949] using wordTrace_append hprefix tailTrace_254949
  have hstable : (prefixWord ++ tailWord_254949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254949).length < 2 ^ (prefixWord ++ tailWord_254949).sum := by decide
  have hdescent : baseEnd_254949 < baseStart_254949 := by decide
  rcases family_descends (prefixWord ++ tailWord_254949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254951 : List Nat := [1, 1, 5, 2, 2, 3, 5]
def baseStart_254951 : Nat := 118140960795 + 254951 * 2 ^ 59
def prefixEnd_254951 : Nat := 4983230072969 + 3 ^ 40 * 254951 * 2
def baseEnd_254951 : Nat := 25859240759414762812841

theorem tailTrace_254951 : CollatzResearch.WordTrace tailWord_254951 prefixEnd_254951 25859240759414762812841 := by
  unfold tailWord_254951
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298826899363544009340707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6199217932909029339560471 9298826899363544009340707)
  ·
    refine ⟨13948240349045316014011061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9298826899363544009340707 13948240349045316014011061)
    ·
      refine ⟨1307647532722998376313537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13948240349045316014011061 1307647532722998376313537)
      ·
        refine ⟨980735649542248782235153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307647532722998376313537 980735649542248782235153)
        ·
          refine ⟨735551737156686586676365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980735649542248782235153 735551737156686586676365)
          ·
            refine ⟨275831901433757470003637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735551737156686586676365 275831901433757470003637)
            ·
              refine ⟨25859240759414762812841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275831901433757470003637 25859240759414762812841)
              ·
                rfl

theorem cell19_254951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_254951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254951 prefixEnd_254951 := by exact prefixLift 254951
  have htrace : WordTrace (prefixWord ++ tailWord_254951) baseStart_254951 baseEnd_254951 := by
    simpa [prefixWord, tailWord_254951, baseEnd_254951] using wordTrace_append hprefix tailTrace_254951
  have hstable : (prefixWord ++ tailWord_254951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254951).length < 2 ^ (prefixWord ++ tailWord_254951).sum := by decide
  have hdescent : baseEnd_254951 < baseStart_254951 := by decide
  rcases family_descends (prefixWord ++ tailWord_254951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254972 : List Nat := [2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_254972 : Nat := 118140960795 + 254972 * 2 ^ 59
def prefixEnd_254972 : Nat := 4983230072969 + 3 ^ 40 * 254972 * 2
def baseEnd_254972 : Nat := 77584112259722461971799

theorem tailTrace_254972 : CollatzResearch.WordTrace tailWord_254972 prefixEnd_254972 77584112259722461971799 := by
  unfold tailWord_254972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649796416143732297927585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6199728554858309730570113 4649796416143732297927585)
  ·
    refine ⟨3487347312107799223445689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4649796416143732297927585 3487347312107799223445689)
    ·
      refine ⟨2615510484080849417584267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3487347312107799223445689 2615510484080849417584267)
      ·
        refine ⟨3923265726121274126376401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615510484080849417584267 3923265726121274126376401)
        ·
          refine ⟨2942449294590955594782301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923265726121274126376401 2942449294590955594782301)
          ·
            refine ⟨1103418485471608348043363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2942449294590955594782301 1103418485471608348043363)
            ·
              refine ⟨1655127728207412522065045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103418485471608348043363 1655127728207412522065045)
              ·
                refine ⟨77584112259722461971799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1655127728207412522065045 77584112259722461971799)
                ·
                  rfl

theorem cell19_254972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_254972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_254972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_254972 prefixEnd_254972 := by exact prefixLift 254972
  have htrace : WordTrace (prefixWord ++ tailWord_254972) baseStart_254972 baseEnd_254972 := by
    simpa [prefixWord, tailWord_254972, baseEnd_254972] using wordTrace_append hprefix tailTrace_254972
  have hstable : (prefixWord ++ tailWord_254972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254972).length < 2 ^ (prefixWord ++ tailWord_254972).sum := by decide
  have hdescent : baseEnd_254972 < baseStart_254972 := by decide
  rcases family_descends (prefixWord ++ tailWord_254972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255008 : List Nat := [2, 1, 1, 7, 1, 7]
def baseStart_255008 : Nat := 118140960795 + 255008 * 2 ^ 59
def prefixEnd_255008 : Nat := 4983230072969 + 3 ^ 40 * 255008 * 2
def baseEnd_255008 : Nat := 8621674057076116130189

theorem tailTrace_255008 : CollatzResearch.WordTrace tailWord_255008 prefixEnd_255008 8621674057076116130189 := by
  unfold tailWord_255008
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650452930078521372082839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6200603906771361829443785 4650452930078521372082839)
  ·
    refine ⟨6975679395117782058124259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4650452930078521372082839 6975679395117782058124259)
    ·
      refine ⟨10463519092676673087186389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975679395117782058124259 10463519092676673087186389)
      ·
        refine ⟨245238728734609525480931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10463519092676673087186389 245238728734609525480931)
        ·
          refine ⟨367858093101914288221397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245238728734609525480931 367858093101914288221397)
          ·
            refine ⟨8621674057076116130189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367858093101914288221397 8621674057076116130189)
            ·
              rfl

theorem cell19_255008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_255008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255008 prefixEnd_255008 := by exact prefixLift 255008
  have htrace : WordTrace (prefixWord ++ tailWord_255008) baseStart_255008 baseEnd_255008 := by
    simpa [prefixWord, tailWord_255008, baseEnd_255008] using wordTrace_append hprefix tailTrace_255008
  have hstable : (prefixWord ++ tailWord_255008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255008).length < 2 ^ (prefixWord ++ tailWord_255008).sum := by decide
  have hdescent : baseEnd_255008 < baseStart_255008 := by decide
  rcases family_descends (prefixWord ++ tailWord_255008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255010 : List Nat := [3, 3, 1, 1, 1, 10]
def baseStart_255010 : Nat := 118140960795 + 255010 * 2 ^ 59
def prefixEnd_255010 : Nat := 4983230072969 + 3 ^ 40 * 255010 * 2
def baseEnd_255010 : Nat := 8621741675927737014139

theorem tailTrace_255010 : CollatzResearch.WordTrace tailWord_255010 prefixEnd_255010 8621741675927737014139 := by
  unfold tailWord_255010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325244701537449271434621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6200652537433198057158989 2325244701537449271434621)
  ·
    refine ⟨871966763076543476787983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2325244701537449271434621 871966763076543476787983)
    ·
      refine ⟨1307950144614815215181975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871966763076543476787983 1307950144614815215181975)
      ·
        refine ⟨1961925216922222822772963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307950144614815215181975 1961925216922222822772963)
        ·
          refine ⟨2942887825383334234159445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961925216922222822772963 2942887825383334234159445)
          ·
            refine ⟨8621741675927737014139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2942887825383334234159445 8621741675927737014139)
            ·
              rfl

theorem cell19_255010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_255010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255010 prefixEnd_255010 := by exact prefixLift 255010
  have htrace : WordTrace (prefixWord ++ tailWord_255010) baseStart_255010 baseEnd_255010 := by
    simpa [prefixWord, tailWord_255010, baseEnd_255010] using wordTrace_append hprefix tailTrace_255010
  have hstable : (prefixWord ++ tailWord_255010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255010).length < 2 ^ (prefixWord ++ tailWord_255010).sum := by decide
  have hdescent : baseEnd_255010 < baseStart_255010 := by decide
  rcases family_descends (prefixWord ++ tailWord_255010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255122 : List Nat := [3, 2, 3, 1, 1, 4, 5]
def baseStart_255122 : Nat := 118140960795 + 255122 * 2 ^ 59
def prefixEnd_255122 : Nat := 4983230072969 + 3 ^ 40 * 255122 * 2
def baseEnd_255122 : Nat := 25876584994855519546019

theorem tailTrace_255122 : CollatzResearch.WordTrace tailWord_255122 prefixEnd_255122 25876584994855519546019 := by
  unfold tailWord_255122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326265945436010053453905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6203375854496026809210413 2326265945436010053453905)
  ·
    refine ⟨1744699459077007540090429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2326265945436010053453905 1744699459077007540090429)
    ·
      refine ⟨654262297153877827533911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1744699459077007540090429 654262297153877827533911)
      ·
        refine ⟨981393445730816741300867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654262297153877827533911 981393445730816741300867)
        ·
          refine ⟨1472090168596225111951301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981393445730816741300867 1472090168596225111951301)
          ·
            refine ⟨276016906611792208490869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1472090168596225111951301 276016906611792208490869)
            ·
              refine ⟨25876584994855519546019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276016906611792208490869 25876584994855519546019)
              ·
                rfl

theorem cell19_255122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_255122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255122 prefixEnd_255122 := by exact prefixLift 255122
  have htrace : WordTrace (prefixWord ++ tailWord_255122) baseStart_255122 baseEnd_255122 := by
    simpa [prefixWord, tailWord_255122, baseEnd_255122] using wordTrace_append hprefix tailTrace_255122
  have hstable : (prefixWord ++ tailWord_255122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255122).length < 2 ^ (prefixWord ++ tailWord_255122).sum := by decide
  have hdescent : baseEnd_255122 < baseStart_255122 := by decide
  rcases family_descends (prefixWord ++ tailWord_255122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255200 : List Nat := [2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_255200 : Nat := 118140960795 + 255200 * 2 ^ 59
def prefixEnd_255200 : Nat := 4983230072969 + 3 ^ 40 * 255200 * 2
def baseEnd_255200 : Nat := 77653489201485488904511

theorem tailTrace_255200 : CollatzResearch.WordTrace tailWord_255200 prefixEnd_255200 77653489201485488904511 := by
  unfold tailWord_255200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653954337730729767577527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6205272450307639690103369 4653954337730729767577527)
  ·
    refine ⟨6980931506596094651366291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653954337730729767577527 6980931506596094651366291)
    ·
      refine ⟨10471397259894141977049437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980931506596094651366291 10471397259894141977049437)
      ·
        refine ⟨3926773972460303241393539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10471397259894141977049437 3926773972460303241393539)
        ·
          refine ⟨5890160958690454862090309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926773972460303241393539 5890160958690454862090309)
          ·
            refine ⟨1104405179754460286641933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5890160958690454862090309 1104405179754460286641933)
            ·
              refine ⟨414151942407922607490725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104405179754460286641933 414151942407922607490725)
              ·
                refine ⟨77653489201485488904511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414151942407922607490725 77653489201485488904511)
                ·
                  rfl

theorem cell19_255200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_255200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255200 prefixEnd_255200 := by exact prefixLift 255200
  have htrace : WordTrace (prefixWord ++ tailWord_255200) baseStart_255200 baseEnd_255200 := by
    simpa [prefixWord, tailWord_255200, baseEnd_255200] using wordTrace_append hprefix tailTrace_255200
  have hstable : (prefixWord ++ tailWord_255200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255200).length < 2 ^ (prefixWord ++ tailWord_255200).sum := by decide
  have hdescent : baseEnd_255200 < baseStart_255200 := by decide
  rcases family_descends (prefixWord ++ tailWord_255200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255259 : List Nat := [1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_255259 : Nat := 118140960795 + 255259 * 2 ^ 59
def prefixEnd_255259 : Nat := 4983230072969 + 3 ^ 40 * 255259 * 2
def baseEnd_255259 : Nat := 77671442006590833593239

theorem tailTrace_255259 : CollatzResearch.WordTrace tailWord_255259 prefixEnd_255259 77671442006590833593239 := by
  unfold tailWord_255259
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310060582247712611552831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6206707054831808407701887 9310060582247712611552831)
  ·
    refine ⟨13965090873371568917329247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9310060582247712611552831 13965090873371568917329247)
    ·
      refine ⟨20947636310057353375993871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13965090873371568917329247 20947636310057353375993871)
      ·
        refine ⟨31421454465086030063990807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20947636310057353375993871 31421454465086030063990807)
        ·
          refine ⟨47132181697629045095986211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31421454465086030063990807 47132181697629045095986211)
          ·
            refine ⟨70698272546443567643979317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47132181697629045095986211 70698272546443567643979317)
            ·
              refine ⟨6627963051229084466623061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70698272546443567643979317 6627963051229084466623061)
              ·
                refine ⟨77671442006590833593239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6627963051229084466623061 77671442006590833593239)
                ·
                  rfl

theorem cell19_255259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_255259 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255259 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255259 prefixEnd_255259 := by exact prefixLift 255259
  have htrace : WordTrace (prefixWord ++ tailWord_255259) baseStart_255259 baseEnd_255259 := by
    simpa [prefixWord, tailWord_255259, baseEnd_255259] using wordTrace_append hprefix tailTrace_255259
  have hstable : (prefixWord ++ tailWord_255259).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255259).length < 2 ^ (prefixWord ++ tailWord_255259).sum := by decide
  have hdescent : baseEnd_255259 < baseStart_255259 := by decide
  rcases family_descends (prefixWord ++ tailWord_255259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255272 : List Nat := [2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_255272 : Nat := 118140960795 + 255272 * 2 ^ 59
def prefixEnd_255272 : Nat := 4983230072969 + 3 ^ 40 * 255272 * 2
def baseEnd_255272 : Nat := 77675397709410655304315

theorem tailTrace_255272 : CollatzResearch.WordTrace tailWord_255272 prefixEnd_255272 77675397709410655304315 := by
  unfold tailWord_255272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655267365600307915888035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6207023154133743887850713 4655267365600307915888035)
  ·
    refine ⟨6982901048400461873832053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4655267365600307915888035 6982901048400461873832053)
    ·
      refine ⟨654646973287543300671755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6982901048400461873832053 654646973287543300671755)
      ·
        refine ⟨981970459931314951007633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654646973287543300671755 981970459931314951007633)
        ·
          refine ⟨736477844948486213255725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981970459931314951007633 736477844948486213255725)
          ·
            refine ⟨276179191855682329970897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736477844948486213255725 276179191855682329970897)
            ·
              refine ⟨207134393891761747478173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276179191855682329970897 207134393891761747478173)
              ·
                refine ⟨77675397709410655304315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207134393891761747478173 77675397709410655304315)
                ·
                  rfl

theorem cell19_255272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_255272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255272 prefixEnd_255272 := by exact prefixLift 255272
  have htrace : WordTrace (prefixWord ++ tailWord_255272) baseStart_255272 baseEnd_255272 := by
    simpa [prefixWord, tailWord_255272, baseEnd_255272] using wordTrace_append hprefix tailTrace_255272
  have hstable : (prefixWord ++ tailWord_255272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255272).length < 2 ^ (prefixWord ++ tailWord_255272).sum := by decide
  have hdescent : baseEnd_255272 < baseStart_255272 := by decide
  rcases family_descends (prefixWord ++ tailWord_255272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255274 : List Nat := [3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_255274 : Nat := 118140960795 + 255274 * 2 ^ 59
def prefixEnd_255274 : Nat := 4983230072969 + 3 ^ 40 * 255274 * 2
def baseEnd_255274 : Nat := 77676006279075243259865

theorem tailTrace_255274 : CollatzResearch.WordTrace tailWord_255274 prefixEnd_255274 77676006279075243259865 := by
  unfold tailWord_255274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327651919298342543337219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6207071784795580115565917 2327651919298342543337219)
  ·
    refine ⟨3491477878947513815005829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327651919298342543337219 3491477878947513815005829)
    ·
      refine ⟨654652102302658840313593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3491477878947513815005829 654652102302658840313593)
      ·
        refine ⟨490989076726994130235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654652102302658840313593 490989076726994130235195)
        ·
          refine ⟨736483615090491195352793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490989076726994130235195 736483615090491195352793)
          ·
            refine ⟨552362711317868396514595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736483615090491195352793 552362711317868396514595)
            ·
              refine ⟨828544066976802594771893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552362711317868396514595 828544066976802594771893)
              ·
                refine ⟨77676006279075243259865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 828544066976802594771893 77676006279075243259865)
                ·
                  rfl

theorem cell19_255274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_255274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255274 prefixEnd_255274 := by exact prefixLift 255274
  have htrace : WordTrace (prefixWord ++ tailWord_255274) baseStart_255274 baseEnd_255274 := by
    simpa [prefixWord, tailWord_255274, baseEnd_255274] using wordTrace_append hprefix tailTrace_255274
  have hstable : (prefixWord ++ tailWord_255274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255274).length < 2 ^ (prefixWord ++ tailWord_255274).sum := by decide
  have hdescent : baseEnd_255274 < baseStart_255274 := by decide
  rcases family_descends (prefixWord ++ tailWord_255274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255295 : List Nat := [1, 1, 2, 2, 4, 4, 5]
def baseStart_255295 : Nat := 118140960795 + 255295 * 2 ^ 59
def prefixEnd_255295 : Nat := 4983230072969 + 3 ^ 40 * 255295 * 2
def baseEnd_255295 : Nat := 25894132086851138931047

theorem tailTrace_255295 : CollatzResearch.WordTrace tailWord_255295 prefixEnd_255295 25894132086851138931047 := by
  unfold tailWord_255295
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311373610117290759863339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6207582406744860506575559 9311373610117290759863339)
  ·
    refine ⟨13967060415175936139795009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9311373610117290759863339 13967060415175936139795009)
    ·
      refine ⟨10475295311381952104846257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13967060415175936139795009 10475295311381952104846257)
      ·
        refine ⟨7856471483536464078634693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10475295311381952104846257 7856471483536464078634693)
        ·
          refine ⟨1473088403163087014744005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7856471483536464078634693 1473088403163087014744005)
          ·
            refine ⟨276204075593078815264501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1473088403163087014744005 276204075593078815264501)
            ·
              refine ⟨25894132086851138931047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276204075593078815264501 25894132086851138931047)
              ·
                rfl

theorem cell19_255295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_255295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255295 prefixEnd_255295 := by exact prefixLift 255295
  have htrace : WordTrace (prefixWord ++ tailWord_255295) baseStart_255295 baseEnd_255295 := by
    simpa [prefixWord, tailWord_255295, baseEnd_255295] using wordTrace_append hprefix tailTrace_255295
  have hstable : (prefixWord ++ tailWord_255295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255295).length < 2 ^ (prefixWord ++ tailWord_255295).sum := by decide
  have hdescent : baseEnd_255295 < baseStart_255295 := by decide
  rcases family_descends (prefixWord ++ tailWord_255295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255369 : List Nat := [1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_255369 : Nat := 118140960795 + 255369 * 2 ^ 59
def prefixEnd_255369 : Nat := 4983230072969 + 3 ^ 40 * 255369 * 2
def baseEnd_255369 : Nat := 77704913338143171148495

theorem tailTrace_255369 : CollatzResearch.WordTrace tailWord_255369 prefixEnd_255369 77704913338143171148495 := by
  unfold tailWord_255369
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314072611849201398057161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6209381741232800932038107 9314072611849201398057161)
  ·
    refine ⟨6985554458886901048542871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9314072611849201398057161 6985554458886901048542871)
    ·
      refine ⟨10478331688330351572814307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6985554458886901048542871 10478331688330351572814307)
      ·
        refine ⟨15717497532495527359221461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478331688330351572814307 15717497532495527359221461)
        ·
          refine ⟨368378848417863922481753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15717497532495527359221461 368378848417863922481753)
          ·
            refine ⟨276284136313397941861315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368378848417863922481753 276284136313397941861315)
            ·
              refine ⟨414426204470096912791973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276284136313397941861315 414426204470096912791973)
              ·
                refine ⟨77704913338143171148495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414426204470096912791973 77704913338143171148495)
                ·
                  rfl

theorem cell19_255369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_255369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255369 prefixEnd_255369 := by exact prefixLift 255369
  have htrace : WordTrace (prefixWord ++ tailWord_255369) baseStart_255369 baseEnd_255369 := by
    simpa [prefixWord, tailWord_255369, baseEnd_255369] using wordTrace_append hprefix tailTrace_255369
  have hstable : (prefixWord ++ tailWord_255369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255369).length < 2 ^ (prefixWord ++ tailWord_255369).sum := by decide
  have hdescent : baseEnd_255369 < baseStart_255369 := by decide
  rcases family_descends (prefixWord ++ tailWord_255369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255485 : List Nat := [1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_255485 : Nat := 118140960795 + 255485 * 2 ^ 59
def prefixEnd_255485 : Nat := 4983230072969 + 3 ^ 40 * 255485 * 2
def baseEnd_255485 : Nat := 77740210378689272570401

theorem tailTrace_255485 : CollatzResearch.WordTrace tailWord_255485 prefixEnd_255485 77740210378689272570401 := by
  unfold tailWord_255485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318303479428953209279909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6212202319619302139519939 9318303479428953209279909)
  ·
    refine ⟨1747181902392928726739983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9318303479428953209279909 1747181902392928726739983)
    ·
      refine ⟨2620772853589393090109975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747181902392928726739983 2620772853589393090109975)
      ·
        refine ⟨3931159280384089635164963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620772853589393090109975 3931159280384089635164963)
        ·
          refine ⟨5896738920576134452747445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931159280384089635164963 5896738920576134452747445)
          ·
            refine ⟨552819273804012604945073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5896738920576134452747445 552819273804012604945073)
            ·
              refine ⟨414614455353009453708805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552819273804012604945073 414614455353009453708805)
              ·
                refine ⟨77740210378689272570401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414614455353009453708805 77740210378689272570401)
                ·
                  rfl

theorem cell19_255485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_255485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255485 prefixEnd_255485 := by exact prefixLift 255485
  have htrace : WordTrace (prefixWord ++ tailWord_255485) baseStart_255485 baseEnd_255485 := by
    simpa [prefixWord, tailWord_255485, baseEnd_255485] using wordTrace_append hprefix tailTrace_255485
  have hstable : (prefixWord ++ tailWord_255485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255485).length < 2 ^ (prefixWord ++ tailWord_255485).sum := by decide
  have hdescent : baseEnd_255485 < baseStart_255485 := by decide
  rcases family_descends (prefixWord ++ tailWord_255485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255523 : List Nat := [1, 1, 1, 4, 6, 6]
def baseStart_255523 : Nat := 118140960795 + 255523 * 2 ^ 59
def prefixEnd_255523 : Nat := 4983230072969 + 3 ^ 40 * 255523 * 2
def baseEnd_255523 : Nat := 8639085911368493747317

theorem tailTrace_255523 : CollatzResearch.WordTrace tailWord_255523 prefixEnd_255523 8639085911368493747317 := by
  unfold tailWord_255523
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319689453291285699163223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6213126302194190466108815 9319689453291285699163223)
  ·
    refine ⟨13979534179936928548744835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9319689453291285699163223 13979534179936928548744835)
    ·
      refine ⟨20969301269905392823117253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979534179936928548744835 20969301269905392823117253)
      ·
        refine ⟨3931743988107261154334485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20969301269905392823117253 3931743988107261154334485)
        ·
          refine ⟨184300499442527866609429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3931743988107261154334485 184300499442527866609429)
          ·
            refine ⟨8639085911368493747317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184300499442527866609429 8639085911368493747317)
            ·
              rfl

theorem cell19_255523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_255523 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255523 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255523 prefixEnd_255523 := by exact prefixLift 255523
  have htrace : WordTrace (prefixWord ++ tailWord_255523) baseStart_255523 baseEnd_255523 := by
    simpa [prefixWord, tailWord_255523, baseEnd_255523] using wordTrace_append hprefix tailTrace_255523
  have hstable : (prefixWord ++ tailWord_255523).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255523).length < 2 ^ (prefixWord ++ tailWord_255523).sum := by decide
  have hdescent : baseEnd_255523 < baseStart_255523 := by decide
  rcases family_descends (prefixWord ++ tailWord_255523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255559 : List Nat := [1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_255559 : Nat := 118140960795 + 255559 * 2 ^ 59
def prefixEnd_255559 : Nat := 4983230072969 + 3 ^ 40 * 255559 * 2
def baseEnd_255559 : Nat := 77762727456279026925755

theorem tailTrace_255559 : CollatzResearch.WordTrace tailWord_255559 prefixEnd_255559 77762727456279026925755 := by
  unfold tailWord_255559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321002481160863847473731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6214001654107242564982487 9321002481160863847473731)
  ·
    refine ⟨13981503721741295771210597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9321002481160863847473731 13981503721741295771210597)
    ·
      refine ⟨2621531947826492957101987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13981503721741295771210597 2621531947826492957101987)
      ·
        refine ⟨3932297921739739435652981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621531947826492957101987 3932297921739739435652981)
        ·
          refine ⟨368652930163100572092467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3932297921739739435652981 368652930163100572092467)
          ·
            refine ⟨552979395244650858138701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368652930163100572092467 552979395244650858138701)
            ·
              refine ⟨207367273216744071802013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552979395244650858138701 207367273216744071802013)
              ·
                refine ⟨77762727456279026925755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207367273216744071802013 77762727456279026925755)
                ·
                  rfl

theorem cell19_255559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_255559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255559 prefixEnd_255559 := by exact prefixLift 255559
  have htrace : WordTrace (prefixWord ++ tailWord_255559) baseStart_255559 baseEnd_255559 := by
    simpa [prefixWord, tailWord_255559, baseEnd_255559] using wordTrace_append hprefix tailTrace_255559
  have hstable : (prefixWord ++ tailWord_255559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255559).length < 2 ^ (prefixWord ++ tailWord_255559).sum := by decide
  have hdescent : baseEnd_255559 < baseStart_255559 := by decide
  rcases family_descends (prefixWord ++ tailWord_255559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255580 : List Nat := [2, 2, 4, 1, 2, 2, 6]
def baseStart_255580 : Nat := 118140960795 + 255580 * 2 ^ 59
def prefixEnd_255580 : Nat := 4983230072969 + 3 ^ 40 * 255580 * 2
def baseEnd_255580 : Nat := 25923039145919066819677

theorem tailTrace_255580 : CollatzResearch.WordTrace tailWord_255580 prefixEnd_255580 25923039145919066819677 := by
  unfold tailWord_255580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660884207042392216994097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6214512276056522955992129 4660884207042392216994097)
  ·
    refine ⟨3495663155281794162745573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4660884207042392216994097 3495663155281794162745573)
    ·
      refine ⟨655436841615336405514795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3495663155281794162745573 655436841615336405514795)
      ·
        refine ⟨983155262423004608272193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655436841615336405514795 983155262423004608272193)
        ·
          refine ⟨737366446817253456204145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983155262423004608272193 737366446817253456204145)
          ·
            refine ⟨553024835112940092153109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737366446817253456204145 553024835112940092153109)
            ·
              refine ⟨25923039145919066819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553024835112940092153109 25923039145919066819677)
              ·
                rfl

theorem cell19_255580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_255580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255580 prefixEnd_255580 := by exact prefixLift 255580
  have htrace : WordTrace (prefixWord ++ tailWord_255580) baseStart_255580 baseEnd_255580 := by
    simpa [prefixWord, tailWord_255580, baseEnd_255580] using wordTrace_append hprefix tailTrace_255580
  have hstable : (prefixWord ++ tailWord_255580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255580).length < 2 ^ (prefixWord ++ tailWord_255580).sum := by decide
  have hdescent : baseEnd_255580 < baseStart_255580 := by decide
  rcases family_descends (prefixWord ++ tailWord_255580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255639 : List Nat := [1, 1, 3, 3, 2, 2, 7]
def baseStart_255639 : Nat := 118140960795 + 255639 * 2 ^ 59
def prefixEnd_255639 : Nat := 4983230072969 + 3 ^ 40 * 255639 * 2
def baseEnd_255639 : Nat := 25929023414287515049253

theorem tailTrace_255639 : CollatzResearch.WordTrace tailWord_255639 prefixEnd_255639 25929023414287515049253 := by
  unfold tailWord_255639
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323920320871037510385971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6215946880580691673590647 9323920320871037510385971)
  ·
    refine ⟨13985880481306556265578957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9323920320871037510385971 13985880481306556265578957)
    ·
      refine ⟨5244705180489958599592109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13985880481306556265578957 5244705180489958599592109)
      ·
        refine ⟨1966764442683734474847041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5244705180489958599592109 1966764442683734474847041)
        ·
          refine ⟨1475073332012800856135281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966764442683734474847041 1475073332012800856135281)
          ·
            refine ⟨1106304999009600642101461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475073332012800856135281 1106304999009600642101461)
            ·
              refine ⟨25929023414287515049253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1106304999009600642101461 25929023414287515049253)
              ·
                rfl

theorem cell19_255639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_255639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255639 prefixEnd_255639 := by exact prefixLift 255639
  have htrace : WordTrace (prefixWord ++ tailWord_255639) baseStart_255639 baseEnd_255639 := by
    simpa [prefixWord, tailWord_255639, baseEnd_255639] using wordTrace_append hprefix tailTrace_255639
  have hstable : (prefixWord ++ tailWord_255639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255639).length < 2 ^ (prefixWord ++ tailWord_255639).sum := by decide
  have hdescent : baseEnd_255639 < baseStart_255639 := by decide
  rcases family_descends (prefixWord ++ tailWord_255639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255677 : List Nat := [1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_255677 : Nat := 118140960795 + 255677 * 2 ^ 59
def prefixEnd_255677 : Nat := 4983230072969 + 3 ^ 40 * 255677 * 2
def baseEnd_255677 : Nat := 77798633066489716303211

theorem tailTrace_255677 : CollatzResearch.WordTrace tailWord_255677 prefixEnd_255677 77798633066489716303211 := by
  unfold tailWord_255677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325306294733370000269285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6216870863155580000179523 9325306294733370000269285)
  ·
    refine ⟨1748494930262506875050491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9325306294733370000269285 1748494930262506875050491)
    ·
      refine ⟨2622742395393760312575737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748494930262506875050491 2622742395393760312575737)
      ·
        refine ⟨1967056796545320234431803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622742395393760312575737 1967056796545320234431803)
        ·
          refine ⟨2950585194817980351647705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967056796545320234431803 2950585194817980351647705)
          ·
            refine ⟨2212938896113485263735779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950585194817980351647705 2212938896113485263735779)
            ·
              refine ⟨3319408344170227895603669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212938896113485263735779 3319408344170227895603669)
              ·
                refine ⟨77798633066489716303211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3319408344170227895603669 77798633066489716303211)
                ·
                  rfl

theorem cell19_255677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_255677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255677 prefixEnd_255677 := by exact prefixLift 255677
  have htrace : WordTrace (prefixWord ++ tailWord_255677) baseStart_255677 baseEnd_255677 := by
    simpa [prefixWord, tailWord_255677, baseEnd_255677] using wordTrace_append hprefix tailTrace_255677
  have hstable : (prefixWord ++ tailWord_255677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255677).length < 2 ^ (prefixWord ++ tailWord_255677).sum := by decide
  have hdescent : baseEnd_255677 < baseStart_255677 := by decide
  rcases family_descends (prefixWord ++ tailWord_255677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255709 : List Nat := [1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_255709 : Nat := 118140960795 + 255709 * 2 ^ 59
def prefixEnd_255709 : Nat := 4983230072969 + 3 ^ 40 * 255709 * 2
def baseEnd_255709 : Nat := 77808370181123123592013

theorem tailTrace_255709 : CollatzResearch.WordTrace tailWord_255709 prefixEnd_255709 77808370181123123592013 := by
  unfold tailWord_255709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326473430617439465434181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217648953744959643622787 9326473430617439465434181)
  ·
    refine ⟨1748713768240769899768909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9326473430617439465434181 1748713768240769899768909)
    ·
      refine ⟨655767663090288712413341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1748713768240769899768909 655767663090288712413341)
      ·
        refine ⟨245912873658858267155003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655767663090288712413341 245912873658858267155003)
        ·
          refine ⟨368869310488287400732505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245912873658858267155003 368869310488287400732505)
          ·
            refine ⟨276651982866215550549379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368869310488287400732505 276651982866215550549379)
            ·
              refine ⟨414977974299323325824069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276651982866215550549379 414977974299323325824069)
              ·
                refine ⟨77808370181123123592013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414977974299323325824069 77808370181123123592013)
                ·
                  rfl

theorem cell19_255709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_255709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255709 prefixEnd_255709 := by exact prefixLift 255709
  have htrace : WordTrace (prefixWord ++ tailWord_255709) baseStart_255709 baseEnd_255709 := by
    simpa [prefixWord, tailWord_255709, baseEnd_255709] using wordTrace_append hprefix tailTrace_255709
  have hstable : (prefixWord ++ tailWord_255709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255709).length < 2 ^ (prefixWord ++ tailWord_255709).sum := by decide
  have hdescent : baseEnd_255709 < baseStart_255709 := by decide
  rcases family_descends (prefixWord ++ tailWord_255709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255751 : List Nat := [1, 1, 4, 4, 2, 1, 6]
def baseStart_255751 : Nat := 118140960795 + 255751 * 2 ^ 59
def prefixEnd_255751 : Nat := 4983230072969 + 3 ^ 40 * 255751 * 2
def baseEnd_255751 : Nat := 25940383381359823552855

theorem tailTrace_255751 : CollatzResearch.WordTrace tailWord_255751 prefixEnd_255751 25940383381359823552855 := by
  unfold tailWord_255751
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328005296465280638463107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6218670197643520425642071 9328005296465280638463107)
  ·
    refine ⟨13992007944697920957694661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9328005296465280638463107 13992007944697920957694661)
    ·
      refine ⟨2623501489630860179567749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13992007944697920957694661 2623501489630860179567749)
      ·
        refine ⟨491906529305786283668953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2623501489630860179567749 491906529305786283668953)
        ·
          refine ⟨368929896979339712751715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491906529305786283668953 368929896979339712751715)
          ·
            refine ⟨553394845469009569127573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368929896979339712751715 553394845469009569127573)
            ·
              refine ⟨25940383381359823552855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553394845469009569127573 25940383381359823552855)
              ·
                rfl

theorem cell19_255751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_255751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255751 prefixEnd_255751 := by exact prefixLift 255751
  have htrace : WordTrace (prefixWord ++ tailWord_255751) baseStart_255751 baseEnd_255751 := by
    simpa [prefixWord, tailWord_255751, baseEnd_255751] using wordTrace_append hprefix tailTrace_255751
  have hstable : (prefixWord ++ tailWord_255751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255751).length < 2 ^ (prefixWord ++ tailWord_255751).sum := by decide
  have hdescent : baseEnd_255751 < baseStart_255751 := by decide
  rcases family_descends (prefixWord ++ tailWord_255751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255772 : List Nat := [2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_255772 : Nat := 118140960795 + 255772 * 2 ^ 59
def prefixEnd_255772 : Nat := 4983230072969 + 3 ^ 40 * 255772 * 2
def baseEnd_255772 : Nat := 77827540125557644191841

theorem tailTrace_255772 : CollatzResearch.WordTrace tailWord_255772 prefixEnd_255772 77827540125557644191841 := by
  unfold tailWord_255772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664385614694600612488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6219180819592800816651713 4664385614694600612488785)
  ·
    refine ⟨3498289211020950459366589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4664385614694600612488785 3498289211020950459366589)
    ·
      refine ⟨1311858454132856422262471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3498289211020950459366589 1311858454132856422262471)
      ·
        refine ⟨1967787681199284633393707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311858454132856422262471 1967787681199284633393707)
        ·
          refine ⟨2951681521798926950090561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967787681199284633393707 2951681521798926950090561)
          ·
            refine ⟨2213761141349195212567921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951681521798926950090561 2213761141349195212567921)
            ·
              refine ⟨1660320856011896409425941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213761141349195212567921 1660320856011896409425941)
              ·
                refine ⟨77827540125557644191841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1660320856011896409425941 77827540125557644191841)
                ·
                  rfl

theorem cell19_255772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_255772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255772 prefixEnd_255772 := by exact prefixLift 255772
  have htrace : WordTrace (prefixWord ++ tailWord_255772) baseStart_255772 baseEnd_255772 := by
    simpa [prefixWord, tailWord_255772, baseEnd_255772] using wordTrace_append hprefix tailTrace_255772
  have hstable : (prefixWord ++ tailWord_255772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255772).length < 2 ^ (prefixWord ++ tailWord_255772).sum := by decide
  have hdescent : baseEnd_255772 < baseStart_255772 := by decide
  rcases family_descends (prefixWord ++ tailWord_255772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255829 : List Nat := [1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_255829 : Nat := 118140960795 + 255829 * 2 ^ 59
def prefixEnd_255829 : Nat := 4983230072969 + 3 ^ 40 * 255829 * 2
def baseEnd_255829 : Nat := 77844884360998400925019

theorem tailTrace_255829 : CollatzResearch.WordTrace tailWord_255829 prefixEnd_255829 77844884360998400925019 := by
  unfold tailWord_255829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330850190182699959802541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6220566793455133306535027 9330850190182699959802541)
  ·
    refine ⟨3499068821318512484925953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9330850190182699959802541 3499068821318512484925953)
    ·
      refine ⟨2624301615988884363694465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499068821318512484925953 2624301615988884363694465)
      ·
        refine ⟨1968226211991663272770849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624301615988884363694465 1968226211991663272770849)
        ·
          refine ⟨1476169658993747454578137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968226211991663272770849 1476169658993747454578137)
          ·
            refine ⟨1107127244245310590933603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476169658993747454578137 1107127244245310590933603)
            ·
              refine ⟨1660690866367965886400405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107127244245310590933603 1660690866367965886400405)
              ·
                refine ⟨77844884360998400925019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1660690866367965886400405 77844884360998400925019)
                ·
                  rfl

theorem cell19_255829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_255829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255829 prefixEnd_255829 := by exact prefixLift 255829
  have htrace : WordTrace (prefixWord ++ tailWord_255829) baseStart_255829 baseEnd_255829 := by
    simpa [prefixWord, tailWord_255829, baseEnd_255829] using wordTrace_append hprefix tailTrace_255829
  have hstable : (prefixWord ++ tailWord_255829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255829).length < 2 ^ (prefixWord ++ tailWord_255829).sum := by decide
  have hdescent : baseEnd_255829 < baseStart_255829 := by decide
  rcases family_descends (prefixWord ++ tailWord_255829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255848 : List Nat := [2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_255848 : Nat := 118140960795 + 255848 * 2 ^ 59
def prefixEnd_255848 : Nat := 4983230072969 + 3 ^ 40 * 255848 * 2
def baseEnd_255848 : Nat := 77850665772811986502745

theorem tailTrace_255848 : CollatzResearch.WordTrace tailWord_255848 prefixEnd_255848 77850665772811986502745 := by
  unfold tailWord_255848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665771588556933102372099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6221028784742577469829465 4665771588556933102372099)
  ·
    refine ⟨6998657382835399653558149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665771588556933102372099 6998657382835399653558149)
    ·
      refine ⟨1312248259281637435042153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6998657382835399653558149 1312248259281637435042153)
      ·
        refine ⟨984186194461228076281615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1312248259281637435042153 984186194461228076281615)
        ·
          refine ⟨1476279291691842114422423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984186194461228076281615 1476279291691842114422423)
          ·
            refine ⟨2214418937537763171633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476279291691842114422423 2214418937537763171633635)
            ·
              refine ⟨3321628406306644757450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214418937537763171633635 3321628406306644757450453)
              ·
                refine ⟨77850665772811986502745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3321628406306644757450453 77850665772811986502745)
                ·
                  rfl

theorem cell19_255848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_255848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255848 prefixEnd_255848 := by exact prefixLift 255848
  have htrace : WordTrace (prefixWord ++ tailWord_255848) baseStart_255848 baseEnd_255848 := by
    simpa [prefixWord, tailWord_255848, baseEnd_255848] using wordTrace_append hprefix tailTrace_255848
  have hstable : (prefixWord ++ tailWord_255848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255848).length < 2 ^ (prefixWord ++ tailWord_255848).sum := by decide
  have hdescent : baseEnd_255848 < baseStart_255848 := by decide
  rcases family_descends (prefixWord ++ tailWord_255848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255882 : List Nat := [3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_255882 : Nat := 118140960795 + 255882 * 2 ^ 59
def prefixEnd_255882 : Nat := 4983230072969 + 3 ^ 40 * 255882 * 2
def baseEnd_255882 : Nat := 77861011457109981747097

theorem tailTrace_255882 : CollatzResearch.WordTrace tailWord_255882 prefixEnd_255882 77861011457109981747097 := by
  unfold tailWord_255882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333195814747672502870475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6221855505993793340987933 2333195814747672502870475)
  ·
    refine ⟨3499793722121508754305713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333195814747672502870475 3499793722121508754305713)
    ·
      refine ⟨2624845291591131565729285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499793722121508754305713 2624845291591131565729285)
      ·
        refine ⟨492158492173337168574241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2624845291591131565729285 492158492173337168574241)
        ·
          refine ⟨369118869130002876430681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492158492173337168574241 369118869130002876430681)
          ·
            refine ⟨276839151847502157323011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369118869130002876430681 276839151847502157323011)
            ·
              refine ⟨415258727771253235984517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276839151847502157323011 415258727771253235984517)
              ·
                refine ⟨77861011457109981747097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415258727771253235984517 77861011457109981747097)
                ·
                  rfl

theorem cell19_255882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_255882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255882 prefixEnd_255882 := by exact prefixLift 255882
  have htrace : WordTrace (prefixWord ++ tailWord_255882) baseStart_255882 baseEnd_255882 := by
    simpa [prefixWord, tailWord_255882, baseEnd_255882] using wordTrace_append hprefix tailTrace_255882
  have hstable : (prefixWord ++ tailWord_255882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255882).length < 2 ^ (prefixWord ++ tailWord_255882).sum := by decide
  have hdescent : baseEnd_255882 < baseStart_255882 := by decide
  rcases family_descends (prefixWord ++ tailWord_255882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255918 : List Nat := [4, 1, 5, 1, 1, 1, 6]
def baseStart_255918 : Nat := 118140960795 + 255918 * 2 ^ 59
def prefixEnd_255918 : Nat := 4983230072969 + 3 ^ 40 * 255918 * 2
def baseEnd_255918 : Nat := 25957321903690854982333

theorem tailTrace_255918 : CollatzResearch.WordTrace tailWord_255918 prefixEnd_255918 25957321903690854982333 := by
  unfold tailWord_255918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166762035857533519974051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6222730857906845439861605 1166762035857533519974051)
  ·
    refine ⟨1750143053786300279961077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166762035857533519974051 1750143053786300279961077)
    ·
      refine ⟨164075911292465651246351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1750143053786300279961077 164075911292465651246351)
      ·
        refine ⟨246113866938698476869527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164075911292465651246351 246113866938698476869527)
        ·
          refine ⟨369170800408047715304291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246113866938698476869527 369170800408047715304291)
          ·
            refine ⟨553756200612071572956437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369170800408047715304291 553756200612071572956437)
            ·
              refine ⟨25957321903690854982333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553756200612071572956437 25957321903690854982333)
              ·
                rfl

theorem cell19_255918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_255918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255918 prefixEnd_255918 := by exact prefixLift 255918
  have htrace : WordTrace (prefixWord ++ tailWord_255918) baseStart_255918 baseEnd_255918 := by
    simpa [prefixWord, tailWord_255918, baseEnd_255918] using wordTrace_append hprefix tailTrace_255918
  have hstable : (prefixWord ++ tailWord_255918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255918).length < 2 ^ (prefixWord ++ tailWord_255918).sum := by decide
  have hdescent : baseEnd_255918 < baseStart_255918 := by decide
  rcases family_descends (prefixWord ++ tailWord_255918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255958 : List Nat := [5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_255958 : Nat := 118140960795 + 255958 * 2 ^ 59
def prefixEnd_255958 : Nat := 4983230072969 + 3 ^ 40 * 255958 * 2
def baseEnd_255958 : Nat := 77884137104364324058001

theorem tailTrace_255958 : CollatzResearch.WordTrace tailWord_255958 prefixEnd_255958 77884137104364324058001 := by
  unfold tailWord_255958
  simp only [CollatzResearch.WordTrace]
  refine ⟨583472200419709686953033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6223703471143569994165685 583472200419709686953033)
  ·
    refine ⟨437604150314782265214775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583472200419709686953033 437604150314782265214775)
    ·
      refine ⟨656406225472173397822163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437604150314782265214775 656406225472173397822163)
      ·
        refine ⟨984609338208260096733245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656406225472173397822163 984609338208260096733245)
        ·
          refine ⟨369228501828097536274967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984609338208260096733245 369228501828097536274967)
          ·
            refine ⟨553842752742146304412451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369228501828097536274967 553842752742146304412451)
            ·
              refine ⟨830764129113219456618677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553842752742146304412451 830764129113219456618677)
              ·
                refine ⟨77884137104364324058001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830764129113219456618677 77884137104364324058001)
                ·
                  rfl

theorem cell19_255958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_255958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255958 prefixEnd_255958 := by exact prefixLift 255958
  have htrace : WordTrace (prefixWord ++ tailWord_255958) baseStart_255958 baseEnd_255958 := by
    simpa [prefixWord, tailWord_255958, baseEnd_255958] using wordTrace_append hprefix tailTrace_255958
  have hstable : (prefixWord ++ tailWord_255958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255958).length < 2 ^ (prefixWord ++ tailWord_255958).sum := by decide
  have hdescent : baseEnd_255958 < baseStart_255958 := by decide
  rcases family_descends (prefixWord ++ tailWord_255958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255998 : List Nat := [4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_255998 : Nat := 118140960795 + 255998 * 2 ^ 59
def prefixEnd_255998 : Nat := 4983230072969 + 3 ^ 40 * 255998 * 2
def baseEnd_255998 : Nat := 77896308497656083169003

theorem tailTrace_255998 : CollatzResearch.WordTrace tailWord_255998 prefixEnd_255998 77896308497656083169003 := by
  unfold tailWord_255998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167126765821305227838081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6224676084380294548469765 1167126765821305227838081)
  ·
    refine ⟨875345074365978920878561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1167126765821305227838081 875345074365978920878561)
    ·
      refine ⟨656508805774484190658921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875345074365978920878561 656508805774484190658921)
      ·
        refine ⟨492381604330863142994191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656508805774484190658921 492381604330863142994191)
        ·
          refine ⟨738572406496294714491287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492381604330863142994191 738572406496294714491287)
          ·
            refine ⟨1107858609744442071736931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738572406496294714491287 1107858609744442071736931)
            ·
              refine ⟨1661787914616663107605397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107858609744442071736931 1661787914616663107605397)
              ·
                refine ⟨77896308497656083169003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1661787914616663107605397 77896308497656083169003)
                ·
                  rfl

theorem cell19_255998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_255998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_255998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_255998 prefixEnd_255998 := by exact prefixLift 255998
  have htrace : WordTrace (prefixWord ++ tailWord_255998) baseStart_255998 baseEnd_255998 := by
    simpa [prefixWord, tailWord_255998, baseEnd_255998] using wordTrace_append hprefix tailTrace_255998
  have hstable : (prefixWord ++ tailWord_255998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255998).length < 2 ^ (prefixWord ++ tailWord_255998).sum := by decide
  have hdescent : baseEnd_255998 < baseStart_255998 := by decide
  rcases family_descends (prefixWord ++ tailWord_255998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256036 : List Nat := [2, 3, 1, 4, 3, 6]
def baseStart_256036 : Nat := 118140960795 + 256036 * 2 ^ 59
def prefixEnd_256036 : Nat := 4983230072969 + 3 ^ 40 * 256036 * 2
def baseEnd_256036 : Nat := 8656430146809250480495

theorem tailTrace_256036 : CollatzResearch.WordTrace tailWord_256036 prefixEnd_256036 8656430146809250480495 := by
  unfold tailWord_256036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669200050216387156293981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6225600066955182875058641 4669200050216387156293981)
  ·
    refine ⟨1750950018831145183610243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4669200050216387156293981 1750950018831145183610243)
    ·
      refine ⟨2626425028246717775415365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750950018831145183610243 2626425028246717775415365)
      ·
        refine ⟨492454692796259582890381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2626425028246717775415365 492454692796259582890381)
        ·
          refine ⟨184670509798597343583893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492454692796259582890381 184670509798597343583893)
          ·
            refine ⟨8656430146809250480495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184670509798597343583893 8656430146809250480495)
            ·
              rfl

theorem cell19_256036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_256036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256036 prefixEnd_256036 := by exact prefixLift 256036
  have htrace : WordTrace (prefixWord ++ tailWord_256036) baseStart_256036 baseEnd_256036 := by
    simpa [prefixWord, tailWord_256036, baseEnd_256036] using wordTrace_append hprefix tailTrace_256036
  have hstable : (prefixWord ++ tailWord_256036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256036).length < 2 ^ (prefixWord ++ tailWord_256036).sum := by decide
  have hdescent : baseEnd_256036 < baseStart_256036 := by decide
  rcases family_descends (prefixWord ++ tailWord_256036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256093 : List Nat := [1, 4, 4, 1, 1, 2, 6]
def baseStart_256093 : Nat := 118140960795 + 256093 * 2 ^ 59
def prefixEnd_256093 : Nat := 4983230072969 + 3 ^ 40 * 256093 * 2
def baseEnd_256093 : Nat := 25975071852241337019211

theorem tailTrace_256093 : CollatzResearch.WordTrace tailWord_256093 prefixEnd_256093 25975071852241337019211 := by
  unfold tailWord_256093
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340479061226273047412933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6226986040817515364941955 9340479061226273047412933)
  ·
    refine ⟨1751339823979926196389925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9340479061226273047412933 1751339823979926196389925)
    ·
      refine ⟨328376216996236161823111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1751339823979926196389925 328376216996236161823111)
      ·
        refine ⟨492564325494354242734667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328376216996236161823111 492564325494354242734667)
        ·
          refine ⟨738846488241531364102001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492564325494354242734667 738846488241531364102001)
          ·
            refine ⟨554134866181148523076501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738846488241531364102001 554134866181148523076501)
            ·
              refine ⟨25975071852241337019211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554134866181148523076501 25975071852241337019211)
              ·
                rfl

theorem cell19_256093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_256093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256093 prefixEnd_256093 := by exact prefixLift 256093
  have htrace : WordTrace (prefixWord ++ tailWord_256093) baseStart_256093 baseEnd_256093 := by
    simpa [prefixWord, tailWord_256093, baseEnd_256093] using wordTrace_append hprefix tailTrace_256093
  have hstable : (prefixWord ++ tailWord_256093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256093).length < 2 ^ (prefixWord ++ tailWord_256093).sum := by decide
  have hdescent : baseEnd_256093 < baseStart_256093 := by decide
  rcases family_descends (prefixWord ++ tailWord_256093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256129 : List Nat := [1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_256129 : Nat := 118140960795 + 256129 * 2 ^ 59
def prefixEnd_256129 : Nat := 4983230072969 + 3 ^ 40 * 256129 * 2
def baseEnd_256129 : Nat := 77936169810686594257535

theorem tailTrace_256129 : CollatzResearch.WordTrace tailWord_256129 prefixEnd_256129 77936169810686594257535 := by
  unfold tailWord_256129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341792089095851195723441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227861392730567463815627 9341792089095851195723441)
  ·
    refine ⟨7006344066821888396792581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9341792089095851195723441 7006344066821888396792581)
    ·
      refine ⟨1313689512529104074398609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7006344066821888396792581 1313689512529104074398609)
      ·
        refine ⟨985267134396828055798957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313689512529104074398609 985267134396828055798957)
        ·
          refine ⟨369475175398810520924609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985267134396828055798957 369475175398810520924609)
          ·
            refine ⟨277106381549107890693457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369475175398810520924609 277106381549107890693457)
            ·
              refine ⟨207829786161830918020093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277106381549107890693457 207829786161830918020093)
              ·
                refine ⟨77936169810686594257535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207829786161830918020093 77936169810686594257535)
                ·
                  rfl

theorem cell19_256129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_256129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256129 prefixEnd_256129 := by exact prefixLift 256129
  have htrace : WordTrace (prefixWord ++ tailWord_256129) baseStart_256129 baseEnd_256129 := by
    simpa [prefixWord, tailWord_256129, baseEnd_256129] using wordTrace_append hprefix tailTrace_256129
  have hstable : (prefixWord ++ tailWord_256129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256129).length < 2 ^ (prefixWord ++ tailWord_256129).sum := by decide
  have hdescent : baseEnd_256129 < baseStart_256129 := by decide
  rcases family_descends (prefixWord ++ tailWord_256129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256131 : List Nat := [1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_256131 : Nat := 118140960795 + 256131 * 2 ^ 59
def prefixEnd_256131 : Nat := 4983230072969 + 3 ^ 40 * 256131 * 2
def baseEnd_256131 : Nat := 77936778380351182213085

theorem tailTrace_256131 : CollatzResearch.WordTrace tailWord_256131 prefixEnd_256131 77936778380351182213085 := by
  unfold tailWord_256131
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341865035088605537296247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227910023392403691530831 9341865035088605537296247)
  ·
    refine ⟨14012797552632908305944371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9341865035088605537296247 14012797552632908305944371)
    ·
      refine ⟨21019196328949362458916557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012797552632908305944371 21019196328949362458916557)
      ·
        refine ⟨7882198623356010922093709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21019196328949362458916557 7882198623356010922093709)
        ·
          refine ⟨2955824483758504095785141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7882198623356010922093709 2955824483758504095785141)
          ·
            refine ⟨277108545352359758979857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2955824483758504095785141 277108545352359758979857)
            ·
              refine ⟨207831409014269819234893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277108545352359758979857 207831409014269819234893)
              ·
                refine ⟨77936778380351182213085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207831409014269819234893 77936778380351182213085)
                ·
                  rfl

theorem cell19_256131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_256131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256131 prefixEnd_256131 := by exact prefixLift 256131
  have htrace : WordTrace (prefixWord ++ tailWord_256131) baseStart_256131 baseEnd_256131 := by
    simpa [prefixWord, tailWord_256131, baseEnd_256131] using wordTrace_append hprefix tailTrace_256131
  have hstable : (prefixWord ++ tailWord_256131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256131).length < 2 ^ (prefixWord ++ tailWord_256131).sum := by decide
  have hdescent : baseEnd_256131 < baseStart_256131 := by decide
  rcases family_descends (prefixWord ++ tailWord_256131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256133 : List Nat := [1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_256133 : Nat := 118140960795 + 256133 * 2 ^ 59
def prefixEnd_256133 : Nat := 4983230072969 + 3 ^ 40 * 256133 * 2
def baseEnd_256133 : Nat := 77937386950015770168635

theorem tailTrace_256133 : CollatzResearch.WordTrace tailWord_256133 prefixEnd_256133 77937386950015770168635 := by
  unfold tailWord_256133
  simp only [CollatzResearch.WordTrace]
  refine ⟨9341937981081359878869053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227958654054239919246035 9341937981081359878869053)
  ·
    refine ⟨3503226742905509954575895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9341937981081359878869053 3503226742905509954575895)
    ·
      refine ⟨5254840114358264931863843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503226742905509954575895 5254840114358264931863843)
      ·
        refine ⟨7882260171537397397795765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254840114358264931863843 7882260171537397397795765)
        ·
          refine ⟨738961891081631006043353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7882260171537397397795765 738961891081631006043353)
          ·
            refine ⟨554221418311223254532515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738961891081631006043353 554221418311223254532515)
            ·
              refine ⟨831332127466834881798773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554221418311223254532515 831332127466834881798773)
              ·
                refine ⟨77937386950015770168635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 831332127466834881798773 77937386950015770168635)
                ·
                  rfl

theorem cell19_256133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_256133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256133 prefixEnd_256133 := by exact prefixLift 256133
  have htrace : WordTrace (prefixWord ++ tailWord_256133) baseStart_256133 baseEnd_256133 := by
    simpa [prefixWord, tailWord_256133, baseEnd_256133] using wordTrace_append hprefix tailTrace_256133
  have hstable : (prefixWord ++ tailWord_256133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256133).length < 2 ^ (prefixWord ++ tailWord_256133).sum := by decide
  have hdescent : baseEnd_256133 < baseStart_256133 := by decide
  rcases family_descends (prefixWord ++ tailWord_256133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256148 : List Nat := [2, 4, 2, 3, 1, 2, 5]
def baseStart_256148 : Nat := 118140960795 + 256148 * 2 ^ 59
def prefixEnd_256148 : Nat := 4983230072969 + 3 ^ 40 * 256148 * 2
def baseEnd_256148 : Nat := 25980650407500059945087

theorem tailTrace_256148 : CollatzResearch.WordTrace tailWord_256148 prefixEnd_256148 25980650407500059945087 := by
  unfold tailWord_256148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671242538013508720332549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6228323384018011627110065 4671242538013508720332549)
  ·
    refine ⟨875857975877532885062353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4671242538013508720332549 875857975877532885062353)
    ·
      refine ⟨656893481908149663796765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875857975877532885062353 656893481908149663796765)
      ·
        refine ⟨246335055715556123923787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656893481908149663796765 246335055715556123923787)
        ·
          refine ⟨369502583573334185885681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246335055715556123923787 369502583573334185885681)
          ·
            refine ⟨277126937680000639414261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369502583573334185885681 277126937680000639414261)
            ·
              refine ⟨25980650407500059945087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277126937680000639414261 25980650407500059945087)
              ·
                rfl

theorem cell19_256148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_256148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256148 prefixEnd_256148 := by exact prefixLift 256148
  have htrace : WordTrace (prefixWord ++ tailWord_256148) baseStart_256148 baseEnd_256148 := by
    simpa [prefixWord, tailWord_256148, baseEnd_256148] using wordTrace_append hprefix tailTrace_256148
  have hstable : (prefixWord ++ tailWord_256148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256148).length < 2 ^ (prefixWord ++ tailWord_256148).sum := by decide
  have hdescent : baseEnd_256148 < baseStart_256148 := by decide
  rcases family_descends (prefixWord ++ tailWord_256148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256268 : List Nat := [2, 2, 1, 2, 2, 2, 8]
def baseStart_256268 : Nat := 118140960795 + 256268 * 2 ^ 59
def prefixEnd_256268 : Nat := 4983230072969 + 3 ^ 40 * 256268 * 2
def baseEnd_256268 : Nat := 25992821800791819056089

theorem tailTrace_256268 : CollatzResearch.WordTrace tailWord_256268 prefixEnd_256268 25992821800791819056089 := by
  unfold tailWord_256268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673430917796138967516729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6231241223728185290022305 4673430917796138967516729)
  ·
    refine ⟨3505073188347104225637547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4673430917796138967516729 3505073188347104225637547)
    ·
      refine ⟨5257609782520656338456321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505073188347104225637547 5257609782520656338456321)
      ·
        refine ⟨3943207336890492253842241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5257609782520656338456321 3943207336890492253842241)
        ·
          refine ⟨2957405502667869190381681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943207336890492253842241 2957405502667869190381681)
          ·
            refine ⟨2218054127000901892786261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2957405502667869190381681 2218054127000901892786261)
            ·
              refine ⟨25992821800791819056089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2218054127000901892786261 25992821800791819056089)
              ·
                rfl

theorem cell19_256268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_256268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256268 prefixEnd_256268 := by exact prefixLift 256268
  have htrace : WordTrace (prefixWord ++ tailWord_256268) baseStart_256268 baseEnd_256268 := by
    simpa [prefixWord, tailWord_256268, baseEnd_256268] using wordTrace_append hprefix tailTrace_256268
  have hstable : (prefixWord ++ tailWord_256268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256268).length < 2 ^ (prefixWord ++ tailWord_256268).sum := by decide
  have hdescent : baseEnd_256268 < baseStart_256268 := by decide
  rcases family_descends (prefixWord ++ tailWord_256268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256298 : List Nat := [3, 1, 4, 2, 3, 1, 2, 3]
def baseStart_256298 : Nat := 118140960795 + 256298 * 2 ^ 59
def prefixEnd_256298 : Nat := 4983230072969 + 3 ^ 40 * 256298 * 2
def baseEnd_256298 : Nat := 77987593947344276501519

theorem tailTrace_256298 : CollatzResearch.WordTrace tailWord_256298 prefixEnd_256298 77987593947344276501519 := by
  unfold tailWord_256298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336989006370898264656387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6231970683655728705750365 2336989006370898264656387)
  ·
    refine ⟨3505483509556347396984581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2336989006370898264656387 3505483509556347396984581)
    ·
      refine ⟨657278158041815136934609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3505483509556347396984581 657278158041815136934609)
      ·
        refine ⟨492958618531361352700957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657278158041815136934609 492958618531361352700957)
        ·
          refine ⟨184859481949260507262859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492958618531361352700957 184859481949260507262859)
          ·
            refine ⟨277289222923890760894289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184859481949260507262859 277289222923890760894289)
            ·
              refine ⟨207966917192918070670717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277289222923890760894289 207966917192918070670717)
              ·
                refine ⟨77987593947344276501519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207966917192918070670717 77987593947344276501519)
                ·
                  rfl

theorem cell19_256298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_256298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256298 prefixEnd_256298 := by exact prefixLift 256298
  have htrace : WordTrace (prefixWord ++ tailWord_256298) baseStart_256298 baseEnd_256298 := by
    simpa [prefixWord, tailWord_256298, baseEnd_256298] using wordTrace_append hprefix tailTrace_256298
  have hstable : (prefixWord ++ tailWord_256298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256298).length < 2 ^ (prefixWord ++ tailWord_256298).sum := by decide
  have hdescent : baseEnd_256298 < baseStart_256298 := by decide
  rcases family_descends (prefixWord ++ tailWord_256298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256321 : List Nat := [1, 2, 5, 2, 2, 2, 5]
def baseStart_256321 : Nat := 118140960795 + 256321 * 2 ^ 59
def prefixEnd_256321 : Nat := 4983230072969 + 3 ^ 40 * 256321 * 2
def baseEnd_256321 : Nat := 25998197499495679330115

theorem tailTrace_256321 : CollatzResearch.WordTrace tailWord_256321 prefixEnd_256321 25998197499495679330115 := by
  unfold tailWord_256321
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348794904400267986712817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6232529936266845324475211 9348794904400267986712817)
  ·
    refine ⟨7011596178300200990034613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9348794904400267986712817 7011596178300200990034613)
    ·
      refine ⟨657337141715643842815745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7011596178300200990034613 657337141715643842815745)
      ·
        refine ⟨493002856286732882111809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657337141715643842815745 493002856286732882111809)
        ·
          refine ⟨369752142215049661583857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493002856286732882111809 369752142215049661583857)
          ·
            refine ⟨277314106661287246187893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369752142215049661583857 277314106661287246187893)
            ·
              refine ⟨25998197499495679330115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277314106661287246187893 25998197499495679330115)
              ·
                rfl

theorem cell19_256321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_256321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256321 prefixEnd_256321 := by exact prefixLift 256321
  have htrace : WordTrace (prefixWord ++ tailWord_256321) baseStart_256321 baseEnd_256321 := by
    simpa [prefixWord, tailWord_256321, baseEnd_256321] using wordTrace_append hprefix tailTrace_256321
  have hstable : (prefixWord ++ tailWord_256321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256321).length < 2 ^ (prefixWord ++ tailWord_256321).sum := by decide
  have hdescent : baseEnd_256321 < baseStart_256321 := by decide
  rcases family_descends (prefixWord ++ tailWord_256321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256414 : List Nat := [4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_256414 : Nat := 118140960795 + 256414 * 2 ^ 59
def prefixEnd_256414 : Nat := 4983230072969 + 3 ^ 40 * 256414 * 2
def baseEnd_256414 : Nat := 78022890987890377923425

theorem tailTrace_256414 : CollatzResearch.WordTrace tailWord_256414 prefixEnd_256414 78022890987890377923425 := by
  unfold tailWord_256414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169023361632918108731037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6234791262042229913232197 1169023361632918108731037)
  ·
    refine ⟨438383760612344290774139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1169023361632918108731037 438383760612344290774139)
    ·
      refine ⟨657575640918516436161209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438383760612344290774139 657575640918516436161209)
      ·
        refine ⟨493181730688887327120907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657575640918516436161209 493181730688887327120907)
        ·
          refine ⟨739772596033330990681361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493181730688887327120907 739772596033330990681361)
          ·
            refine ⟨554829447024998243011021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739772596033330990681361 554829447024998243011021)
            ·
              refine ⟨208061042634374341129133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554829447024998243011021 208061042634374341129133)
              ·
                refine ⟨78022890987890377923425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208061042634374341129133 78022890987890377923425)
                ·
                  rfl

theorem cell19_256414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_256414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256414 prefixEnd_256414 := by exact prefixLift 256414
  have htrace : WordTrace (prefixWord ++ tailWord_256414) baseStart_256414 baseEnd_256414 := by
    simpa [prefixWord, tailWord_256414, baseEnd_256414] using wordTrace_append hprefix tailTrace_256414
  have hstable : (prefixWord ++ tailWord_256414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256414).length < 2 ^ (prefixWord ++ tailWord_256414).sum := by decide
  have hdescent : baseEnd_256414 < baseStart_256414 := by decide
  rcases family_descends (prefixWord ++ tailWord_256414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256420 : List Nat := [2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_256420 : Nat := 118140960795 + 256420 * 2 ^ 59
def prefixEnd_256420 : Nat := 4983230072969 + 3 ^ 40 * 256420 * 2
def baseEnd_256420 : Nat := 78024716696884141790075

theorem tailTrace_256420 : CollatzResearch.WordTrace tailWord_256420 prefixEnd_256420 78024716696884141790075 := by
  unfold tailWord_256420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676202865520803947283357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6234937154027738596377809 4676202865520803947283357)
  ·
    refine ⟨1753576074570301480231259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4676202865520803947283357 1753576074570301480231259)
    ·
      refine ⟨2630364111855452220346889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753576074570301480231259 2630364111855452220346889)
      ·
        refine ⟨1972773083891589165260167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630364111855452220346889 1972773083891589165260167)
        ·
          refine ⟨2959159625837383747890251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1972773083891589165260167 2959159625837383747890251)
          ·
            refine ⟨4438739438756075621835377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959159625837383747890251 4438739438756075621835377)
            ·
              refine ⟨3329054579067056716376533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438739438756075621835377 3329054579067056716376533)
              ·
                refine ⟨78024716696884141790075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3329054579067056716376533 78024716696884141790075)
                ·
                  rfl

theorem cell19_256420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_256420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256420 prefixEnd_256420 := by exact prefixLift 256420
  have htrace : WordTrace (prefixWord ++ tailWord_256420) baseStart_256420 baseEnd_256420 := by
    simpa [prefixWord, tailWord_256420, baseEnd_256420] using wordTrace_append hprefix tailTrace_256420
  have hstable : (prefixWord ++ tailWord_256420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256420).length < 2 ^ (prefixWord ++ tailWord_256420).sum := by decide
  have hdescent : baseEnd_256420 < baseStart_256420 := by decide
  rcases family_descends (prefixWord ++ tailWord_256420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256437 : List Nat := [1, 3, 3, 2, 3, 1, 6]
def baseStart_256437 : Nat := 118140960795 + 256437 * 2 ^ 59
def prefixEnd_256437 : Nat := 4983230072969 + 3 ^ 40 * 256437 * 2
def baseEnd_256437 : Nat := 26009963179677713137417

theorem tailTrace_256437 : CollatzResearch.WordTrace tailWord_256437 prefixEnd_256437 26009963179677713137417 := by
  unfold tailWord_256437
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353025771980019797935565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6235350514653346531957043 9353025771980019797935565)
  ·
    refine ⟨3507384664492507424225837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9353025771980019797935565 3507384664492507424225837)
    ·
      refine ⟨1315269249184690284084689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3507384664492507424225837 1315269249184690284084689)
      ·
        refine ⟨986451936888517713063517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1315269249184690284084689 986451936888517713063517)
        ·
          refine ⟨369919476333194142398819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 986451936888517713063517 369919476333194142398819)
          ·
            refine ⟨554879214499791213598229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369919476333194142398819 554879214499791213598229)
            ·
              refine ⟨26009963179677713137417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554879214499791213598229 26009963179677713137417)
              ·
                rfl

theorem cell19_256437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_256437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256437 prefixEnd_256437 := by exact prefixLift 256437
  have htrace : WordTrace (prefixWord ++ tailWord_256437) baseStart_256437 baseEnd_256437 := by
    simpa [prefixWord, tailWord_256437, baseEnd_256437] using wordTrace_append hprefix tailTrace_256437
  have hstable : (prefixWord ++ tailWord_256437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256437).length < 2 ^ (prefixWord ++ tailWord_256437).sum := by decide
  have hdescent : baseEnd_256437 < baseStart_256437 := by decide
  rcases family_descends (prefixWord ++ tailWord_256437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256439 : List Nat := [1, 1, 3, 1, 3, 4, 6]
def baseStart_256439 : Nat := 118140960795 + 256439 * 2 ^ 59
def prefixEnd_256439 : Nat := 4983230072969 + 3 ^ 40 * 256439 * 2
def baseEnd_256439 : Nat := 26010166036232575789267

theorem tailTrace_256439 : CollatzResearch.WordTrace tailWord_256439 prefixEnd_256439 26010166036232575789267 := by
  unfold tailWord_256439
  simp only [CollatzResearch.WordTrace]
  refine ⟨9353098717972774139508371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6235399145315182759672247 9353098717972774139508371)
  ·
    refine ⟨14029648076959161209262557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9353098717972774139508371 14029648076959161209262557)
    ·
      refine ⟨5261118028859685453473459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14029648076959161209262557 5261118028859685453473459)
      ·
        refine ⟨7891677043289528180210189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261118028859685453473459 7891677043289528180210189)
        ·
          refine ⟨2959378891233573067578821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7891677043289528180210189 2959378891233573067578821)
          ·
            refine ⟨554883542106294950171029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2959378891233573067578821 554883542106294950171029)
            ·
              refine ⟨26010166036232575789267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 554883542106294950171029 26010166036232575789267)
              ·
                rfl

theorem cell19_256439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_256439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256439 prefixEnd_256439 := by exact prefixLift 256439
  have htrace : WordTrace (prefixWord ++ tailWord_256439) baseStart_256439 baseEnd_256439 := by
    simpa [prefixWord, tailWord_256439, baseEnd_256439] using wordTrace_append hprefix tailTrace_256439
  have hstable : (prefixWord ++ tailWord_256439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256439).length < 2 ^ (prefixWord ++ tailWord_256439).sum := by decide
  have hdescent : baseEnd_256439 < baseStart_256439 := by decide
  rcases family_descends (prefixWord ++ tailWord_256439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256458 : List Nat := [3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_256458 : Nat := 118140960795 + 256458 * 2 ^ 59
def prefixEnd_256458 : Nat := 4983230072969 + 3 ^ 40 * 256458 * 2
def baseEnd_256458 : Nat := 78036279520511312945527

theorem tailTrace_256458 : CollatzResearch.WordTrace tailWord_256458 prefixEnd_256458 78036279520511312945527 := by
  unfold tailWord_256458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338447926225985096112507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6235861136602626922966685 2338447926225985096112507)
  ·
    refine ⟨3507671889338977644168761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338447926225985096112507 3507671889338977644168761)
    ·
      refine ⟨2630753917004233233126571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507671889338977644168761 2630753917004233233126571)
      ·
        refine ⟨3946130875506349849689857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630753917004233233126571 3946130875506349849689857)
        ·
          refine ⟨2959598156629762387267393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946130875506349849689857 2959598156629762387267393)
          ·
            refine ⟨2219698617472321790450545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2959598156629762387267393 2219698617472321790450545)
            ·
              refine ⟨1664773963104241342837909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219698617472321790450545 1664773963104241342837909)
              ·
                refine ⟨78036279520511312945527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1664773963104241342837909 78036279520511312945527)
                ·
                  rfl

theorem cell19_256458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_256458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256458 prefixEnd_256458 := by exact prefixLift 256458
  have htrace : WordTrace (prefixWord ++ tailWord_256458) baseStart_256458 baseEnd_256458 := by
    simpa [prefixWord, tailWord_256458, baseEnd_256458] using wordTrace_append hprefix tailTrace_256458
  have hstable : (prefixWord ++ tailWord_256458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256458).length < 2 ^ (prefixWord ++ tailWord_256458).sum := by decide
  have hdescent : baseEnd_256458 < baseStart_256458 := by decide
  rcases family_descends (prefixWord ++ tailWord_256458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256494 : List Nat := [4, 1, 2, 1, 2, 4, 5]
def baseStart_256494 : Nat := 118140960795 + 256494 * 2 ^ 59
def prefixEnd_256494 : Nat := 4983230072969 + 3 ^ 40 * 256494 * 2
def baseEnd_256494 : Nat := 26015744591491298715143

theorem tailTrace_256494 : CollatzResearch.WordTrace tailWord_256494 prefixEnd_256494 26015744591491298715143 := by
  unfold tailWord_256494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169388091596689816595067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6236736488515679021840357 1169388091596689816595067)
  ·
    refine ⟨1754082137395034724892601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1169388091596689816595067 1754082137395034724892601)
    ·
      refine ⟨1315561603046276043669451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1754082137395034724892601 1315561603046276043669451)
      ·
        refine ⟨1973342404569414065504177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315561603046276043669451 1973342404569414065504177)
        ·
          refine ⟨1480006803427060549128133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973342404569414065504177 1480006803427060549128133)
          ·
            refine ⟨277501275642573852961525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1480006803427060549128133 277501275642573852961525)
            ·
              refine ⟨26015744591491298715143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277501275642573852961525 26015744591491298715143)
              ·
                rfl

theorem cell19_256494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_256494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256494 prefixEnd_256494 := by exact prefixLift 256494
  have htrace : WordTrace (prefixWord ++ tailWord_256494) baseStart_256494 baseEnd_256494 := by
    simpa [prefixWord, tailWord_256494, baseEnd_256494] using wordTrace_append hprefix tailTrace_256494
  have hstable : (prefixWord ++ tailWord_256494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256494).length < 2 ^ (prefixWord ++ tailWord_256494).sum := by decide
  have hdescent : baseEnd_256494 < baseStart_256494 := by decide
  rcases family_descends (prefixWord ++ tailWord_256494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256513 : List Nat := [1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_256513 : Nat := 118140960795 + 256513 * 2 ^ 59
def prefixEnd_256513 : Nat := 4983230072969 + 3 ^ 40 * 256513 * 2
def baseEnd_256513 : Nat := 78053015186287481723155

theorem tailTrace_256513 : CollatzResearch.WordTrace tailWord_256513 prefixEnd_256513 78053015186287481723155 := by
  unfold tailWord_256513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355797719704684777702193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6237198479803123185134795 9355797719704684777702193)
  ·
    refine ⟨7016848289778513583276645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9355797719704684777702193 7016848289778513583276645)
    ·
      refine ⟨1315659054333471296864371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7016848289778513583276645 1315659054333471296864371)
      ·
        refine ⟨1973488581500206945296557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315659054333471296864371 1973488581500206945296557)
        ·
          refine ⟨740058218062577604486209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1973488581500206945296557 740058218062577604486209)
          ·
            refine ⟨555043663546933203364657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740058218062577604486209 555043663546933203364657)
            ·
              refine ⟨416282747660199902523493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555043663546933203364657 416282747660199902523493)
              ·
                refine ⟨78053015186287481723155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416282747660199902523493 78053015186287481723155)
                ·
                  rfl

theorem cell19_256513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_256513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256513 prefixEnd_256513 := by exact prefixLift 256513
  have htrace : WordTrace (prefixWord ++ tailWord_256513) baseStart_256513 baseEnd_256513 := by
    simpa [prefixWord, tailWord_256513, baseEnd_256513] using wordTrace_append hprefix tailTrace_256513
  have hstable : (prefixWord ++ tailWord_256513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256513).length < 2 ^ (prefixWord ++ tailWord_256513).sum := by decide
  have hdescent : baseEnd_256513 < baseStart_256513 := by decide
  rcases family_descends (prefixWord ++ tailWord_256513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256515 : List Nat := [1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_256515 : Nat := 118140960795 + 256515 * 2 ^ 59
def prefixEnd_256515 : Nat := 4983230072969 + 3 ^ 40 * 256515 * 2
def baseEnd_256515 : Nat := 78053623755952069678705

theorem tailTrace_256515 : CollatzResearch.WordTrace tailWord_256515 prefixEnd_256515 78053623755952069678705 := by
  unfold tailWord_256515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355870665697439119274999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6237247110464959412849999 9355870665697439119274999)
  ·
    refine ⟨14033805998546158678912499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9355870665697439119274999 14033805998546158678912499)
    ·
      refine ⟨21050708997819238018368749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14033805998546158678912499 21050708997819238018368749)
      ·
        refine ⟨7894015874182214256888281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21050708997819238018368749 7894015874182214256888281)
        ·
          refine ⟨5920511905636660692666211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894015874182214256888281 5920511905636660692666211)
          ·
            refine ⟨8880767858454991038999317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920511905636660692666211 8880767858454991038999317)
            ·
              refine ⟨416285993365077704953093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8880767858454991038999317 416285993365077704953093)
              ·
                refine ⟨78053623755952069678705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416285993365077704953093 78053623755952069678705)
                ·
                  rfl

theorem cell19_256515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_256515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256515 prefixEnd_256515 := by exact prefixLift 256515
  have htrace : WordTrace (prefixWord ++ tailWord_256515) baseStart_256515 baseEnd_256515 := by
    simpa [prefixWord, tailWord_256515, baseEnd_256515] using wordTrace_append hprefix tailTrace_256515
  have hstable : (prefixWord ++ tailWord_256515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256515).length < 2 ^ (prefixWord ++ tailWord_256515).sum := by decide
  have hdescent : baseEnd_256515 < baseStart_256515 := by decide
  rcases family_descends (prefixWord ++ tailWord_256515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256551 : List Nat := [1, 1, 7, 2, 8]
def baseStart_256551 : Nat := 118140960795 + 256551 * 2 ^ 59
def prefixEnd_256551 : Nat := 4983230072969 + 3 ^ 40 * 256551 * 2
def baseEnd_256551 : Nat := 2891280667033876032541

theorem tailTrace_256551 : CollatzResearch.WordTrace tailWord_256551 prefixEnd_256551 2891280667033876032541 := by
  unfold tailWord_256551
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357183693567017267585507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6238122462378011511723671 9357183693567017267585507)
  ·
    refine ⟨14035775540350525901378261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357183693567017267585507 14035775540350525901378261)
    ·
      refine ⟨328963489226965450813553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14035775540350525901378261 328963489226965450813553)
      ·
        refine ⟨246722616920224088110165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328963489226965450813553 246722616920224088110165)
        ·
          refine ⟨2891280667033876032541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 246722616920224088110165 2891280667033876032541)
          ·
            rfl

theorem cell19_256551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_256551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256551 prefixEnd_256551 := by exact prefixLift 256551
  have htrace : WordTrace (prefixWord ++ tailWord_256551) baseStart_256551 baseEnd_256551 := by
    simpa [prefixWord, tailWord_256551, baseEnd_256551] using wordTrace_append hprefix tailTrace_256551
  have hstable : (prefixWord ++ tailWord_256551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256551).length < 2 ^ (prefixWord ++ tailWord_256551).sum := by decide
  have hdescent : baseEnd_256551 < baseStart_256551 := by decide
  rcases family_descends (prefixWord ++ tailWord_256551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256564 : List Nat := [2, 5, 1, 3, 2, 1, 1, 4]
def baseStart_256564 : Nat := 118140960795 + 256564 * 2 ^ 59
def prefixEnd_256564 : Nat := 4983230072969 + 3 ^ 40 * 256564 * 2
def baseEnd_256564 : Nat := 78068533712734474589683

theorem tailTrace_256564 : CollatzResearch.WordTrace tailWord_256564 prefixEnd_256564 78068533712734474589683 := by
  unfold tailWord_256564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678828921259960243904373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6238438561679946991872497 4678828921259960243904373)
  ·
    refine ⟨438640211368121272866035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4678828921259960243904373 438640211368121272866035)
    ·
      refine ⟨657960317052181909299053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438640211368121272866035 657960317052181909299053)
      ·
        refine ⟨246735118894568215987145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657960317052181909299053 246735118894568215987145)
        ·
          refine ⟨185051339170926161990359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246735118894568215987145 185051339170926161990359)
          ·
            refine ⟨277577008756389242985539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185051339170926161990359 277577008756389242985539)
            ·
              refine ⟨416365513134583864478309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277577008756389242985539 416365513134583864478309)
              ·
                refine ⟨78068533712734474589683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416365513134583864478309 78068533712734474589683)
                ·
                  rfl

theorem cell19_256564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_256564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256564 prefixEnd_256564 := by exact prefixLift 256564
  have htrace : WordTrace (prefixWord ++ tailWord_256564) baseStart_256564 baseEnd_256564 := by
    simpa [prefixWord, tailWord_256564, baseEnd_256564] using wordTrace_append hprefix tailTrace_256564
  have hstable : (prefixWord ++ tailWord_256564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256564).length < 2 ^ (prefixWord ++ tailWord_256564).sum := by decide
  have hdescent : baseEnd_256564 < baseStart_256564 := by decide
  rcases family_descends (prefixWord ++ tailWord_256564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256570 : List Nat := [3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_256570 : Nat := 118140960795 + 256570 * 2 ^ 59
def prefixEnd_256570 : Nat := 4983230072969 + 3 ^ 40 * 256570 * 2
def baseEnd_256570 : Nat := 78070359421728238456333

theorem tailTrace_256570 : CollatzResearch.WordTrace tailWord_256570 prefixEnd_256570 78070359421728238456333 := by
  unfold tailWord_256570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339469170124545878131791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6238584453665455675018109 2339469170124545878131791)
  ·
    refine ⟨3509203755186818817197687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2339469170124545878131791 3509203755186818817197687)
    ·
      refine ⟨5263805632780228225796531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509203755186818817197687 5263805632780228225796531)
      ·
        refine ⟨7895708449170342338694797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263805632780228225796531 7895708449170342338694797)
        ·
          refine ⟨2960890668438878377010549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7895708449170342338694797 2960890668438878377010549)
          ·
            refine ⟨277583500166144847844739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2960890668438878377010549 277583500166144847844739)
            ·
              refine ⟨416375250249217271767109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277583500166144847844739 416375250249217271767109)
              ·
                refine ⟨78070359421728238456333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416375250249217271767109 78070359421728238456333)
                ·
                  rfl

theorem cell19_256570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_256570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256570 prefixEnd_256570 := by exact prefixLift 256570
  have htrace : WordTrace (prefixWord ++ tailWord_256570) baseStart_256570 baseEnd_256570 := by
    simpa [prefixWord, tailWord_256570, baseEnd_256570] using wordTrace_append hprefix tailTrace_256570
  have hstable : (prefixWord ++ tailWord_256570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256570).length < 2 ^ (prefixWord ++ tailWord_256570).sum := by decide
  have hdescent : baseEnd_256570 < baseStart_256570 := by decide
  rcases family_descends (prefixWord ++ tailWord_256570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256644 : List Nat := [2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_256644 : Nat := 118140960795 + 256644 * 2 ^ 59
def prefixEnd_256644 : Nat := 4983230072969 + 3 ^ 40 * 256644 * 2
def baseEnd_256644 : Nat := 78092876499317992811687

theorem tailTrace_256644 : CollatzResearch.WordTrace tailWord_256644 prefixEnd_256644 78092876499317992811687 := by
  unfold tailWord_256644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680287841115047075360493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6240383788153396100480657 4680287841115047075360493)
  ·
    refine ⟨1755107940418142653260185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4680287841115047075360493 1755107940418142653260185)
    ·
      refine ⟨1316330955313606989945139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755107940418142653260185 1316330955313606989945139)
      ·
        refine ⟨1974496432970410484917709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316330955313606989945139 1974496432970410484917709)
        ·
          refine ⟨740436162363903931844141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1974496432970410484917709 740436162363903931844141)
          ·
            refine ⟨277663560886463974441553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740436162363903931844141 277663560886463974441553)
            ·
              refine ⟨208247670664847980831165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277663560886463974441553 208247670664847980831165)
              ·
                refine ⟨78092876499317992811687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208247670664847980831165 78092876499317992811687)
                ·
                  rfl

theorem cell19_256644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_256644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256644 prefixEnd_256644 := by exact prefixLift 256644
  have htrace : WordTrace (prefixWord ++ tailWord_256644) baseStart_256644 baseEnd_256644 := by
    simpa [prefixWord, tailWord_256644, baseEnd_256644] using wordTrace_append hprefix tailTrace_256644
  have hstable : (prefixWord ++ tailWord_256644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256644).length < 2 ^ (prefixWord ++ tailWord_256644).sum := by decide
  have hdescent : baseEnd_256644 < baseStart_256644 := by decide
  rcases family_descends (prefixWord ++ tailWord_256644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256722 : List Nat := [3, 2, 2, 2, 4, 6]
def baseStart_256722 : Nat := 118140960795 + 256722 * 2 ^ 59
def prefixEnd_256722 : Nat := 4983230072969 + 3 ^ 40 * 256722 * 2
def baseEnd_256722 : Nat := 8679623412915213675349

theorem tailTrace_256722 : CollatzResearch.WordTrace tailWord_256722 prefixEnd_256722 8679623412915213675349 := by
  unfold tailWord_256722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340855143986878368015105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6242280383965008981373613 2340855143986878368015105)
  ·
    refine ⟨1755641357990158776011329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2340855143986878368015105 1755641357990158776011329)
    ·
      refine ⟨1316731018492619082008497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755641357990158776011329 1316731018492619082008497)
      ·
        refine ⟨987548263869464311506373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316731018492619082008497 987548263869464311506373)
        ·
          refine ⟨185165299475524558407445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 987548263869464311506373 185165299475524558407445)
          ·
            refine ⟨8679623412915213675349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185165299475524558407445 8679623412915213675349)
            ·
              rfl

theorem cell19_256722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_256722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256722 prefixEnd_256722 := by exact prefixLift 256722
  have htrace : WordTrace (prefixWord ++ tailWord_256722) baseStart_256722 baseEnd_256722 := by
    simpa [prefixWord, tailWord_256722, baseEnd_256722] using wordTrace_append hprefix tailTrace_256722
  have hstable : (prefixWord ++ tailWord_256722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256722).length < 2 ^ (prefixWord ++ tailWord_256722).sum := by decide
  have hdescent : baseEnd_256722 < baseStart_256722 := by decide
  rcases family_descends (prefixWord ++ tailWord_256722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256724 : List Nat := [2, 4, 1, 3, 9]
def baseStart_256724 : Nat := 118140960795 + 256724 * 2 ^ 59
def prefixEnd_256724 : Nat := 4983230072969 + 3 ^ 40 * 256724 * 2
def baseEnd_256724 : Nat := 2893230343922278186433

theorem tailTrace_256724 : CollatzResearch.WordTrace tailWord_256724 prefixEnd_256724 2893230343922278186433 := by
  unfold tailWord_256724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681746760970133906816613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6242329014626845209088817 4681746760970133906816613)
  ·
    refine ⟨877827517681900107528115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4681746760970133906816613 877827517681900107528115)
    ·
      refine ⟨1316741276522850161292173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877827517681900107528115 1316741276522850161292173)
      ·
        refine ⟨493777978696068810484565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1316741276522850161292173 493777978696068810484565)
        ·
          refine ⟨2893230343922278186433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 493777978696068810484565 2893230343922278186433)
          ·
            rfl

theorem cell19_256724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_256724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256724 prefixEnd_256724 := by exact prefixLift 256724
  have htrace : WordTrace (prefixWord ++ tailWord_256724) baseStart_256724 baseEnd_256724 := by
    simpa [prefixWord, tailWord_256724, baseEnd_256724] using wordTrace_append hprefix tailTrace_256724
  have hstable : (prefixWord ++ tailWord_256724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256724).length < 2 ^ (prefixWord ++ tailWord_256724).sum := by decide
  have hdescent : baseEnd_256724 < baseStart_256724 := by decide
  rcases family_descends (prefixWord ++ tailWord_256724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256741 : List Nat := [1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_256741 : Nat := 118140960795 + 256741 * 2 ^ 59
def prefixEnd_256741 : Nat := 4983230072969 + 3 ^ 40 * 256741 * 2
def baseEnd_256741 : Nat := 78122392128050508655867

theorem tailTrace_256741 : CollatzResearch.WordTrace tailWord_256741 prefixEnd_256741 78122392128050508655867 := by
  unfold tailWord_256741
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364113562878679717002077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6242742375252453144668051 9364113562878679717002077)
  ·
    refine ⟨3511542586079504893875779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9364113562878679717002077 3511542586079504893875779)
    ·
      refine ⟨5267313879119257340813669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511542586079504893875779 5267313879119257340813669)
      ·
        refine ⟨987621352334860751402563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5267313879119257340813669 987621352334860751402563)
        ·
          refine ⟨1481432028502291127103845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987621352334860751402563 1481432028502291127103845)
          ·
            refine ⟨277768505344179586331971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1481432028502291127103845 277768505344179586331971)
            ·
              refine ⟨416652758016269379497957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277768505344179586331971 416652758016269379497957)
              ·
                refine ⟨78122392128050508655867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416652758016269379497957 78122392128050508655867)
                ·
                  rfl

theorem cell19_256741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_256741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256741 prefixEnd_256741 := by exact prefixLift 256741
  have htrace : WordTrace (prefixWord ++ tailWord_256741) baseStart_256741 baseEnd_256741 := by
    simpa [prefixWord, tailWord_256741, baseEnd_256741] using wordTrace_append hprefix tailTrace_256741
  have hstable : (prefixWord ++ tailWord_256741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256741).length < 2 ^ (prefixWord ++ tailWord_256741).sum := by decide
  have hdescent : baseEnd_256741 < baseStart_256741 := by decide
  rcases family_descends (prefixWord ++ tailWord_256741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256783 : List Nat := [1, 1, 2, 1, 1, 1, 12]
def baseStart_256783 : Nat := 118140960795 + 256783 * 2 ^ 59
def prefixEnd_256783 : Nat := 4983230072969 + 3 ^ 40 * 256783 * 2
def baseEnd_256783 : Nat := 26045057363668951907473

theorem tailTrace_256783 : CollatzResearch.WordTrace tailWord_256783 prefixEnd_256783 26045057363668951907473 := by
  unfold tailWord_256783
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365645428726520890031003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6243763619151013926687335 9365645428726520890031003)
  ·
    refine ⟨14048468143089781335046505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9365645428726520890031003 14048468143089781335046505)
    ·
      refine ⟨10536351107317336001284879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14048468143089781335046505 10536351107317336001284879)
      ·
        refine ⟨15804526660976004001927319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10536351107317336001284879 15804526660976004001927319)
        ·
          refine ⟨23706789991464006002890979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15804526660976004001927319 23706789991464006002890979)
          ·
            refine ⟨35560184987196009004336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23706789991464006002890979 35560184987196009004336469)
            ·
              refine ⟨26045057363668951907473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35560184987196009004336469 26045057363668951907473)
              ·
                rfl

theorem cell19_256783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_256783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256783 prefixEnd_256783 := by exact prefixLift 256783
  have htrace : WordTrace (prefixWord ++ tailWord_256783) baseStart_256783 baseEnd_256783 := by
    simpa [prefixWord, tailWord_256783, baseEnd_256783] using wordTrace_append hprefix tailTrace_256783
  have hstable : (prefixWord ++ tailWord_256783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256783).length < 2 ^ (prefixWord ++ tailWord_256783).sum := by decide
  have hdescent : baseEnd_256783 < baseStart_256783 := by decide
  rcases family_descends (prefixWord ++ tailWord_256783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256819 : List Nat := [1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_256819 : Nat := 118140960795 + 256819 * 2 ^ 59
def prefixEnd_256819 : Nat := 4983230072969 + 3 ^ 40 * 256819 * 2
def baseEnd_256819 : Nat := 78146126344969438922321

theorem tailTrace_256819 : CollatzResearch.WordTrace tailWord_256819 prefixEnd_256819 78146126344969438922321 := by
  unfold tailWord_256819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366958456596099038341511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6244638971064066025561007 9366958456596099038341511)
  ·
    refine ⟨14050437684894148557512267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9366958456596099038341511 14050437684894148557512267)
    ·
      refine ⟨21075656527341222836268401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14050437684894148557512267 21075656527341222836268401)
      ·
        refine ⟨15806742395505917127201301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21075656527341222836268401 15806742395505917127201301)
        ·
          refine ⟨740941049789339865337561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15806742395505917127201301 740941049789339865337561)
          ·
            refine ⟨555705787342004899003171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 740941049789339865337561 555705787342004899003171)
            ·
              refine ⟨833558681013007348504757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555705787342004899003171 833558681013007348504757)
              ·
                refine ⟨78146126344969438922321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 833558681013007348504757 78146126344969438922321)
                ·
                  rfl

theorem cell19_256819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_256819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256819 prefixEnd_256819 := by exact prefixLift 256819
  have htrace : WordTrace (prefixWord ++ tailWord_256819) baseStart_256819 baseEnd_256819 := by
    simpa [prefixWord, tailWord_256819, baseEnd_256819] using wordTrace_append hprefix tailTrace_256819
  have hstable : (prefixWord ++ tailWord_256819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256819).length < 2 ^ (prefixWord ++ tailWord_256819).sum := by decide
  have hdescent : baseEnd_256819 < baseStart_256819 := by decide
  rcases family_descends (prefixWord ++ tailWord_256819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256857 : List Nat := [1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_256857 : Nat := 118140960795 + 256857 * 2 ^ 59
def prefixEnd_256857 : Nat := 4983230072969 + 3 ^ 40 * 256857 * 2
def baseEnd_256857 : Nat := 78157689168596610077773

theorem tailTrace_256857 : CollatzResearch.WordTrace tailWord_256857 prefixEnd_256857 78157689168596610077773 := by
  unfold tailWord_256857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368344430458431528224825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6245562953638954352149883 9368344430458431528224825)
  ·
    refine ⟨7026258322843823646168619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9368344430458431528224825 7026258322843823646168619)
    ·
      refine ⟨10539387484265735469252929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026258322843823646168619 10539387484265735469252929)
      ·
        refine ⟨7904540613199301601939697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539387484265735469252929 7904540613199301601939697)
        ·
          refine ⟨5928405459899476201454773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904540613199301601939697 5928405459899476201454773)
          ·
            refine ⟨555788011865575893886385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5928405459899476201454773 555788011865575893886385)
            ·
              refine ⟨416841008899181920414789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555788011865575893886385 416841008899181920414789)
              ·
                refine ⟨78157689168596610077773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416841008899181920414789 78157689168596610077773)
                ·
                  rfl

theorem cell19_256857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_256857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256857 prefixEnd_256857 := by exact prefixLift 256857
  have htrace : WordTrace (prefixWord ++ tailWord_256857) baseStart_256857 baseEnd_256857 := by
    simpa [prefixWord, tailWord_256857, baseEnd_256857] using wordTrace_append hprefix tailTrace_256857
  have hstable : (prefixWord ++ tailWord_256857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256857).length < 2 ^ (prefixWord ++ tailWord_256857).sum := by decide
  have hdescent : baseEnd_256857 < baseStart_256857 := by decide
  rcases family_descends (prefixWord ++ tailWord_256857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256897 : List Nat := [1, 2, 4, 12]
def baseStart_256897 : Nat := 118140960795 + 256897 * 2 ^ 59
def prefixEnd_256897 : Nat := 4983230072969 + 3 ^ 40 * 256897 * 2
def baseEnd_256897 : Nat := 965060006936893446775

theorem tailTrace_256897 : CollatzResearch.WordTrace tailWord_256897 prefixEnd_256897 965060006936893446775 := by
  unfold tailWord_256897
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369803350313518359680945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6246535566875678906453963 9369803350313518359680945)
  ·
    refine ⟨7027352512735138769760709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9369803350313518359680945 7027352512735138769760709)
    ·
      refine ⟨1317628596137838519330133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7027352512735138769760709 1317628596137838519330133)
      ·
        refine ⟨965060006936893446775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1317628596137838519330133 965060006936893446775)
        ·
          rfl

theorem cell19_256897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 12].length) (baseStart_256897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256897 prefixEnd_256897 := by exact prefixLift 256897
  have htrace : WordTrace (prefixWord ++ tailWord_256897) baseStart_256897 baseEnd_256897 := by
    simpa [prefixWord, tailWord_256897, baseEnd_256897] using wordTrace_append hprefix tailTrace_256897
  have hstable : (prefixWord ++ tailWord_256897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256897).length < 2 ^ (prefixWord ++ tailWord_256897).sum := by decide
  have hdescent : baseEnd_256897 < baseStart_256897 := by decide
  rcases family_descends (prefixWord ++ tailWord_256897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256954 : List Nat := [3, 1, 1, 1, 2, 1, 10]
def baseStart_256954 : Nat := 118140960795 + 256954 * 2 ^ 59
def prefixEnd_256954 : Nat := 4983230072969 + 3 ^ 40 * 256954 * 2
def baseEnd_256954 : Nat := 26062401599109708640651

theorem tailTrace_256954 : CollatzResearch.WordTrace tailWord_256954 prefixEnd_256954 26062401599109708640651 := by
  unfold tailWord_256954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2342970577776754273626479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6247921540738011396337277 2342970577776754273626479)
  ·
    refine ⟨3514455866665131410439719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2342970577776754273626479 3514455866665131410439719)
    ·
      refine ⟨5271683799997697115659579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514455866665131410439719 5271683799997697115659579)
      ·
        refine ⟨7907525699996545673489369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271683799997697115659579 7907525699996545673489369)
        ·
          refine ⟨5930644274997409255117027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907525699996545673489369 5930644274997409255117027)
          ·
            refine ⟨8895966412496113882675541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930644274997409255117027 8895966412496113882675541)
            ·
              refine ⟨26062401599109708640651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8895966412496113882675541 26062401599109708640651)
              ·
                rfl

theorem cell19_256954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_256954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_256954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_256954 prefixEnd_256954 := by exact prefixLift 256954
  have htrace : WordTrace (prefixWord ++ tailWord_256954) baseStart_256954 baseEnd_256954 := by
    simpa [prefixWord, tailWord_256954, baseEnd_256954] using wordTrace_append hprefix tailTrace_256954
  have hstable : (prefixWord ++ tailWord_256954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256954).length < 2 ^ (prefixWord ++ tailWord_256954).sum := by decide
  have hdescent : baseEnd_256954 < baseStart_256954 := by decide
  rcases family_descends (prefixWord ++ tailWord_256954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257009 : List Nat := [1, 2, 2, 2, 4, 3, 5]
def baseStart_257009 : Nat := 118140960795 + 257009 * 2 ^ 59
def prefixEnd_257009 : Nat := 4983230072969 + 3 ^ 40 * 257009 * 2
def baseEnd_257009 : Nat := 26067980154368431566527

theorem tailTrace_257009 : CollatzResearch.WordTrace tailWord_257009 prefixEnd_257009 26067980154368431566527 := by
  unfold tailWord_257009
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373888325907761487758081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6249258883938507658505387 9373888325907761487758081)
  ·
    refine ⟨7030416244430821115818561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9373888325907761487758081 7030416244430821115818561)
    ·
      refine ⟨5272812183323115836863921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7030416244430821115818561 5272812183323115836863921)
      ·
        refine ⟨3954609137492336877647941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272812183323115836863921 3954609137492336877647941)
        ·
          refine ⟨741489213279813164558989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3954609137492336877647941 741489213279813164558989)
          ·
            refine ⟨278058454979929936709621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741489213279813164558989 278058454979929936709621)
            ·
              refine ⟨26067980154368431566527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278058454979929936709621 26067980154368431566527)
              ·
                rfl

theorem cell19_257009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_257009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257009 prefixEnd_257009 := by exact prefixLift 257009
  have htrace : WordTrace (prefixWord ++ tailWord_257009) baseStart_257009 baseEnd_257009 := by
    simpa [prefixWord, tailWord_257009, baseEnd_257009] using wordTrace_append hprefix tailTrace_257009
  have hstable : (prefixWord ++ tailWord_257009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257009).length < 2 ^ (prefixWord ++ tailWord_257009).sum := by decide
  have hdescent : baseEnd_257009 < baseStart_257009 := by decide
  rcases family_descends (prefixWord ++ tailWord_257009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257047 : List Nat := [1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_257047 : Nat := 118140960795 + 257047 * 2 ^ 59
def prefixEnd_257047 : Nat := 4983230072969 + 3 ^ 40 * 257047 * 2
def baseEnd_257047 : Nat := 78215503286732465855033

theorem tailTrace_257047 : CollatzResearch.WordTrace tailWord_257047 prefixEnd_257047 78215503286732465855033 := by
  unfold tailWord_257047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375274299770093977641395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6250182866513395985094263 9375274299770093977641395)
  ·
    refine ⟨14062911449655140966462093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375274299770093977641395 14062911449655140966462093)
    ·
      refine ⟨5273591793620677862423285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14062911449655140966462093 5273591793620677862423285)
      ·
        refine ⟨494399230651938549602183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5273591793620677862423285 494399230651938549602183)
        ·
          refine ⟨741598845977907824403275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494399230651938549602183 741598845977907824403275)
          ·
            refine ⟨1112398268966861736604913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741598845977907824403275 1112398268966861736604913)
            ·
              refine ⟨834298701725146302453685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112398268966861736604913 834298701725146302453685)
              ·
                refine ⟨78215503286732465855033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834298701725146302453685 78215503286732465855033)
                ·
                  rfl

theorem cell19_257047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_257047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257047 prefixEnd_257047 := by exact prefixLift 257047
  have htrace : WordTrace (prefixWord ++ tailWord_257047) baseStart_257047 baseEnd_257047 := by
    simpa [prefixWord, tailWord_257047, baseEnd_257047] using wordTrace_append hprefix tailTrace_257047
  have hstable : (prefixWord ++ tailWord_257047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257047).length < 2 ^ (prefixWord ++ tailWord_257047).sum := by decide
  have hdescent : baseEnd_257047 < baseStart_257047 := by decide
  rcases family_descends (prefixWord ++ tailWord_257047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257049 : List Nat := [1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_257049 : Nat := 118140960795 + 257049 * 2 ^ 59
def prefixEnd_257049 : Nat := 4983230072969 + 3 ^ 40 * 257049 * 2
def baseEnd_257049 : Nat := 78216111856397053810583

theorem tailTrace_257049 : CollatzResearch.WordTrace tailWord_257049 prefixEnd_257049 78216111856397053810583 := by
  unfold tailWord_257049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375347245762848319214201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6250231497175232212809467 9375347245762848319214201)
  ·
    refine ⟨7031510434322136239410651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9375347245762848319214201 7031510434322136239410651)
    ·
      refine ⟨10547265651483204359115977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031510434322136239410651 10547265651483204359115977)
      ·
        refine ⟨7910449238612403269336983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10547265651483204359115977 7910449238612403269336983)
        ·
          refine ⟨11865673857918604904005475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910449238612403269336983 11865673857918604904005475)
          ·
            refine ⟨17798510786877907356008213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865673857918604904005475 17798510786877907356008213)
            ·
              refine ⟨834305193134901907312885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17798510786877907356008213 834305193134901907312885)
              ·
                refine ⟨78216111856397053810583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 834305193134901907312885 78216111856397053810583)
                ·
                  rfl

theorem cell19_257049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_257049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257049 prefixEnd_257049 := by exact prefixLift 257049
  have htrace : WordTrace (prefixWord ++ tailWord_257049) baseStart_257049 baseEnd_257049 := by
    simpa [prefixWord, tailWord_257049, baseEnd_257049] using wordTrace_append hprefix tailTrace_257049
  have hstable : (prefixWord ++ tailWord_257049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257049).length < 2 ^ (prefixWord ++ tailWord_257049).sum := by decide
  have hdescent : baseEnd_257049 < baseStart_257049 := by decide
  rcases family_descends (prefixWord ++ tailWord_257049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257066 : List Nat := [3, 1, 4, 1, 3, 7]
def baseStart_257066 : Nat := 118140960795 + 257066 * 2 ^ 59
def prefixEnd_257066 : Nat := 4983230072969 + 3 ^ 40 * 257066 * 2
def baseEnd_257066 : Nat := 8691253855394005714751

theorem tailTrace_257066 : CollatzResearch.WordTrace tailWord_257066 prefixEnd_257066 8691253855394005714751 := by
  unfold tailWord_257066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343991821675315055645763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6250644857800840148388701 2343991821675315055645763)
  ·
    refine ⟨3515987732512972583468645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343991821675315055645763 3515987732512972583468645)
    ·
      refine ⟨659247699846182359400371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3515987732512972583468645 659247699846182359400371)
      ·
        refine ⟨988871549769273539100557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659247699846182359400371 988871549769273539100557)
        ·
          refine ⟨370826831163477577162709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 988871549769273539100557 370826831163477577162709)
          ·
            refine ⟨8691253855394005714751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 370826831163477577162709 8691253855394005714751)
            ·
              rfl

theorem cell19_257066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_257066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257066 prefixEnd_257066 := by exact prefixLift 257066
  have htrace : WordTrace (prefixWord ++ tailWord_257066) baseStart_257066 baseEnd_257066 := by
    simpa [prefixWord, tailWord_257066, baseEnd_257066] using wordTrace_append hprefix tailTrace_257066
  have hstable : (prefixWord ++ tailWord_257066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257066).length < 2 ^ (prefixWord ++ tailWord_257066).sum := by decide
  have hdescent : baseEnd_257066 < baseStart_257066 := by decide
  rcases family_descends (prefixWord ++ tailWord_257066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257085 : List Nat := [1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_257085 : Nat := 118140960795 + 257085 * 2 ^ 59
def prefixEnd_257085 : Nat := 4983230072969 + 3 ^ 40 * 257085 * 2
def baseEnd_257085 : Nat := 78227066110359637010485

theorem tailTrace_257085 : CollatzResearch.WordTrace tailWord_257085 prefixEnd_257085 78227066110359637010485 := by
  unfold tailWord_257085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9376660273632426467524709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6251106849088284311683139 9376660273632426467524709)
  ·
    refine ⟨1758123801306079962660883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9376660273632426467524709 1758123801306079962660883)
    ·
      refine ⟨2637185701959119943991325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758123801306079962660883 2637185701959119943991325)
      ·
        refine ⟨988944638234669978996747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2637185701959119943991325 988944638234669978996747)
        ·
          refine ⟨1483416957352004968495121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988944638234669978996747 1483416957352004968495121)
          ·
            refine ⟨1112562718014003726371341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483416957352004968495121 1112562718014003726371341)
            ·
              refine ⟨417211019255251397389253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112562718014003726371341 417211019255251397389253)
              ·
                refine ⟨78227066110359637010485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417211019255251397389253 78227066110359637010485)
                ·
                  rfl

theorem cell19_257085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_257085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257085 prefixEnd_257085 := by exact prefixLift 257085
  have htrace : WordTrace (prefixWord ++ tailWord_257085) baseStart_257085 baseEnd_257085 := by
    simpa [prefixWord, tailWord_257085, baseEnd_257085] using wordTrace_append hprefix tailTrace_257085
  have hstable : (prefixWord ++ tailWord_257085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257085).length < 2 ^ (prefixWord ++ tailWord_257085).sum := by decide
  have hdescent : baseEnd_257085 < baseStart_257085 := by decide
  rcases family_descends (prefixWord ++ tailWord_257085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257125 : List Nat := [1, 3, 1, 3, 2, 1, 8]
def baseStart_257125 : Nat := 118140960795 + 257125 * 2 ^ 59
def prefixEnd_257125 : Nat := 4983230072969 + 3 ^ 40 * 257125 * 2
def baseEnd_257125 : Nat := 26079745834550465373829

theorem tailTrace_257125 : CollatzResearch.WordTrace tailWord_257125 prefixEnd_257125 26079745834550465373829 := by
  unfold tailWord_257125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378119193487513298980829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252079462325008865987219 9378119193487513298980829)
  ·
    refine ⟨3516794697557817487117811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9378119193487513298980829 3516794697557817487117811)
    ·
      refine ⟨5275192046336726230676717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516794697557817487117811 5275192046336726230676717)
      ·
        refine ⟨1978197017376272336503769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5275192046336726230676717 1978197017376272336503769)
        ·
          refine ⟨1483647763032204252377827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978197017376272336503769 1483647763032204252377827)
          ·
            refine ⟨2225471644548306378566741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483647763032204252377827 2225471644548306378566741)
            ·
              refine ⟨26079745834550465373829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2225471644548306378566741 26079745834550465373829)
              ·
                rfl

theorem cell19_257125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_257125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257125 prefixEnd_257125 := by exact prefixLift 257125
  have htrace : WordTrace (prefixWord ++ tailWord_257125) baseStart_257125 baseEnd_257125 := by
    simpa [prefixWord, tailWord_257125, baseEnd_257125] using wordTrace_append hprefix tailTrace_257125
  have hstable : (prefixWord ++ tailWord_257125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257125).length < 2 ^ (prefixWord ++ tailWord_257125).sum := by decide
  have hdescent : baseEnd_257125 < baseStart_257125 := by decide
  rcases family_descends (prefixWord ++ tailWord_257125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257142 : List Nat := [5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_257142 : Nat := 118140960795 + 257142 * 2 ^ 59
def prefixEnd_257142 : Nat := 4983230072969 + 3 ^ 40 * 257142 * 2
def baseEnd_257142 : Nat := 78244410345800393743663

theorem tailTrace_257142 : CollatzResearch.WordTrace tailWord_257142 prefixEnd_257142 78244410345800393743663 := by
  unfold tailWord_257142
  simp only [CollatzResearch.WordTrace]
  refine ⟨586171202151620325146855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6252492822950616801566453 586171202151620325146855)
  ·
    refine ⟨879256803227430487720283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586171202151620325146855 879256803227430487720283)
    ·
      refine ⟨1318885204841145731580425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879256803227430487720283 1318885204841145731580425)
      ·
        refine ⟨989163903630859298685319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318885204841145731580425 989163903630859298685319)
        ·
          refine ⟨1483745855446288948027979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989163903630859298685319 1483745855446288948027979)
          ·
            refine ⟨2225618783169433422041969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483745855446288948027979 2225618783169433422041969)
            ·
              refine ⟨1669214087377075066531477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225618783169433422041969 1669214087377075066531477)
              ·
                refine ⟨78244410345800393743663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1669214087377075066531477 78244410345800393743663)
                ·
                  rfl

theorem cell19_257142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_257142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257142 prefixEnd_257142 := by exact prefixLift 257142
  have htrace : WordTrace (prefixWord ++ tailWord_257142) baseStart_257142 baseEnd_257142 := by
    simpa [prefixWord, tailWord_257142, baseEnd_257142] using wordTrace_append hprefix tailTrace_257142
  have hstable : (prefixWord ++ tailWord_257142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257142).length < 2 ^ (prefixWord ++ tailWord_257142).sum := by decide
  have hdescent : baseEnd_257142 < baseStart_257142 := by decide
  rcases family_descends (prefixWord ++ tailWord_257142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257157 : List Nat := [1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_257157 : Nat := 118140960795 + 257157 * 2 ^ 59
def prefixEnd_257157 : Nat := 4983230072969 + 3 ^ 40 * 257157 * 2
def baseEnd_257157 : Nat := 78248974618284803410289

theorem tailTrace_257157 : CollatzResearch.WordTrace tailWord_257157 prefixEnd_257157 78248974618284803410289 := by
  unfold tailWord_257157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379286329371582764145725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252857552914388509430483 9379286329371582764145725)
  ·
    refine ⟨3517232373514343536554647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9379286329371582764145725 3517232373514343536554647)
    ·
      refine ⟨5275848560271515304831971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517232373514343536554647 5275848560271515304831971)
      ·
        refine ⟨7913772840407272957247957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275848560271515304831971 7913772840407272957247957)
        ·
          refine ⟨185479050947045459935499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7913772840407272957247957 185479050947045459935499)
          ·
            refine ⟨278218576420568189903249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185479050947045459935499 278218576420568189903249)
            ·
              refine ⟨208663932315426142427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278218576420568189903249 208663932315426142427437)
              ·
                refine ⟨78248974618284803410289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208663932315426142427437 78248974618284803410289)
                ·
                  rfl

theorem cell19_257157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_257157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257157 prefixEnd_257157 := by exact prefixLift 257157
  have htrace : WordTrace (prefixWord ++ tailWord_257157) baseStart_257157 baseEnd_257157 := by
    simpa [prefixWord, tailWord_257157, baseEnd_257157] using wordTrace_append hprefix tailTrace_257157
  have hstable : (prefixWord ++ tailWord_257157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257157).length < 2 ^ (prefixWord ++ tailWord_257157).sum := by decide
  have hdescent : baseEnd_257157 < baseStart_257157 := by decide
  rcases family_descends (prefixWord ++ tailWord_257157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257161 : List Nat := [1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_257161 : Nat := 118140960795 + 257161 * 2 ^ 59
def prefixEnd_257161 : Nat := 4983230072969 + 3 ^ 40 * 257161 * 2
def baseEnd_257161 : Nat := 78250191757613979321389

theorem tailTrace_257161 : CollatzResearch.WordTrace tailWord_257161 prefixEnd_257161 78250191757613979321389 := by
  unfold tailWord_257161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379432221357091447291337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252954814238060964860891 9379432221357091447291337)
  ·
    refine ⟨7034574166017818585468503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9379432221357091447291337 7034574166017818585468503)
    ·
      refine ⟨10551861249026727878202755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034574166017818585468503 10551861249026727878202755)
      ·
        refine ⟨15827791873540091817304133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551861249026727878202755 15827791873540091817304133)
        ·
          refine ⟨2967710976288767215744525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15827791873540091817304133 2967710976288767215744525)
          ·
            refine ⟨1112891616108287705904197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2967710976288767215744525 1112891616108287705904197)
            ·
              refine ⟨208667178020303944857037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1112891616108287705904197 208667178020303944857037)
              ·
                refine ⟨78250191757613979321389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208667178020303944857037 78250191757613979321389)
                ·
                  rfl

theorem cell19_257161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_257161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257161 prefixEnd_257161 := by exact prefixLift 257161
  have htrace : WordTrace (prefixWord ++ tailWord_257161) baseStart_257161 baseEnd_257161 := by
    simpa [prefixWord, tailWord_257161, baseEnd_257161] using wordTrace_append hprefix tailTrace_257161
  have hstable : (prefixWord ++ tailWord_257161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257161).length < 2 ^ (prefixWord ++ tailWord_257161).sum := by decide
  have hdescent : baseEnd_257161 < baseStart_257161 := by decide
  rcases family_descends (prefixWord ++ tailWord_257161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257180 : List Nat := [2, 2, 3, 2, 1, 4, 5]
def baseStart_257180 : Nat := 118140960795 + 257180 * 2 ^ 59
def prefixEnd_257180 : Nat := 4983230072969 + 3 ^ 40 * 257180 * 2
def baseEnd_257180 : Nat := 26085324389809188299705

theorem tailTrace_257180 : CollatzResearch.WordTrace tailWord_257180 prefixEnd_257180 26085324389809188299705 := by
  unfold tailWord_257180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690062604144128846116497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6253416805525505128155329 4690062604144128846116497)
  ·
    refine ⟨3517546953108096634587373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4690062604144128846116497 3517546953108096634587373)
    ·
      refine ⟨1319080107415536237970265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3517546953108096634587373 1319080107415536237970265)
      ·
        refine ⟨989310080561652178477699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319080107415536237970265 989310080561652178477699)
        ·
          refine ⟨1483965120842478267716549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989310080561652178477699 1483965120842478267716549)
          ·
            refine ⟨278243460157964675196853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1483965120842478267716549 278243460157964675196853)
            ·
              refine ⟨26085324389809188299705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278243460157964675196853 26085324389809188299705)
              ·
                rfl

theorem cell19_257180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_257180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257180 prefixEnd_257180 := by exact prefixLift 257180
  have htrace : WordTrace (prefixWord ++ tailWord_257180) baseStart_257180 baseEnd_257180 := by
    simpa [prefixWord, tailWord_257180, baseEnd_257180] using wordTrace_append hprefix tailTrace_257180
  have hstable : (prefixWord ++ tailWord_257180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257180).length < 2 ^ (prefixWord ++ tailWord_257180).sum := by decide
  have hdescent : baseEnd_257180 < baseStart_257180 := by decide
  rcases family_descends (prefixWord ++ tailWord_257180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257197 : List Nat := [1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_257197 : Nat := 118140960795 + 257197 * 2 ^ 59
def prefixEnd_257197 : Nat := 4983230072969 + 3 ^ 40 * 257197 * 2
def baseEnd_257197 : Nat := 78261146011576562521291

theorem tailTrace_257197 : CollatzResearch.WordTrace tailWord_257197 prefixEnd_257197 78261146011576562521291 := by
  unfold tailWord_257197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380745249226669595601845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6253830166151113063734563 9380745249226669595601845)
  ·
    refine ⟨879444867115000274587673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9380745249226669595601845 879444867115000274587673)
    ·
      refine ⟨659583650336250205940755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 879444867115000274587673 659583650336250205940755)
      ·
        refine ⟨989375475504375308911133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659583650336250205940755 989375475504375308911133)
        ·
          refine ⟨371015803314140740841675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 989375475504375308911133 371015803314140740841675)
          ·
            refine ⟨556523704971211111262513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371015803314140740841675 556523704971211111262513)
            ·
              refine ⟨417392778728408333446885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556523704971211111262513 417392778728408333446885)
              ·
                refine ⟨78261146011576562521291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417392778728408333446885 78261146011576562521291)
                ·
                  rfl

theorem cell19_257197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_257197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257197 prefixEnd_257197 := by exact prefixLift 257197
  have htrace : WordTrace (prefixWord ++ tailWord_257197) baseStart_257197 baseEnd_257197 := by
    simpa [prefixWord, tailWord_257197, baseEnd_257197] using wordTrace_append hprefix tailTrace_257197
  have hstable : (prefixWord ++ tailWord_257197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257197).length < 2 ^ (prefixWord ++ tailWord_257197).sum := by decide
  have hdescent : baseEnd_257197 < baseStart_257197 := by decide
  rcases family_descends (prefixWord ++ tailWord_257197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257330 : List Nat := [3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_257330 : Nat := 118140960795 + 257330 * 2 ^ 59
def prefixEnd_257330 : Nat := 4983230072969 + 3 ^ 40 * 257330 * 2
def baseEnd_257330 : Nat := 78301615894271661565373

theorem tailTrace_257330 : CollatzResearch.WordTrace tailWord_257330 prefixEnd_257330 78301615894271661565373 := by
  unfold tailWord_257330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346399039436208327548361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6257064105163222206795629 2346399039436208327548361)
  ·
    refine ⟨1759799279577156245661271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2346399039436208327548361 1759799279577156245661271)
    ·
      refine ⟨2639698919365734368491907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1759799279577156245661271 2639698919365734368491907)
      ·
        refine ⟨3959548379048601552737861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639698919365734368491907 3959548379048601552737861)
        ·
          refine ⟨742415321071612791138349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3959548379048601552737861 742415321071612791138349)
          ·
            refine ⟨278405745401854796676881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742415321071612791138349 278405745401854796676881)
            ·
              refine ⟨208804309051391097507661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278405745401854796676881 208804309051391097507661)
              ·
                refine ⟨78301615894271661565373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208804309051391097507661 78301615894271661565373)
                ·
                  rfl

theorem cell19_257330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_257330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257330 prefixEnd_257330 := by exact prefixLift 257330
  have htrace : WordTrace (prefixWord ++ tailWord_257330) baseStart_257330 baseEnd_257330 := by
    simpa [prefixWord, tailWord_257330, baseEnd_257330] using wordTrace_append hprefix tailTrace_257330
  have hstable : (prefixWord ++ tailWord_257330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257330).length < 2 ^ (prefixWord ++ tailWord_257330).sum := by decide
  have hdescent : baseEnd_257330 < baseStart_257330 := by decide
  rcases family_descends (prefixWord ++ tailWord_257330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257332 : List Nat := [2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_257332 : Nat := 118140960795 + 257332 * 2 ^ 59
def prefixEnd_257332 : Nat := 4983230072969 + 3 ^ 40 * 257332 * 2
def baseEnd_257332 : Nat := 78302224463936249520923

theorem tailTrace_257332 : CollatzResearch.WordTrace tailWord_257332 prefixEnd_257332 78302224463936249520923 := by
  unfold tailWord_257332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692834551868793825883125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6257112735825058434510833 4692834551868793825883125)
  ·
    refine ⟨439953239237699421176543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4692834551868793825883125 439953239237699421176543)
    ·
      refine ⟨659929858856549131764815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439953239237699421176543 659929858856549131764815)
      ·
        refine ⟨989894788284823697647223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659929858856549131764815 989894788284823697647223)
        ·
          refine ⟨1484842182427235546470835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989894788284823697647223 1484842182427235546470835)
          ·
            refine ⟨2227263273640853319706253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484842182427235546470835 2227263273640853319706253)
            ·
              refine ⟨835223727615319994889845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2227263273640853319706253 835223727615319994889845)
              ·
                refine ⟨78302224463936249520923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 835223727615319994889845 78302224463936249520923)
                ·
                  rfl

theorem cell19_257332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_257332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257332 prefixEnd_257332 := by exact prefixLift 257332
  have htrace : WordTrace (prefixWord ++ tailWord_257332) baseStart_257332 baseEnd_257332 := by
    simpa [prefixWord, tailWord_257332, baseEnd_257332] using wordTrace_append hprefix tailTrace_257332
  have hstable : (prefixWord ++ tailWord_257332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257332).length < 2 ^ (prefixWord ++ tailWord_257332).sum := by decide
  have hdescent : baseEnd_257332 < baseStart_257332 := by decide
  rcases family_descends (prefixWord ++ tailWord_257332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257406 : List Nat := [4, 2, 3, 2, 1, 7]
def baseStart_257406 : Nat := 118140960795 + 257406 * 2 ^ 59
def prefixEnd_257406 : Nat := 4983230072969 + 3 ^ 40 * 257406 * 2
def baseEnd_257406 : Nat := 8702749060169555986253

theorem tailTrace_257406 : CollatzResearch.WordTrace tailWord_257406 prefixEnd_257406 8702749060169555986253 := by
  unfold tailWord_257406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173546013183687286245009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6258912070312998859973381 1173546013183687286245009)
  ·
    refine ⟨880159509887765464683757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1173546013183687286245009 880159509887765464683757)
    ·
      refine ⟨330059816207912049256409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 880159509887765464683757 330059816207912049256409)
      ·
        refine ⟨247544862155934036942307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330059816207912049256409 247544862155934036942307)
        ·
          refine ⟨371317293233901055413461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247544862155934036942307 371317293233901055413461)
          ·
            refine ⟨8702749060169555986253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 371317293233901055413461 8702749060169555986253)
            ·
              rfl

theorem cell19_257406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_257406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257406 prefixEnd_257406 := by exact prefixLift 257406
  have htrace : WordTrace (prefixWord ++ tailWord_257406) baseStart_257406 baseEnd_257406 := by
    simpa [prefixWord, tailWord_257406, baseEnd_257406] using wordTrace_append hprefix tailTrace_257406
  have hstable : (prefixWord ++ tailWord_257406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257406).length < 2 ^ (prefixWord ++ tailWord_257406).sum := by decide
  have hdescent : baseEnd_257406 < baseStart_257406 := by decide
  rcases family_descends (prefixWord ++ tailWord_257406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257429 : List Nat := [1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_257429 : Nat := 118140960795 + 257429 * 2 ^ 59
def prefixEnd_257429 : Nat := 4983230072969 + 3 ^ 40 * 257429 * 2
def baseEnd_257429 : Nat := 78331740092668765365103

theorem tailTrace_257429 : CollatzResearch.WordTrace tailWord_257429 prefixEnd_257429 78331740092668765365103 := by
  unfold tailWord_257429
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389206984386173218047341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6259471322924115478698227 9389206984386173218047341)
  ·
    refine ⟨3520952619144814956767753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9389206984386173218047341 3520952619144814956767753)
    ·
      refine ⟨2640714464358611217575815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3520952619144814956767753 2640714464358611217575815)
      ·
        refine ⟨3961071696537916826363723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640714464358611217575815 3961071696537916826363723)
        ·
          refine ⟨5941607544806875239545585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961071696537916826363723 5941607544806875239545585)
          ·
            refine ⟨4456205658605156429659189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941607544806875239545585 4456205658605156429659189)
            ·
              refine ⟨417769280494233415280549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4456205658605156429659189 417769280494233415280549)
              ·
                refine ⟨78331740092668765365103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417769280494233415280549 78331740092668765365103)
                ·
                  rfl

theorem cell19_257429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_257429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257429 prefixEnd_257429 := by exact prefixLift 257429
  have htrace : WordTrace (prefixWord ++ tailWord_257429) baseStart_257429 baseEnd_257429 := by
    simpa [prefixWord, tailWord_257429, baseEnd_257429] using wordTrace_append hprefix tailTrace_257429
  have hstable : (prefixWord ++ tailWord_257429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257429).length < 2 ^ (prefixWord ++ tailWord_257429).sum := by decide
  have hdescent : baseEnd_257429 < baseStart_257429 := by decide
  rcases family_descends (prefixWord ++ tailWord_257429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257501 : List Nat := [1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_257501 : Nat := 118140960795 + 257501 * 2 ^ 59
def prefixEnd_257501 : Nat := 4983230072969 + 3 ^ 40 * 257501 * 2
def baseEnd_257501 : Nat := 78353648600593931764907

theorem tailTrace_257501 : CollatzResearch.WordTrace tailWord_257501 prefixEnd_257501 78353648600593931764907 := by
  unfold tailWord_257501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391833040125329514668357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6261222026750219676445571 9391833040125329514668357)
  ·
    refine ⟨1760968695023499284000317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9391833040125329514668357 1760968695023499284000317)
    ·
      refine ⟨660363260633812231500119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1760968695023499284000317 660363260633812231500119)
      ·
        refine ⟨990544890950718347250179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660363260633812231500119 990544890950718347250179)
        ·
          refine ⟨1485817336426077520875269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990544890950718347250179 1485817336426077520875269)
          ·
            refine ⟨278590750579889535164113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1485817336426077520875269 278590750579889535164113)
            ·
              refine ⟨208943062934917151373085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278590750579889535164113 208943062934917151373085)
              ·
                refine ⟨78353648600593931764907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208943062934917151373085 78353648600593931764907)
                ·
                  rfl

theorem cell19_257501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_257501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257501 prefixEnd_257501 := by exact prefixLift 257501
  have htrace : WordTrace (prefixWord ++ tailWord_257501) baseStart_257501 baseEnd_257501 := by
    simpa [prefixWord, tailWord_257501, baseEnd_257501] using wordTrace_append hprefix tailTrace_257501
  have hstable : (prefixWord ++ tailWord_257501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257501).length < 2 ^ (prefixWord ++ tailWord_257501).sum := by decide
  have hdescent : baseEnd_257501 < baseStart_257501 := by decide
  rcases family_descends (prefixWord ++ tailWord_257501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257505 : List Nat := [1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_257505 : Nat := 118140960795 + 257505 * 2 ^ 59
def prefixEnd_257505 : Nat := 4983230072969 + 3 ^ 40 * 257505 * 2
def baseEnd_257505 : Nat := 78354865739923107676007

theorem tailTrace_257505 : CollatzResearch.WordTrace tailWord_257505 prefixEnd_257505 78354865739923107676007 := by
  unfold tailWord_257505
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391978932110838197813969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6261319288073892131875979 9391978932110838197813969)
  ·
    refine ⟨7043984199083128648360477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9391978932110838197813969 7043984199083128648360477)
    ·
      refine ⟨2641494074656173243135179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7043984199083128648360477 2641494074656173243135179)
      ·
        refine ⟨3962241111984259864702769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641494074656173243135179 3962241111984259864702769)
        ·
          refine ⟨2971680833988194898527077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962241111984259864702769 2971680833988194898527077)
          ·
            refine ⟨557190156372786543473827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2971680833988194898527077 557190156372786543473827)
            ·
              refine ⟨835785234559179815210741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557190156372786543473827 835785234559179815210741)
              ·
                refine ⟨78354865739923107676007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 835785234559179815210741 78354865739923107676007)
                ·
                  rfl

theorem cell19_257505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_257505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257505 prefixEnd_257505 := by exact prefixLift 257505
  have htrace : WordTrace (prefixWord ++ tailWord_257505) baseStart_257505 baseEnd_257505 := by
    simpa [prefixWord, tailWord_257505, baseEnd_257505] using wordTrace_append hprefix tailTrace_257505
  have hstable : (prefixWord ++ tailWord_257505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257505).length < 2 ^ (prefixWord ++ tailWord_257505).sum := by decide
  have hdescent : baseEnd_257505 < baseStart_257505 := by decide
  rcases family_descends (prefixWord ++ tailWord_257505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257522 : List Nat := [3, 2, 1, 4, 1, 3, 5]
def baseStart_257522 : Nat := 118140960795 + 257522 * 2 ^ 59
def prefixEnd_257522 : Nat := 4983230072969 + 3 ^ 40 * 257522 * 2
def baseEnd_257522 : Nat := 26120012860690701766061

theorem tailTrace_257522 : CollatzResearch.WordTrace tailWord_257522 prefixEnd_257522 26120012860690701766061 := by
  unfold tailWord_257522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348149743262312525295705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6261732648699500067455213 2348149743262312525295705)
  ·
    refine ⟨1761112307446734393971779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2348149743262312525295705 1761112307446734393971779)
    ·
      refine ⟨2641668461170101590957669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761112307446734393971779 2641668461170101590957669)
      ·
        refine ⟨495312836469394048304563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2641668461170101590957669 495312836469394048304563)
        ·
          refine ⟨742969254704091072456845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495312836469394048304563 742969254704091072456845)
          ·
            refine ⟨278613470514034152171317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742969254704091072456845 278613470514034152171317)
            ·
              refine ⟨26120012860690701766061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278613470514034152171317 26120012860690701766061)
              ·
                rfl

theorem cell19_257522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_257522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257522 prefixEnd_257522 := by exact prefixLift 257522
  have htrace : WordTrace (prefixWord ++ tailWord_257522) baseStart_257522 baseEnd_257522 := by
    simpa [prefixWord, tailWord_257522, baseEnd_257522] using wordTrace_append hprefix tailTrace_257522
  have hstable : (prefixWord ++ tailWord_257522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257522).length < 2 ^ (prefixWord ++ tailWord_257522).sum := by decide
  have hdescent : baseEnd_257522 < baseStart_257522 := by decide
  rcases family_descends (prefixWord ++ tailWord_257522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257543 : List Nat := [1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_257543 : Nat := 118140960795 + 257543 * 2 ^ 59
def prefixEnd_257543 : Nat := 4983230072969 + 3 ^ 40 * 257543 * 2
def baseEnd_257543 : Nat := 78366428563550278831459

theorem tailTrace_257543 : CollatzResearch.WordTrace tailWord_257543 prefixEnd_257543 78366428563550278831459 := by
  unfold tailWord_257543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393364905973170687697283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6262243270648780458464855 9393364905973170687697283)
  ·
    refine ⟨14090047358959756031545925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9393364905973170687697283 14090047358959756031545925)
    ·
      refine ⟨2641883879804954255914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14090047358959756031545925 2641883879804954255914861)
      ·
        refine ⟨990706454926857845968073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641883879804954255914861 990706454926857845968073)
        ·
          refine ⟨743029841195143384476055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990706454926857845968073 743029841195143384476055)
          ·
            refine ⟨1114544761792715076714083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743029841195143384476055 1114544761792715076714083)
            ·
              refine ⟨1671817142689072615071125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114544761792715076714083 1671817142689072615071125)
              ·
                refine ⟨78366428563550278831459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1671817142689072615071125 78366428563550278831459)
                ·
                  rfl

theorem cell19_257543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_257543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257543 prefixEnd_257543 := by exact prefixLift 257543
  have htrace : WordTrace (prefixWord ++ tailWord_257543) baseStart_257543 baseEnd_257543 := by
    simpa [prefixWord, tailWord_257543, baseEnd_257543] using wordTrace_append hprefix tailTrace_257543
  have hstable : (prefixWord ++ tailWord_257543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257543).length < 2 ^ (prefixWord ++ tailWord_257543).sum := by decide
  have hdescent : baseEnd_257543 < baseStart_257543 := by decide
  rcases family_descends (prefixWord ++ tailWord_257543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257596 : List Nat := [2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_257596 : Nat := 118140960795 + 257596 * 2 ^ 59
def prefixEnd_257596 : Nat := 4983230072969 + 3 ^ 40 * 257596 * 2
def baseEnd_257596 : Nat := 78382555659661859653537

theorem tailTrace_257596 : CollatzResearch.WordTrace tailWord_257596 prefixEnd_257596 78382555659661859653537 := by
  unfold tailWord_257596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697648987390580369688321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6263531983187440492917761 4697648987390580369688321)
  ·
    refine ⟨3523236740542935277266241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4697648987390580369688321 3523236740542935277266241)
    ·
      refine ⟨2642427555407201457949681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3523236740542935277266241 2642427555407201457949681)
      ·
        refine ⟨1981820666555401093462261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642427555407201457949681 1981820666555401093462261)
        ·
          refine ⟨185795687489568852512087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1981820666555401093462261 185795687489568852512087)
          ·
            refine ⟨278693531234353278768131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185795687489568852512087 278693531234353278768131)
            ·
              refine ⟨418040296851529918152197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278693531234353278768131 418040296851529918152197)
              ·
                refine ⟨78382555659661859653537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418040296851529918152197 78382555659661859653537)
                ·
                  rfl

theorem cell19_257596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_257596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257596 prefixEnd_257596 := by exact prefixLift 257596
  have htrace : WordTrace (prefixWord ++ tailWord_257596) baseStart_257596 baseEnd_257596 := by
    simpa [prefixWord, tailWord_257596, baseEnd_257596] using wordTrace_append hprefix tailTrace_257596
  have hstable : (prefixWord ++ tailWord_257596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257596).length < 2 ^ (prefixWord ++ tailWord_257596).sum := by decide
  have hdescent : baseEnd_257596 < baseStart_257596 := by decide
  rcases family_descends (prefixWord ++ tailWord_257596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257659 : List Nat := [1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_257659 : Nat := 118140960795 + 257659 * 2 ^ 59
def prefixEnd_257659 : Nat := 4983230072969 + 3 ^ 40 * 257659 * 2
def baseEnd_257659 : Nat := 78401725604096380253365

theorem tailTrace_257659 : CollatzResearch.WordTrace tailWord_257659 prefixEnd_257659 78401725604096380253365 := by
  unfold tailWord_257659
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397595773552922498920031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6265063849035281665946687 9397595773552922498920031)
  ·
    refine ⟨14096393660329383748380047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9397595773552922498920031 14096393660329383748380047)
    ·
      refine ⟨21144590490494075622570071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096393660329383748380047 21144590490494075622570071)
      ·
        refine ⟨31716885735741113433855107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21144590490494075622570071 31716885735741113433855107)
        ·
          refine ⟨47575328603611670150782661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31716885735741113433855107 47575328603611670150782661)
          ·
            refine ⟨8920374113177188153271749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47575328603611670150782661 8920374113177188153271749)
            ·
              refine ⟨1672570146220722778738453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8920374113177188153271749 1672570146220722778738453)
              ·
                refine ⟨78401725604096380253365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1672570146220722778738453 78401725604096380253365)
                ·
                  rfl

theorem cell19_257659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_257659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257659 prefixEnd_257659 := by exact prefixLift 257659
  have htrace : WordTrace (prefixWord ++ tailWord_257659) baseStart_257659 baseEnd_257659 := by
    simpa [prefixWord, tailWord_257659, baseEnd_257659] using wordTrace_append hprefix tailTrace_257659
  have hstable : (prefixWord ++ tailWord_257659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257659).length < 2 ^ (prefixWord ++ tailWord_257659).sum := by decide
  have hdescent : baseEnd_257659 < baseStart_257659 := by decide
  rcases family_descends (prefixWord ++ tailWord_257659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257674 : List Nat := [3, 1, 2, 3, 2, 1, 4, 3]
def baseStart_257674 : Nat := 118140960795 + 257674 * 2 ^ 59
def prefixEnd_257674 : Nat := 4983230072969 + 3 ^ 40 * 257674 * 2
def baseEnd_257674 : Nat := 78406289876580789919991

theorem tailTrace_257674 : CollatzResearch.WordTrace tailWord_257674 prefixEnd_257674 78406289876580789919991 := by
  unfold tailWord_257674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349535717124645015179019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6265428578999053373810717 2349535717124645015179019)
  ·
    refine ⟨3524303575686967522768529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349535717124645015179019 3524303575686967522768529)
    ·
      refine ⟨2643227681765225642076397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3524303575686967522768529 2643227681765225642076397)
      ·
        refine ⟨991210380661959615778649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2643227681765225642076397 991210380661959615778649)
        ·
          refine ⟨743407785496469711833987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991210380661959615778649 743407785496469711833987)
          ·
            refine ⟨1115111678244704567750981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743407785496469711833987 1115111678244704567750981)
            ·
              refine ⟨209083439670882106453309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1115111678244704567750981 209083439670882106453309)
              ·
                refine ⟨78406289876580789919991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209083439670882106453309 78406289876580789919991)
                ·
                  rfl

theorem cell19_257674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_257674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257674 prefixEnd_257674 := by exact prefixLift 257674
  have htrace : WordTrace (prefixWord ++ tailWord_257674) baseStart_257674 baseEnd_257674 := by
    simpa [prefixWord, tailWord_257674, baseEnd_257674] using wordTrace_append hprefix tailTrace_257674
  have hstable : (prefixWord ++ tailWord_257674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257674).length < 2 ^ (prefixWord ++ tailWord_257674).sum := by decide
  have hdescent : baseEnd_257674 < baseStart_257674 := by decide
  rcases family_descends (prefixWord ++ tailWord_257674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257710 : List Nat := [4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_257710 : Nat := 118140960795 + 257710 * 2 ^ 59
def prefixEnd_257710 : Nat := 4983230072969 + 3 ^ 40 * 257710 * 2
def baseEnd_257710 : Nat := 78417244130543373119893

theorem tailTrace_257710 : CollatzResearch.WordTrace tailWord_257710 prefixEnd_257710 78417244130543373119893 := by
  unfold tailWord_257710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174931987046019776128323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6266303930912105472684389 1174931987046019776128323)
  ·
    refine ⟨1762397980569029664192485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174931987046019776128323 1762397980569029664192485)
    ·
      refine ⟨330449621356693062036091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1762397980569029664192485 330449621356693062036091)
      ·
        refine ⟨495674432035039593054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330449621356693062036091 495674432035039593054137)
        ·
          refine ⟨371755824026279694790603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495674432035039593054137 371755824026279694790603)
          ·
            refine ⟨557633736039419542185905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371755824026279694790603 557633736039419542185905)
            ·
              refine ⟨418225302029564656639429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557633736039419542185905 418225302029564656639429)
              ·
                refine ⟨78417244130543373119893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418225302029564656639429 78417244130543373119893)
                ·
                  rfl

theorem cell19_257710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_257710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257710 prefixEnd_257710 := by exact prefixLift 257710
  have htrace : WordTrace (prefixWord ++ tailWord_257710) baseStart_257710 baseEnd_257710 := by
    simpa [prefixWord, tailWord_257710, baseEnd_257710] using wordTrace_append hprefix tailTrace_257710
  have hstable : (prefixWord ++ tailWord_257710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257710).length < 2 ^ (prefixWord ++ tailWord_257710).sum := by decide
  have hdescent : baseEnd_257710 < baseStart_257710 := by decide
  rcases family_descends (prefixWord ++ tailWord_257710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257735 : List Nat := [1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_257735 : Nat := 118140960795 + 257735 * 2 ^ 59
def prefixEnd_257735 : Nat := 4983230072969 + 3 ^ 40 * 257735 * 2
def baseEnd_257735 : Nat := 78424851251350722564269

theorem tailTrace_257735 : CollatzResearch.WordTrace tailWord_257735 prefixEnd_257735 78424851251350722564269 := by
  unfold tailWord_257735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400367721277587478686659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6266911814185058319124439 9400367721277587478686659)
  ·
    refine ⟨14100551581916381218029989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400367721277587478686659 14100551581916381218029989)
    ·
      refine ⟨2643853421609321478380623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14100551581916381218029989 2643853421609321478380623)
      ·
        refine ⟨3965780132413982217570935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643853421609321478380623 3965780132413982217570935)
        ·
          refine ⟨5948670198620973326356403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965780132413982217570935 5948670198620973326356403)
          ·
            refine ⟨8923005297931459989534605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948670198620973326356403 8923005297931459989534605)
            ·
              refine ⟨3346126986724297496075477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923005297931459989534605 3346126986724297496075477)
              ·
                refine ⟨78424851251350722564269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3346126986724297496075477 78424851251350722564269)
                ·
                  rfl

theorem cell19_257735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_257735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257735 prefixEnd_257735 := by exact prefixLift 257735
  have htrace : WordTrace (prefixWord ++ tailWord_257735) baseStart_257735 baseEnd_257735 := by
    simpa [prefixWord, tailWord_257735, baseEnd_257735] using wordTrace_append hprefix tailTrace_257735
  have hstable : (prefixWord ++ tailWord_257735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257735).length < 2 ^ (prefixWord ++ tailWord_257735).sum := by decide
  have hdescent : baseEnd_257735 < baseStart_257735 := by decide
  rcases family_descends (prefixWord ++ tailWord_257735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257750 : List Nat := [5, 2, 1, 3, 8]
def baseStart_257750 : Nat := 118140960795 + 257750 * 2 ^ 59
def prefixEnd_257750 : Nat := 4983230072969 + 3 ^ 40 * 257750 * 2
def baseEnd_257750 : Nat := 2904793167549449341885

theorem tailTrace_257750 : CollatzResearch.WordTrace tailWord_257750 prefixEnd_257750 2904793167549449341885 := by
  unfold tailWord_257750
  simp only [CollatzResearch.WordTrace]
  refine ⟨587557176013952815030169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6267276544148830026988469 587557176013952815030169)
  ·
    refine ⟨440667882010464611272627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 587557176013952815030169 440667882010464611272627)
    ·
      refine ⟨661001823015696916908941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440667882010464611272627 661001823015696916908941)
      ·
        refine ⟨247875683630886343840853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661001823015696916908941 247875683630886343840853)
        ·
          refine ⟨2904793167549449341885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 247875683630886343840853 2904793167549449341885)
          ·
            rfl

theorem cell19_257750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_257750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257750 prefixEnd_257750 := by exact prefixLift 257750
  have htrace : WordTrace (prefixWord ++ tailWord_257750) baseStart_257750 baseEnd_257750 := by
    simpa [prefixWord, tailWord_257750, baseEnd_257750] using wordTrace_append hprefix tailTrace_257750
  have hstable : (prefixWord ++ tailWord_257750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257750).length < 2 ^ (prefixWord ++ tailWord_257750).sum := by decide
  have hdescent : baseEnd_257750 < baseStart_257750 := by decide
  rcases family_descends (prefixWord ++ tailWord_257750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257754 : List Nat := [3, 1, 1, 2, 2, 10]
def baseStart_257754 : Nat := 118140960795 + 257754 * 2 ^ 59
def prefixEnd_257754 : Nat := 4983230072969 + 3 ^ 40 * 257754 * 2
def baseEnd_257754 : Nat := 8714514740351589793555

theorem tailTrace_257754 : CollatzResearch.WordTrace tailWord_257754 prefixEnd_257754 8714514740351589793555 := by
  unfold tailWord_257754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350265177052188430907079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6267373805472502482418877 2350265177052188430907079)
  ·
    refine ⟨3525397765578282646360619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2350265177052188430907079 3525397765578282646360619)
    ·
      refine ⟨5288096648367423969540929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525397765578282646360619 5288096648367423969540929)
      ·
        refine ⟨3966072486275567977155697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5288096648367423969540929 3966072486275567977155697)
        ·
          refine ⟨2974554364706675982866773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966072486275567977155697 2974554364706675982866773)
          ·
            refine ⟨8714514740351589793555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2974554364706675982866773 8714514740351589793555)
            ·
              rfl

theorem cell19_257754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_257754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257754 prefixEnd_257754 := by exact prefixLift 257754
  have htrace : WordTrace (prefixWord ++ tailWord_257754) baseStart_257754 baseEnd_257754 := by
    simpa [prefixWord, tailWord_257754, baseEnd_257754] using wordTrace_append hprefix tailTrace_257754
  have hstable : (prefixWord ++ tailWord_257754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257754).length < 2 ^ (prefixWord ++ tailWord_257754).sum := by decide
  have hdescent : baseEnd_257754 < baseStart_257754 := by decide
  rcases family_descends (prefixWord ++ tailWord_257754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257767 : List Nat := [1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_257767 : Nat := 118140960795 + 257767 * 2 ^ 59
def prefixEnd_257767 : Nat := 4983230072969 + 3 ^ 40 * 257767 * 2
def baseEnd_257767 : Nat := 78434588365984129853071

theorem tailTrace_257767 : CollatzResearch.WordTrace tailWord_257767 prefixEnd_257767 78434588365984129853071 := by
  unfold tailWord_257767
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401534857161656943851555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6267689904774437962567703 9401534857161656943851555)
  ·
    refine ⟨14102302285742485415777333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401534857161656943851555 14102302285742485415777333)
    ·
      refine ⟨1322090839288358007729125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14102302285742485415777333 1322090839288358007729125)
      ·
        refine ⟨247892032366567126449211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1322090839288358007729125 247892032366567126449211)
        ·
          refine ⟨371838048549850689673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247892032366567126449211 371838048549850689673817)
          ·
            refine ⟨278878536412388017255363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371838048549850689673817 278878536412388017255363)
            ·
              refine ⟨418317804618582025883045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278878536412388017255363 418317804618582025883045)
              ·
                refine ⟨78434588365984129853071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418317804618582025883045 78434588365984129853071)
                ·
                  rfl

theorem cell19_257767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_257767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257767 prefixEnd_257767 := by exact prefixLift 257767
  have htrace : WordTrace (prefixWord ++ tailWord_257767) baseStart_257767 baseEnd_257767 := by
    simpa [prefixWord, tailWord_257767, baseEnd_257767] using wordTrace_append hprefix tailTrace_257767
  have hstable : (prefixWord ++ tailWord_257767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257767).length < 2 ^ (prefixWord ++ tailWord_257767).sum := by decide
  have hdescent : baseEnd_257767 < baseStart_257767 := by decide
  rcases family_descends (prefixWord ++ tailWord_257767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257843 : List Nat := [1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_257843 : Nat := 118140960795 + 257843 * 2 ^ 59
def prefixEnd_257843 : Nat := 4983230072969 + 3 ^ 40 * 257843 * 2
def baseEnd_257843 : Nat := 78457714013238472163975

theorem tailTrace_257843 : CollatzResearch.WordTrace tailWord_257843 prefixEnd_257843 78457714013238472163975 := by
  unfold tailWord_257843
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404306804886321923618183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6269537869924214615745455 9404306804886321923618183)
  ·
    refine ⟨14106460207329482885427275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9404306804886321923618183 14106460207329482885427275)
    ·
      refine ⟨21159690310994224328140913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14106460207329482885427275 21159690310994224328140913)
      ·
        refine ⟨15869767733245668246105685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21159690310994224328140913 15869767733245668246105685)
        ·
          refine ⟨185973840623972674759051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 15869767733245668246105685 185973840623972674759051)
          ·
            refine ⟨278960760935959012138577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185973840623972674759051 278960760935959012138577)
            ·
              refine ⟨209220570701969259103933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278960760935959012138577 209220570701969259103933)
              ·
                refine ⟨78457714013238472163975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209220570701969259103933 78457714013238472163975)
                ·
                  rfl

theorem cell19_257843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_257843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257843 prefixEnd_257843 := by exact prefixLift 257843
  have htrace : WordTrace (prefixWord ++ tailWord_257843) baseStart_257843 baseEnd_257843 := by
    simpa [prefixWord, tailWord_257843, baseEnd_257843] using wordTrace_append hprefix tailTrace_257843
  have hstable : (prefixWord ++ tailWord_257843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257843).length < 2 ^ (prefixWord ++ tailWord_257843).sum := by decide
  have hdescent : baseEnd_257843 < baseStart_257843 := by decide
  rcases family_descends (prefixWord ++ tailWord_257843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257862 : List Nat := [6, 1, 1, 2, 1, 3, 5]
def baseStart_257862 : Nat := 118140960795 + 257862 * 2 ^ 59
def prefixEnd_257862 : Nat := 4983230072969 + 3 ^ 40 * 257862 * 2
def baseEnd_257862 : Nat := 26154498475017352580567

theorem tailTrace_257862 : CollatzResearch.WordTrace tailWord_257862 prefixEnd_257862 26154498475017352580567 := by
  unfold tailWord_257862
  simp only [CollatzResearch.WordTrace]
  refine ⟨293906243494296505267495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6269999861211658779039893 293906243494296505267495)
  ·
    refine ⟨440859365241444757901243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293906243494296505267495 440859365241444757901243)
    ·
      refine ⟨661289047862167136851865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440859365241444757901243 661289047862167136851865)
      ·
        refine ⟨495966785896625352638899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661289047862167136851865 495966785896625352638899)
        ·
          refine ⟨743950178844938028958349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495966785896625352638899 743950178844938028958349)
          ·
            refine ⟨278981317066851760859381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743950178844938028958349 278981317066851760859381)
            ·
              refine ⟨26154498475017352580567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278981317066851760859381 26154498475017352580567)
              ·
                rfl

theorem cell19_257862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_257862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257862 prefixEnd_257862 := by exact prefixLift 257862
  have htrace : WordTrace (prefixWord ++ tailWord_257862) baseStart_257862 baseEnd_257862 := by
    simpa [prefixWord, tailWord_257862, baseEnd_257862] using wordTrace_append hprefix tailTrace_257862
  have hstable : (prefixWord ++ tailWord_257862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257862).length < 2 ^ (prefixWord ++ tailWord_257862).sum := by decide
  have hdescent : baseEnd_257862 < baseStart_257862 := by decide
  rcases family_descends (prefixWord ++ tailWord_257862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257887 : List Nat := [1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_257887 : Nat := 118140960795 + 257887 * 2 ^ 59
def prefixEnd_257887 : Nat := 4983230072969 + 3 ^ 40 * 257887 * 2
def baseEnd_257887 : Nat := 78471102545859407186077

theorem tailTrace_257887 : CollatzResearch.WordTrace tailWord_257887 prefixEnd_257887 78471102545859407186077 := by
  unfold tailWord_257887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405911616726917438219915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6270607744484611625479943 9405911616726917438219915)
  ·
    refine ⟨14108867425090376157329873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9405911616726917438219915 14108867425090376157329873)
    ·
      refine ⟨10581650568817782117997405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14108867425090376157329873 10581650568817782117997405)
      ·
        refine ⟨3968118963306668294249027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10581650568817782117997405 3968118963306668294249027)
        ·
          refine ⟨5952178444960002441373541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968118963306668294249027 5952178444960002441373541)
          ·
            refine ⟨1116033458430000457757539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5952178444960002441373541 1116033458430000457757539)
            ·
              refine ⟨1674050187645000686636309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116033458430000457757539 1674050187645000686636309)
              ·
                refine ⟨78471102545859407186077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1674050187645000686636309 78471102545859407186077)
                ·
                  rfl

theorem cell19_257887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_257887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257887 prefixEnd_257887 := by exact prefixLift 257887
  have htrace : WordTrace (prefixWord ++ tailWord_257887) baseStart_257887 baseEnd_257887 := by
    simpa [prefixWord, tailWord_257887, baseEnd_257887] using wordTrace_append hprefix tailTrace_257887
  have hstable : (prefixWord ++ tailWord_257887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257887).length < 2 ^ (prefixWord ++ tailWord_257887).sum := by decide
  have hdescent : baseEnd_257887 < baseStart_257887 := by decide
  rcases family_descends (prefixWord ++ tailWord_257887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257921 : List Nat := [1, 2, 4, 4, 2, 6]
def baseStart_257921 : Nat := 118140960795 + 257921 * 2 ^ 59
def prefixEnd_257921 : Nat := 4983230072969 + 3 ^ 40 * 257921 * 2
def baseEnd_257921 : Nat := 8720160914461933603381

theorem tailTrace_257921 : CollatzResearch.WordTrace tailWord_257921 prefixEnd_257921 8720160914461933603381 := by
  unfold tailWord_257921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407151698603741244957617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6271434465735827496638411 9407151698603741244957617)
  ·
    refine ⟨7055363773952805933718213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9407151698603741244957617 7055363773952805933718213)
    ·
      refine ⟨1322880707616151112572165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7055363773952805933718213 1322880707616151112572165)
      ·
        refine ⟨248040132678028333607281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1322880707616151112572165 248040132678028333607281)
        ·
          refine ⟨186030099508521250205461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248040132678028333607281 186030099508521250205461)
          ·
            refine ⟨8720160914461933603381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186030099508521250205461 8720160914461933603381)
            ·
              rfl

theorem cell19_257921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_257921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257921 prefixEnd_257921 := by exact prefixLift 257921
  have htrace : WordTrace (prefixWord ++ tailWord_257921) baseStart_257921 baseEnd_257921 := by
    simpa [prefixWord, tailWord_257921, baseEnd_257921] using wordTrace_append hprefix tailTrace_257921
  have hstable : (prefixWord ++ tailWord_257921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257921).length < 2 ^ (prefixWord ++ tailWord_257921).sum := by decide
  have hdescent : baseEnd_257921 < baseStart_257921 := by decide
  rcases family_descends (prefixWord ++ tailWord_257921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257940 : List Nat := [2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_257940 : Nat := 118140960795 + 257940 * 2 ^ 59
def prefixEnd_257940 : Nat := 4983230072969 + 3 ^ 40 * 257940 * 2
def baseEnd_257940 : Nat := 78487229641970988008155

theorem tailTrace_257940 : CollatzResearch.WordTrace tailWord_257940 prefixEnd_257940 78487229641970988008155 := by
  unfold tailWord_257940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703922342767453744949637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6271896457023271659932849 4703922342767453744949637)
  ·
    refine ⟨881985439268897577178057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4703922342767453744949637 881985439268897577178057)
    ·
      refine ⟨661489079451673182883543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881985439268897577178057 661489079451673182883543)
      ·
        refine ⟨992233619177509774325315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661489079451673182883543 992233619177509774325315)
        ·
          refine ⟨1488350428766264661487973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992233619177509774325315 1488350428766264661487973)
          ·
            refine ⟨279065705393674624028995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1488350428766264661487973 279065705393674624028995)
            ·
              refine ⟨418598558090511936043493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279065705393674624028995 418598558090511936043493)
              ·
                refine ⟨78487229641970988008155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418598558090511936043493 78487229641970988008155)
                ·
                  rfl

theorem cell19_257940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_257940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257940 prefixEnd_257940 := by exact prefixLift 257940
  have htrace : WordTrace (prefixWord ++ tailWord_257940) baseStart_257940 baseEnd_257940 := by
    simpa [prefixWord, tailWord_257940, baseEnd_257940] using wordTrace_append hprefix tailTrace_257940
  have hstable : (prefixWord ++ tailWord_257940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257940).length < 2 ^ (prefixWord ++ tailWord_257940).sum := by decide
  have hdescent : baseEnd_257940 < baseStart_257940 := by decide
  rcases family_descends (prefixWord ++ tailWord_257940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257959 : List Nat := [1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_257959 : Nat := 118140960795 + 257959 * 2 ^ 59
def prefixEnd_257959 : Nat := 4983230072969 + 3 ^ 40 * 257959 * 2
def baseEnd_257959 : Nat := 78493011053784573585881

theorem tailTrace_257959 : CollatzResearch.WordTrace tailWord_257959 prefixEnd_257959 78493011053784573585881 := by
  unfold tailWord_257959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408537672466073734840931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6272358448310715823227287 9408537672466073734840931)
  ·
    refine ⟨14112806508699110602261397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9408537672466073734840931 14112806508699110602261397)
    ·
      refine ⟨661537805095270809481003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14112806508699110602261397 661537805095270809481003)
      ·
        refine ⟨992306707642906214221505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661537805095270809481003 992306707642906214221505)
        ·
          refine ⟨744230030732179660666129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992306707642906214221505 744230030732179660666129)
          ·
            refine ⟨558172523049134745499597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744230030732179660666129 558172523049134745499597)
            ·
              refine ⟨209314696143425529562349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558172523049134745499597 209314696143425529562349)
              ·
                refine ⟨78493011053784573585881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209314696143425529562349 78493011053784573585881)
                ·
                  rfl

theorem cell19_257959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_257959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_257959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_257959 prefixEnd_257959 := by exact prefixLift 257959
  have htrace : WordTrace (prefixWord ++ tailWord_257959) baseStart_257959 baseEnd_257959 := by
    simpa [prefixWord, tailWord_257959, baseEnd_257959] using wordTrace_append hprefix tailTrace_257959
  have hstable : (prefixWord ++ tailWord_257959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257959).length < 2 ^ (prefixWord ++ tailWord_257959).sum := by decide
  have hdescent : baseEnd_257959 < baseStart_257959 := by decide
  rcases family_descends (prefixWord ++ tailWord_257959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258020 : List Nat := [2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_258020 : Nat := 118140960795 + 258020 * 2 ^ 59
def prefixEnd_258020 : Nat := 4983230072969 + 3 ^ 40 * 258020 * 2
def baseEnd_258020 : Nat := 78511572428554506230159

theorem tailTrace_258020 : CollatzResearch.WordTrace tailWord_258020 prefixEnd_258020 78511572428554506230159 := by
  unfold tailWord_258020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705381262622540576405757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6273841683496720768541009 4705381262622540576405757)
  ·
    refine ⟨1764517973483452716152159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4705381262622540576405757 1764517973483452716152159)
    ·
      refine ⟨2646776960225179074228239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764517973483452716152159 2646776960225179074228239)
      ·
        refine ⟨3970165440337768611342359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646776960225179074228239 3970165440337768611342359)
        ·
          refine ⟨5955248160506652917013539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970165440337768611342359 5955248160506652917013539)
          ·
            refine ⟨8932872240759979375520309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5955248160506652917013539 8932872240759979375520309)
            ·
              refine ⟨837456772571248066455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8932872240759979375520309 837456772571248066455029)
              ·
                refine ⟨78511572428554506230159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837456772571248066455029 78511572428554506230159)
                ·
                  rfl

theorem cell19_258020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_258020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258020 prefixEnd_258020 := by exact prefixLift 258020
  have htrace : WordTrace (prefixWord ++ tailWord_258020) baseStart_258020 baseEnd_258020 := by
    simpa [prefixWord, tailWord_258020, baseEnd_258020] using wordTrace_append hprefix tailTrace_258020
  have hstable : (prefixWord ++ tailWord_258020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258020).length < 2 ^ (prefixWord ++ tailWord_258020).sum := by decide
  have hdescent : baseEnd_258020 < baseStart_258020 := by decide
  rcases family_descends (prefixWord ++ tailWord_258020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258113 : List Nat := [1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_258113 : Nat := 118140960795 + 258113 * 2 ^ 59
def prefixEnd_258113 : Nat := 4983230072969 + 3 ^ 40 * 258113 * 2
def baseEnd_258113 : Nat := 78539870917957846163239

theorem tailTrace_258113 : CollatzResearch.WordTrace tailWord_258113 prefixEnd_258113 78539870917957846163239 := by
  unfold tailWord_258113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414154513908158035946993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6276103009272105357297995 9414154513908158035946993)
  ·
    refine ⟨7060615885431118526960245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414154513908158035946993 7060615885431118526960245)
    ·
      refine ⟨661932739259167361902523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7060615885431118526960245 661932739259167361902523)
      ·
        refine ⟨992899108888751042853785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661932739259167361902523 992899108888751042853785)
        ·
          refine ⟨744674331666563282140339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992899108888751042853785 744674331666563282140339)
          ·
            refine ⟨1117011497499844923210509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744674331666563282140339 1117011497499844923210509)
            ·
              refine ⟨418879311562441846203941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1117011497499844923210509 418879311562441846203941)
              ·
                refine ⟨78539870917957846163239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418879311562441846203941 78539870917957846163239)
                ·
                  rfl

theorem cell19_258113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_258113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258113 prefixEnd_258113 := by exact prefixLift 258113
  have htrace : WordTrace (prefixWord ++ tailWord_258113) baseStart_258113 baseEnd_258113 := by
    simpa [prefixWord, tailWord_258113, baseEnd_258113] using wordTrace_append hprefix tailTrace_258113
  have hstable : (prefixWord ++ tailWord_258113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258113).length < 2 ^ (prefixWord ++ tailWord_258113).sum := by decide
  have hdescent : baseEnd_258113 < baseStart_258113 := by decide
  rcases family_descends (prefixWord ++ tailWord_258113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258130 : List Nat := [3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_258130 : Nat := 118140960795 + 258130 * 2 ^ 59
def prefixEnd_258130 : Nat := 4983230072969 + 3 ^ 40 * 258130 * 2
def baseEnd_258130 : Nat := 78545043760106843785415

theorem tailTrace_258130 : CollatzResearch.WordTrace tailWord_258130 prefixEnd_258130 78545043760106843785415 := by
  unfold tailWord_258130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353693638711642484828961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6276516369897713292877229 2353693638711642484828961)
  ·
    refine ⟨1765270229033731863621721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353693638711642484828961 1765270229033731863621721)
    ·
      refine ⟨1323952671775298897716291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765270229033731863621721 1323952671775298897716291)
      ·
        refine ⟨1985929007662948346574437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323952671775298897716291 1985929007662948346574437)
        ·
          refine ⟨372361688936802814982707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1985929007662948346574437 372361688936802814982707)
          ·
            refine ⟨558542533405204222474061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372361688936802814982707 558542533405204222474061)
            ·
              refine ⟨209453450026951583427773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558542533405204222474061 209453450026951583427773)
              ·
                refine ⟨78545043760106843785415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209453450026951583427773 78545043760106843785415)
                ·
                  rfl

theorem cell19_258130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_258130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258130 prefixEnd_258130 := by exact prefixLift 258130
  have htrace : WordTrace (prefixWord ++ tailWord_258130) baseStart_258130 baseEnd_258130 := by
    simpa [prefixWord, tailWord_258130, baseEnd_258130] using wordTrace_append hprefix tailTrace_258130
  have hstable : (prefixWord ++ tailWord_258130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258130).length < 2 ^ (prefixWord ++ tailWord_258130).sum := by decide
  have hdescent : baseEnd_258130 < baseStart_258130 := by decide
  rcases family_descends (prefixWord ++ tailWord_258130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258206 : List Nat := [4, 3, 1, 1, 3, 2, 5]
def baseStart_258206 : Nat := 118140960795 + 258206 * 2 ^ 59
def prefixEnd_258206 : Nat := 4983230072969 + 3 ^ 40 * 258206 * 2
def baseEnd_258206 : Nat := 26189389802453728698773

theorem tailTrace_258206 : CollatzResearch.WordTrace tailWord_258206 prefixEnd_258206 26189389802453728698773 := by
  unfold tailWord_258206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177193312821404364885309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6278364335047489946054981 1177193312821404364885309)
  ·
    refine ⟨441447492308026636831991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1177193312821404364885309 441447492308026636831991)
    ·
      refine ⟨662171238462039955247987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441447492308026636831991 662171238462039955247987)
      ·
        refine ⟨993256857693059932871981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662171238462039955247987 993256857693059932871981)
        ·
          refine ⟨372471321634897474826993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993256857693059932871981 372471321634897474826993)
          ·
            refine ⟨279353491226173106120245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372471321634897474826993 279353491226173106120245)
            ·
              refine ⟨26189389802453728698773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279353491226173106120245 26189389802453728698773)
              ·
                rfl

theorem cell19_258206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_258206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258206 prefixEnd_258206 := by exact prefixLift 258206
  have htrace : WordTrace (prefixWord ++ tailWord_258206) baseStart_258206 baseEnd_258206 := by
    simpa [prefixWord, tailWord_258206, baseEnd_258206] using wordTrace_append hprefix tailTrace_258206
  have hstable : (prefixWord ++ tailWord_258206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258206).length < 2 ^ (prefixWord ++ tailWord_258206).sum := by decide
  have hdescent : baseEnd_258206 < baseStart_258206 := by decide
  rcases family_descends (prefixWord ++ tailWord_258206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258362 : List Nat := [3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_258362 : Nat := 118140960795 + 258362 * 2 ^ 59
def prefixEnd_258362 : Nat := 4983230072969 + 3 ^ 40 * 258362 * 2
def baseEnd_258362 : Nat := 78615637841199046629227

theorem tailTrace_258362 : CollatzResearch.WordTrace tailWord_258362 prefixEnd_258362 78615637841199046629227 := by
  unfold tailWord_258362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355809072501518390440335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6282157526670715707840893 2355809072501518390440335)
  ·
    refine ⟨3533713608752277585660503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2355809072501518390440335 3533713608752277585660503)
    ·
      refine ⟨5300570413128416378490755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533713608752277585660503 5300570413128416378490755)
      ·
        refine ⟨7950855619692624567736133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300570413128416378490755 7950855619692624567736133)
        ·
          refine ⟨1490785428692367106450525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7950855619692624567736133 1490785428692367106450525)
          ·
            refine ⟨559044535759637664918947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1490785428692367106450525 559044535759637664918947)
            ·
              refine ⟨838566803639456497378421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559044535759637664918947 838566803639456497378421)
              ·
                refine ⟨78615637841199046629227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838566803639456497378421 78615637841199046629227)
                ·
                  rfl

theorem cell19_258362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_258362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258362 prefixEnd_258362 := by exact prefixLift 258362
  have htrace : WordTrace (prefixWord ++ tailWord_258362) baseStart_258362 baseEnd_258362 := by
    simpa [prefixWord, tailWord_258362, baseEnd_258362] using wordTrace_append hprefix tailTrace_258362
  have hstable : (prefixWord ++ tailWord_258362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258362).length < 2 ^ (prefixWord ++ tailWord_258362).sum := by decide
  have hdescent : baseEnd_258362 < baseStart_258362 := by decide
  rcases family_descends (prefixWord ++ tailWord_258362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258396 : List Nat := [2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_258396 : Nat := 118140960795 + 258396 * 2 ^ 59
def prefixEnd_258396 : Nat := 4983230072969 + 3 ^ 40 * 258396 * 2
def baseEnd_258396 : Nat := 78625983525497041873579

theorem tailTrace_258396 : CollatzResearch.WordTrace tailWord_258396 prefixEnd_258396 78625983525497041873579 := by
  unfold tailWord_258396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712238185941448684249521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6282984247921931578999361 4712238185941448684249521)
  ·
    refine ⟨3534178639456086513187141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4712238185941448684249521 3534178639456086513187141)
    ·
      refine ⟨662658494898016221222589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3534178639456086513187141 662658494898016221222589)
      ·
        refine ⟨248496935586756082958471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662658494898016221222589 248496935586756082958471)
        ·
          refine ⟨372745403380134124437707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248496935586756082958471 372745403380134124437707)
          ·
            refine ⟨559118105070201186656561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372745403380134124437707 559118105070201186656561)
            ·
              refine ⟨419338578802650889992421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559118105070201186656561 419338578802650889992421)
              ·
                refine ⟨78625983525497041873579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419338578802650889992421 78625983525497041873579)
                ·
                  rfl

theorem cell19_258396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_258396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258396 prefixEnd_258396 := by exact prefixLift 258396
  have htrace : WordTrace (prefixWord ++ tailWord_258396) baseStart_258396 baseEnd_258396 := by
    simpa [prefixWord, tailWord_258396, baseEnd_258396] using wordTrace_append hprefix tailTrace_258396
  have hstable : (prefixWord ++ tailWord_258396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258396).length < 2 ^ (prefixWord ++ tailWord_258396).sum := by decide
  have hdescent : baseEnd_258396 < baseStart_258396 := by decide
  rcases family_descends (prefixWord ++ tailWord_258396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258434 : List Nat := [3, 4, 2, 1, 3, 6]
def baseStart_258434 : Nat := 118140960795 + 258434 * 2 ^ 59
def prefixEnd_258434 : Nat := 4983230072969 + 3 ^ 40 * 258434 * 2
def baseEnd_258434 : Nat := 8737505149902690336559

theorem tailTrace_258434 : CollatzResearch.WordTrace tailWord_258434 prefixEnd_258434 8737505149902690336559 := by
  unfold tailWord_258434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356465586436307464595589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6283908230496819905588237 2356465586436307464595589)
  ·
    refine ⟨441837297456807649611673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2356465586436307464595589 441837297456807649611673)
    ·
      refine ⟨331377973092605737208755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441837297456807649611673 331377973092605737208755)
      ·
        refine ⟨497066959638908605813133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331377973092605737208755 497066959638908605813133)
        ·
          refine ⟨186400109864590727179925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497066959638908605813133 186400109864590727179925)
          ·
            refine ⟨8737505149902690336559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186400109864590727179925 8737505149902690336559)
            ·
              rfl

theorem cell19_258434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_258434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258434 prefixEnd_258434 := by exact prefixLift 258434
  have htrace : WordTrace (prefixWord ++ tailWord_258434) baseStart_258434 baseEnd_258434 := by
    simpa [prefixWord, tailWord_258434, baseEnd_258434] using wordTrace_append hprefix tailTrace_258434
  have hstable : (prefixWord ++ tailWord_258434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258434).length < 2 ^ (prefixWord ++ tailWord_258434).sum := by decide
  have hdescent : baseEnd_258434 < baseStart_258434 := by decide
  rcases family_descends (prefixWord ++ tailWord_258434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258472 : List Nat := [2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_258472 : Nat := 118140960795 + 258472 * 2 ^ 59
def prefixEnd_258472 : Nat := 4983230072969 + 3 ^ 40 * 258472 * 2
def baseEnd_258472 : Nat := 78649109172751384184483

theorem tailTrace_258472 : CollatzResearch.WordTrace tailWord_258472 prefixEnd_258472 78649109172751384184483 := by
  unfold tailWord_258472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713624159803781174132835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6284832213071708232177113 4713624159803781174132835)
  ·
    refine ⟨7070436239705671761199253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713624159803781174132835 7070436239705671761199253)
    ·
      refine ⟨331426698736203363806215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7070436239705671761199253 331426698736203363806215)
      ·
        refine ⟨497140048104305045709323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331426698736203363806215 497140048104305045709323)
        ·
          refine ⟨745710072156457568563985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497140048104305045709323 745710072156457568563985)
          ·
            refine ⟨559282554117343176422989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745710072156457568563985 559282554117343176422989)
            ·
              refine ⟨209730957794003691158621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559282554117343176422989 209730957794003691158621)
              ·
                refine ⟨78649109172751384184483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209730957794003691158621 78649109172751384184483)
                ·
                  rfl

theorem cell19_258472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_258472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258472 prefixEnd_258472 := by exact prefixLift 258472
  have htrace : WordTrace (prefixWord ++ tailWord_258472) baseStart_258472 baseEnd_258472 := by
    simpa [prefixWord, tailWord_258472, baseEnd_258472] using wordTrace_append hprefix tailTrace_258472
  have hstable : (prefixWord ++ tailWord_258472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258472).length < 2 ^ (prefixWord ++ tailWord_258472).sum := by decide
  have hdescent : baseEnd_258472 < baseStart_258472 := by decide
  rcases family_descends (prefixWord ++ tailWord_258472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258571 : List Nat := [1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_258571 : Nat := 118140960795 + 258571 * 2 ^ 59
def prefixEnd_258571 : Nat := 4983230072969 + 3 ^ 40 * 258571 * 2
def baseEnd_258571 : Nat := 78679233371148487984213

theorem tailTrace_258571 : CollatzResearch.WordTrace tailWord_258571 prefixEnd_258571 78679233371148487984213 := by
  unfold tailWord_258571
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430859146248902256119567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6287239430832601504079711 9430859146248902256119567)
  ·
    refine ⟨14146288719373353384179351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9430859146248902256119567 14146288719373353384179351)
    ·
      refine ⟨21219433079060030076269027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14146288719373353384179351 21219433079060030076269027)
      ·
        refine ⟨31829149618590045114403541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21219433079060030076269027 31829149618590045114403541)
        ·
          refine ⟨745995694185704182368833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31829149618590045114403541 745995694185704182368833)
          ·
            refine ⟨559496770639278136776625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745995694185704182368833 559496770639278136776625)
            ·
              refine ⟨419622577979458602582469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559496770639278136776625 419622577979458602582469)
              ·
                refine ⟨78679233371148487984213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419622577979458602582469 78679233371148487984213)
                ·
                  rfl

theorem cell19_258571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_258571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258571 prefixEnd_258571 := by exact prefixLift 258571
  have htrace : WordTrace (prefixWord ++ tailWord_258571) baseStart_258571 baseEnd_258571 := by
    simpa [prefixWord, tailWord_258571, baseEnd_258571] using wordTrace_append hprefix tailTrace_258571
  have hstable : (prefixWord ++ tailWord_258571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258571).length < 2 ^ (prefixWord ++ tailWord_258571).sum := by decide
  have hdescent : baseEnd_258571 < baseStart_258571 := by decide
  rcases family_descends (prefixWord ++ tailWord_258571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258605 : List Nat := [1, 5, 4, 1, 1, 7]
def baseStart_258605 : Nat := 118140960795 + 258605 * 2 ^ 59
def prefixEnd_258605 : Nat := 4983230072969 + 3 ^ 40 * 258605 * 2
def baseEnd_258605 : Nat := 8743286561716275914285

theorem tailTrace_258605 : CollatzResearch.WordTrace tailWord_258605 prefixEnd_258605 8743286561716275914285 := by
  unfold tailWord_258605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432099228125726062857269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6288066152083817375238179 9432099228125726062857269)
  ·
    refine ⟨884259302636786818392869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9432099228125726062857269 884259302636786818392869)
    ·
      refine ⟨165798619244397528448663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 884259302636786818392869 165798619244397528448663)
      ·
        refine ⟨248697928866596292672995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165798619244397528448663 248697928866596292672995)
        ·
          refine ⟨373046893299894439009493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248697928866596292672995 373046893299894439009493)
          ·
            refine ⟨8743286561716275914285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 373046893299894439009493 8743286561716275914285)
            ·
              rfl

theorem cell19_258605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_258605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258605 prefixEnd_258605 := by exact prefixLift 258605
  have htrace : WordTrace (prefixWord ++ tailWord_258605) baseStart_258605 baseEnd_258605 := by
    simpa [prefixWord, tailWord_258605, baseEnd_258605] using wordTrace_append hprefix tailTrace_258605
  have hstable : (prefixWord ++ tailWord_258605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258605).length < 2 ^ (prefixWord ++ tailWord_258605).sum := by decide
  have hdescent : baseEnd_258605 < baseStart_258605 := by decide
  rcases family_descends (prefixWord ++ tailWord_258605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258622 : List Nat := [4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_258622 : Nat := 118140960795 + 258622 * 2 ^ 59
def prefixEnd_258622 : Nat := 4983230072969 + 3 ^ 40 * 258622 * 2
def baseEnd_258622 : Nat := 78694751897595480850741

theorem tailTrace_258622 : CollatzResearch.WordTrace tailWord_258622 prefixEnd_258622 78694751897595480850741 := by
  unfold tailWord_258622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179089908633017245778265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6288479512709425310817413 1179089908633017245778265)
  ·
    refine ⟨884317431474762934333699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1179089908633017245778265 884317431474762934333699)
    ·
      refine ⟨1326476147212144401500549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884317431474762934333699 1326476147212144401500549)
      ·
        refine ⟨248714277602277075281353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1326476147212144401500549 248714277602277075281353)
        ·
          refine ⟨186535708201707806461015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248714277602277075281353 186535708201707806461015)
          ·
            refine ⟨279803562302561709691523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186535708201707806461015 279803562302561709691523)
            ·
              refine ⟨419705343453842564537285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279803562302561709691523 419705343453842564537285)
              ·
                refine ⟨78694751897595480850741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419705343453842564537285 78694751897595480850741)
                ·
                  rfl

theorem cell19_258622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_258622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258622 prefixEnd_258622 := by exact prefixLift 258622
  have htrace : WordTrace (prefixWord ++ tailWord_258622) baseStart_258622 baseEnd_258622 := by
    simpa [prefixWord, tailWord_258622, baseEnd_258622] using wordTrace_append hprefix tailTrace_258622
  have hstable : (prefixWord ++ tailWord_258622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258622).length < 2 ^ (prefixWord ++ tailWord_258622).sum := by decide
  have hdescent : baseEnd_258622 < baseStart_258622 := by decide
  rcases family_descends (prefixWord ++ tailWord_258622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258647 : List Nat := [1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_258647 : Nat := 118140960795 + 258647 * 2 ^ 59
def prefixEnd_258647 : Nat := 4983230072969 + 3 ^ 40 * 258647 * 2
def baseEnd_258647 : Nat := 78702359018402830295117

theorem tailTrace_258647 : CollatzResearch.WordTrace tailWord_258647 prefixEnd_258647 78702359018402830295117 := by
  unfold tailWord_258647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9433631093973567235886195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6289087395982378157257463 9433631093973567235886195)
  ·
    refine ⟨14150446640960350853829293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9433631093973567235886195 14150446640960350853829293)
    ·
      refine ⟨5306417490360131570185985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14150446640960350853829293 5306417490360131570185985)
      ·
        refine ⟨3979813117770098677639489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5306417490360131570185985 3979813117770098677639489)
        ·
          refine ⟨2984859838327574008229617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979813117770098677639489 2984859838327574008229617)
          ·
            refine ⟨2238644878745680506172213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984859838327574008229617 2238644878745680506172213)
            ·
              refine ⟨209872957382407547453645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2238644878745680506172213 209872957382407547453645)
              ·
                refine ⟨78702359018402830295117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209872957382407547453645 78702359018402830295117)
                ·
                  rfl

theorem cell19_258647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_258647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258647 prefixEnd_258647 := by exact prefixLift 258647
  have htrace : WordTrace (prefixWord ++ tailWord_258647) baseStart_258647 baseEnd_258647 := by
    simpa [prefixWord, tailWord_258647, baseEnd_258647] using wordTrace_append hprefix tailTrace_258647
  have hstable : (prefixWord ++ tailWord_258647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258647).length < 2 ^ (prefixWord ++ tailWord_258647).sum := by decide
  have hdescent : baseEnd_258647 < baseStart_258647 := by decide
  rcases family_descends (prefixWord ++ tailWord_258647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258721 : List Nat := [1, 2, 3, 3, 4, 1, 5]
def baseStart_258721 : Nat := 118140960795 + 258721 * 2 ^ 59
def prefixEnd_258721 : Nat := 4983230072969 + 3 ^ 40 * 258721 * 2
def baseEnd_258721 : Nat := 26241625365330861550157

theorem tailTrace_258721 : CollatzResearch.WordTrace tailWord_258721 prefixEnd_258721 26241625365330861550157 := by
  unfold tailWord_258721
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436330095705477874080017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6290886730470318582720011 9436330095705477874080017)
  ·
    refine ⟨7077247571779108405560013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9436330095705477874080017 7077247571779108405560013)
    ·
      refine ⟨2653967839417165652085005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7077247571779108405560013 2653967839417165652085005)
      ·
        refine ⟨995237939781437119531877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2653967839417165652085005 995237939781437119531877)
        ·
          refine ⟨186607113709019459912227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 995237939781437119531877 186607113709019459912227)
          ·
            refine ⟨279910670563529189868341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186607113709019459912227 279910670563529189868341)
            ·
              refine ⟨26241625365330861550157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279910670563529189868341 26241625365330861550157)
              ·
                rfl

theorem cell19_258721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_258721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258721 prefixEnd_258721 := by exact prefixLift 258721
  have htrace : WordTrace (prefixWord ++ tailWord_258721) baseStart_258721 baseEnd_258721 := by
    simpa [prefixWord, tailWord_258721, baseEnd_258721] using wordTrace_append hprefix tailTrace_258721
  have hstable : (prefixWord ++ tailWord_258721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258721).length < 2 ^ (prefixWord ++ tailWord_258721).sum := by decide
  have hdescent : baseEnd_258721 < baseStart_258721 := by decide
  rcases family_descends (prefixWord ++ tailWord_258721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258780 : List Nat := [2, 2, 5, 1, 1, 8]
def baseStart_258780 : Nat := 118140960795 + 258780 * 2 ^ 59
def prefixEnd_258780 : Nat := 4983230072969 + 3 ^ 40 * 258780 * 2
def baseEnd_258780 : Nat := 8749203211233103259911

theorem tailTrace_258780 : CollatzResearch.WordTrace tailWord_258780 prefixEnd_258780 8749203211233103259911 := by
  unfold tailWord_258780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719241001245865475238897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6292321334994487300318529 4719241001245865475238897)
  ·
    refine ⟨3539430750934399106429173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4719241001245865475238897 3539430750934399106429173)
    ·
      refine ⟨331821632900099916227735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3539430750934399106429173 331821632900099916227735)
      ·
        refine ⟨497732449350149874341603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331821632900099916227735 497732449350149874341603)
        ·
          refine ⟨746598674025224811512405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497732449350149874341603 746598674025224811512405)
          ·
            refine ⟨8749203211233103259911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 746598674025224811512405 8749203211233103259911)
            ·
              rfl

theorem cell19_258780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_258780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258780 prefixEnd_258780 := by exact prefixLift 258780
  have htrace : WordTrace (prefixWord ++ tailWord_258780) baseStart_258780 baseEnd_258780 := by
    simpa [prefixWord, tailWord_258780, baseEnd_258780] using wordTrace_append hprefix tailTrace_258780
  have hstable : (prefixWord ++ tailWord_258780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258780).length < 2 ^ (prefixWord ++ tailWord_258780).sum := by decide
  have hdescent : baseEnd_258780 < baseStart_258780 := by decide
  rcases family_descends (prefixWord ++ tailWord_258780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258799 : List Nat := [1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_258799 : Nat := 118140960795 + 258799 * 2 ^ 59
def prefixEnd_258799 : Nat := 4983230072969 + 3 ^ 40 * 258799 * 2
def baseEnd_258799 : Nat := 78748610312911514916925

theorem tailTrace_258799 : CollatzResearch.WordTrace tailWord_258799 prefixEnd_258799 78748610312911514916925 := by
  unfold tailWord_258799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439174989422897195419451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6292783326281931463612967 9439174989422897195419451)
  ·
    refine ⟨14158762484134345793129177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9439174989422897195419451 14158762484134345793129177)
    ·
      refine ⟨10619071863100759344846883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14158762484134345793129177 10619071863100759344846883)
      ·
        refine ⟨15928607794651139017270325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619071863100759344846883 15928607794651139017270325)
        ·
          refine ⟨1493306980748544282869093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15928607794651139017270325 1493306980748544282869093)
          ·
            refine ⟨279995058890352053037955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1493306980748544282869093 279995058890352053037955)
            ·
              refine ⟨419992588335528079556933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279995058890352053037955 419992588335528079556933)
              ·
                refine ⟨78748610312911514916925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419992588335528079556933 78748610312911514916925)
                ·
                  rfl

theorem cell19_258799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_258799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258799 prefixEnd_258799 := by exact prefixLift 258799
  have htrace : WordTrace (prefixWord ++ tailWord_258799) baseStart_258799 baseEnd_258799 := by
    simpa [prefixWord, tailWord_258799, baseEnd_258799] using wordTrace_append hprefix tailTrace_258799
  have hstable : (prefixWord ++ tailWord_258799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258799).length < 2 ^ (prefixWord ++ tailWord_258799).sum := by decide
  have hdescent : baseEnd_258799 < baseStart_258799 := by decide
  rcases family_descends (prefixWord ++ tailWord_258799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258915 : List Nat := [1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_258915 : Nat := 118140960795 + 258915 * 2 ^ 59
def prefixEnd_258915 : Nat := 4983230072969 + 3 ^ 40 * 258915 * 2
def baseEnd_258915 : Nat := 78783907353457616338831

theorem tailTrace_258915 : CollatzResearch.WordTrace tailWord_258915 prefixEnd_258915 78783907353457616338831 := by
  unfold tailWord_258915
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443405857002649006642199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6295603904668432671094799 9443405857002649006642199)
  ·
    refine ⟨14165108785503973509963299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9443405857002649006642199 14165108785503973509963299)
    ·
      refine ⟨21247663178255960264944949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14165108785503973509963299 21247663178255960264944949)
      ·
        refine ⟨1991968422961496274838589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21247663178255960264944949 1991968422961496274838589)
        ·
          refine ⟨746988158610561103064471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1991968422961496274838589 746988158610561103064471)
          ·
            refine ⟨1120482237915841654596707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746988158610561103064471 1120482237915841654596707)
            ·
              refine ⟨1680723356873762481895061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120482237915841654596707 1680723356873762481895061)
              ·
                refine ⟨78783907353457616338831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1680723356873762481895061 78783907353457616338831)
                ·
                  rfl

theorem cell19_258915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_258915 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258915 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258915 prefixEnd_258915 := by exact prefixLift 258915
  have htrace : WordTrace (prefixWord ++ tailWord_258915) baseStart_258915 baseEnd_258915 := by
    simpa [prefixWord, tailWord_258915, baseEnd_258915] using wordTrace_append hprefix tailTrace_258915
  have hstable : (prefixWord ++ tailWord_258915).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258915).length < 2 ^ (prefixWord ++ tailWord_258915).sum := by decide
  have hdescent : baseEnd_258915 < baseStart_258915 := by decide
  rcases family_descends (prefixWord ++ tailWord_258915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258966 : List Nat := [5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_258966 : Nat := 118140960795 + 258966 * 2 ^ 59
def prefixEnd_258966 : Nat := 4983230072969 + 3 ^ 40 * 258966 * 2
def baseEnd_258966 : Nat := 78799425879904609205359

theorem tailTrace_258966 : CollatzResearch.WordTrace tailWord_258966 prefixEnd_258966 78799425879904609205359 := by
  unfold tailWord_258966
  simp only [CollatzResearch.WordTrace]
  refine ⟨590329123738617794796797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6296843986545256477832501 590329123738617794796797)
  ·
    refine ⟨221373421401981673048799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 590329123738617794796797 221373421401981673048799)
    ·
      refine ⟨332060132102972509573199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221373421401981673048799 332060132102972509573199)
      ·
        refine ⟨498090198154458764359799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332060132102972509573199 498090198154458764359799)
        ·
          refine ⟨747135297231688146539699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498090198154458764359799 747135297231688146539699)
          ·
            refine ⟨1120702945847532219809549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747135297231688146539699 1120702945847532219809549)
            ·
              refine ⟨420263604692824582428581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1120702945847532219809549 420263604692824582428581)
              ·
                refine ⟨78799425879904609205359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420263604692824582428581 78799425879904609205359)
                ·
                  rfl

theorem cell19_258966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_258966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_258966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_258966 prefixEnd_258966 := by exact prefixLift 258966
  have htrace : WordTrace (prefixWord ++ tailWord_258966) baseStart_258966 baseEnd_258966 := by
    simpa [prefixWord, tailWord_258966, baseEnd_258966] using wordTrace_append hprefix tailTrace_258966
  have hstable : (prefixWord ++ tailWord_258966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258966).length < 2 ^ (prefixWord ++ tailWord_258966).sum := by decide
  have hdescent : baseEnd_258966 < baseStart_258966 := by decide
  rcases family_descends (prefixWord ++ tailWord_258966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259042 : List Nat := [3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_259042 : Nat := 118140960795 + 259042 * 2 ^ 59
def prefixEnd_259042 : Nat := 4983230072969 + 3 ^ 40 * 259042 * 2
def baseEnd_259042 : Nat := 78822551527158951516263

theorem tailTrace_259042 : CollatzResearch.WordTrace tailWord_259042 prefixEnd_259042 78822551527158951516263 := by
  unfold tailWord_259042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362009481885637424128845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6298691951695033131010253 2362009481885637424128845)
  ·
    refine ⟨885753555707114034048317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2362009481885637424128845 885753555707114034048317)
    ·
      refine ⟨332157583390167762768119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 885753555707114034048317 332157583390167762768119)
      ·
        refine ⟨498236375085251644152179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332157583390167762768119 498236375085251644152179)
        ·
          refine ⟨747354562627877466228269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498236375085251644152179 747354562627877466228269)
          ·
            refine ⟨280257960985454049835601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747354562627877466228269 280257960985454049835601)
            ·
              refine ⟨210193470739090537376701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280257960985454049835601 210193470739090537376701)
              ·
                refine ⟨78822551527158951516263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210193470739090537376701 78822551527158951516263)
                ·
                  rfl

theorem cell19_259042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_259042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259042 prefixEnd_259042 := by exact prefixLift 259042
  have htrace : WordTrace (prefixWord ++ tailWord_259042) baseStart_259042 baseEnd_259042 := by
    simpa [prefixWord, tailWord_259042, baseEnd_259042] using wordTrace_append hprefix tailTrace_259042
  have hstable : (prefixWord ++ tailWord_259042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259042).length < 2 ^ (prefixWord ++ tailWord_259042).sum := by decide
  have hdescent : baseEnd_259042 < baseStart_259042 := by decide
  rcases family_descends (prefixWord ++ tailWord_259042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259061 : List Nat := [1, 3, 5, 2, 2, 1, 5]
def baseStart_259061 : Nat := 118140960795 + 259061 * 2 ^ 59
def prefixEnd_259061 : Nat := 4983230072969 + 3 ^ 40 * 259061 * 2
def baseEnd_259061 : Nat := 26276110979657512364663

theorem tailTrace_259061 : CollatzResearch.WordTrace tailWord_259061 prefixEnd_259061 26276110979657512364663 := by
  unfold tailWord_259061
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448730914473715941457037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6299153942982477294304691 9448730914473715941457037)
  ·
    refine ⟨3543274092927643478046389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9448730914473715941457037 3543274092927643478046389)
    ·
      refine ⟨332181946211966576066849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3543274092927643478046389 332181946211966576066849)
      ·
        refine ⟨249136459658974932050137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332181946211966576066849 249136459658974932050137)
        ·
          refine ⟨186852344744231199037603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249136459658974932050137 186852344744231199037603)
          ·
            refine ⟨280278517116346798556405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186852344744231199037603 280278517116346798556405)
            ·
              refine ⟨26276110979657512364663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280278517116346798556405 26276110979657512364663)
              ·
                rfl

theorem cell19_259061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_259061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259061 prefixEnd_259061 := by exact prefixLift 259061
  have htrace : WordTrace (prefixWord ++ tailWord_259061) baseStart_259061 baseEnd_259061 := by
    simpa [prefixWord, tailWord_259061, baseEnd_259061] using wordTrace_append hprefix tailTrace_259061
  have hstable : (prefixWord ++ tailWord_259061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259061).length < 2 ^ (prefixWord ++ tailWord_259061).sum := by decide
  have hdescent : baseEnd_259061 < baseStart_259061 := by decide
  rcases family_descends (prefixWord ++ tailWord_259061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259086 : List Nat := [4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_259086 : Nat := 118140960795 + 259086 * 2 ^ 59
def prefixEnd_259086 : Nat := 4983230072969 + 3 ^ 40 * 259086 * 2
def baseEnd_259086 : Nat := 78835940059779886538365

theorem tailTrace_259086 : CollatzResearch.WordTrace tailWord_259086 prefixEnd_259086 78835940059779886538365 := by
  unfold tailWord_259086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181205342422893151389639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6299761826255430140744741 1181205342422893151389639)
  ·
    refine ⟨1771808013634339727084459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181205342422893151389639 1771808013634339727084459)
    ·
      refine ⟨2657712020451509590626689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771808013634339727084459 2657712020451509590626689)
      ·
        refine ⟨1993284015338632192970017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2657712020451509590626689 1993284015338632192970017)
        ·
          refine ⟨1494963011503974144727513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993284015338632192970017 1494963011503974144727513)
          ·
            refine ⟨1121222258627980608545635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494963011503974144727513 1121222258627980608545635)
            ·
              refine ⟨1681833387941970912818453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121222258627980608545635 1681833387941970912818453)
              ·
                refine ⟨78835940059779886538365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1681833387941970912818453 78835940059779886538365)
                ·
                  rfl

theorem cell19_259086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_259086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259086 prefixEnd_259086 := by exact prefixLift 259086
  have htrace : WordTrace (prefixWord ++ tailWord_259086) baseStart_259086 baseEnd_259086 := by
    simpa [prefixWord, tailWord_259086, baseEnd_259086] using wordTrace_append hprefix tailTrace_259086
  have hstable : (prefixWord ++ tailWord_259086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259086).length < 2 ^ (prefixWord ++ tailWord_259086).sum := by decide
  have hdescent : baseEnd_259086 < baseStart_259086 := by decide
  rcases family_descends (prefixWord ++ tailWord_259086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259105 : List Nat := [1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_259105 : Nat := 118140960795 + 259105 * 2 ^ 59
def prefixEnd_259105 : Nat := 4983230072969 + 3 ^ 40 * 259105 * 2
def baseEnd_259105 : Nat := 78841721471593472116091

theorem tailTrace_259105 : CollatzResearch.WordTrace tailWord_259105 prefixEnd_259105 78841721471593472116091 := by
  unfold tailWord_259105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450335726314311456058769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6300223817542874304039179 9450335726314311456058769)
  ·
    refine ⟨7087751794735733592044077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9450335726314311456058769 7087751794735733592044077)
    ·
      refine ⟨2657906923025900097016529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7087751794735733592044077 2657906923025900097016529)
      ·
        refine ⟨1993430192269425072762397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2657906923025900097016529 1993430192269425072762397)
        ·
          refine ⟨747536322101034402285899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993430192269425072762397 747536322101034402285899)
          ·
            refine ⟨1121304483151551603428849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747536322101034402285899 1121304483151551603428849)
            ·
              refine ⟨840978362363663702571637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121304483151551603428849 840978362363663702571637)
              ·
                refine ⟨78841721471593472116091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840978362363663702571637 78841721471593472116091)
                ·
                  rfl

theorem cell19_259105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_259105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259105 prefixEnd_259105 := by exact prefixLift 259105
  have htrace : WordTrace (prefixWord ++ tailWord_259105) baseStart_259105 baseEnd_259105 := by
    simpa [prefixWord, tailWord_259105, baseEnd_259105] using wordTrace_append hprefix tailTrace_259105
  have hstable : (prefixWord ++ tailWord_259105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259105).length < 2 ^ (prefixWord ++ tailWord_259105).sum := by decide
  have hdescent : baseEnd_259105 < baseStart_259105 := by decide
  rcases family_descends (prefixWord ++ tailWord_259105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259143 : List Nat := [1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_259143 : Nat := 118140960795 + 259143 * 2 ^ 59
def prefixEnd_259143 : Nat := 4983230072969 + 3 ^ 40 * 259143 * 2
def baseEnd_259143 : Nat := 78853284295220643271543

theorem tailTrace_259143 : CollatzResearch.WordTrace tailWord_259143 prefixEnd_259143 78853284295220643271543 := by
  unfold tailWord_259143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451721700176643945942083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6301147800117762630628055 9451721700176643945942083)
  ·
    refine ⟨14177582550264965918913125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451721700176643945942083 14177582550264965918913125)
    ·
      refine ⟨2658296728174681109796211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14177582550264965918913125 2658296728174681109796211)
      ·
        refine ⟨3987445092262021664694317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658296728174681109796211 3987445092262021664694317)
        ·
          refine ⟨1495291909598258124260369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3987445092262021664694317 1495291909598258124260369)
          ·
            refine ⟨1121468932198693593195277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495291909598258124260369 1121468932198693593195277)
            ·
              refine ⟨420550849574510097448229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121468932198693593195277 420550849574510097448229)
              ·
                refine ⟨78853284295220643271543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420550849574510097448229 78853284295220643271543)
                ·
                  rfl

theorem cell19_259143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_259143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259143 prefixEnd_259143 := by exact prefixLift 259143
  have htrace : WordTrace (prefixWord ++ tailWord_259143) baseStart_259143 baseEnd_259143 := by
    simpa [prefixWord, tailWord_259143, baseEnd_259143] using wordTrace_append hprefix tailTrace_259143
  have hstable : (prefixWord ++ tailWord_259143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259143).length < 2 ^ (prefixWord ++ tailWord_259143).sum := by decide
  have hdescent : baseEnd_259143 < baseStart_259143 := by decide
  rcases family_descends (prefixWord ++ tailWord_259143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259145 : List Nat := [1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_259145 : Nat := 118140960795 + 259145 * 2 ^ 59
def prefixEnd_259145 : Nat := 4983230072969 + 3 ^ 40 * 259145 * 2
def baseEnd_259145 : Nat := 78853892864885231227093

theorem tailTrace_259145 : CollatzResearch.WordTrace tailWord_259145 prefixEnd_259145 78853892864885231227093 := by
  unfold tailWord_259145
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451794646169398287514889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6301196430779598858343259 9451794646169398287514889)
  ·
    refine ⟨7088845984627048715636167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9451794646169398287514889 7088845984627048715636167)
    ·
      refine ⟨10633268976940573073454251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088845984627048715636167 10633268976940573073454251)
      ·
        refine ⟨15949903465410859610181377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633268976940573073454251 15949903465410859610181377)
        ·
          refine ⟨11962427599058144707636033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949903465410859610181377 11962427599058144707636033)
          ·
            refine ⟨8971820699293608530727025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962427599058144707636033 8971820699293608530727025)
            ·
              refine ⟨6728865524470206398045269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971820699293608530727025 6728865524470206398045269)
              ·
                refine ⟨78853892864885231227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6728865524470206398045269 78853892864885231227093)
                ·
                  rfl

theorem cell19_259145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_259145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259145 prefixEnd_259145 := by exact prefixLift 259145
  have htrace : WordTrace (prefixWord ++ tailWord_259145) baseStart_259145 baseEnd_259145 := by
    simpa [prefixWord, tailWord_259145, baseEnd_259145] using wordTrace_append hprefix tailTrace_259145
  have hstable : (prefixWord ++ tailWord_259145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259145).length < 2 ^ (prefixWord ++ tailWord_259145).sum := by decide
  have hdescent : baseEnd_259145 < baseStart_259145 := by decide
  rcases family_descends (prefixWord ++ tailWord_259145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259181 : List Nat := [1, 5, 1, 1, 2, 3, 6]
def baseStart_259181 : Nat := 118140960795 + 259181 * 2 ^ 59
def prefixEnd_259181 : Nat := 4983230072969 + 3 ^ 40 * 259181 * 2
def baseEnd_259181 : Nat := 26288282372949271475665

theorem tailTrace_259181 : CollatzResearch.WordTrace tailWord_259181 prefixEnd_259181 26288282372949271475665 := by
  unfold tailWord_259181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453107674038976435825397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6302071782692650957216931 9453107674038976435825397)
  ·
    refine ⟨886228844441154040858631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9453107674038976435825397 886228844441154040858631)
    ·
      refine ⟨1329343266661731061287947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886228844441154040858631 1329343266661731061287947)
      ·
        refine ⟨1994014899992596591931921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329343266661731061287947 1994014899992596591931921)
        ·
          refine ⟨1495511174994447443948941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994014899992596591931921 1495511174994447443948941)
          ·
            refine ⟨560816690622917791480853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1495511174994447443948941 560816690622917791480853)
            ·
              refine ⟨26288282372949271475665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560816690622917791480853 26288282372949271475665)
              ·
                rfl

theorem cell19_259181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_259181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259181 prefixEnd_259181 := by exact prefixLift 259181
  have htrace : WordTrace (prefixWord ++ tailWord_259181) baseStart_259181 baseEnd_259181 := by
    simpa [prefixWord, tailWord_259181, baseEnd_259181] using wordTrace_append hprefix tailTrace_259181
  have hstable : (prefixWord ++ tailWord_259181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259181).length < 2 ^ (prefixWord ++ tailWord_259181).sum := by decide
  have hdescent : baseEnd_259181 < baseStart_259181 := by decide
  rcases family_descends (prefixWord ++ tailWord_259181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259183 : List Nat := [1, 1, 2, 1, 3, 3, 8]
def baseStart_259183 : Nat := 118140960795 + 259183 * 2 ^ 59
def prefixEnd_259183 : Nat := 4983230072969 + 3 ^ 40 * 259183 * 2
def baseEnd_259183 : Nat := 26288485229504134127515

theorem tailTrace_259183 : CollatzResearch.WordTrace tailWord_259183 prefixEnd_259183 26288485229504134127515 := by
  unfold tailWord_259183
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453180620031730777398203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6302120413354487184932135 9453180620031730777398203)
  ·
    refine ⟨14179770930047596166097305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9453180620031730777398203 14179770930047596166097305)
    ·
      refine ⟨10634828197535697124572979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14179770930047596166097305 10634828197535697124572979)
      ·
        refine ⟨15952242296303545686859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634828197535697124572979 15952242296303545686859469)
        ·
          refine ⟨5982090861113829632572301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15952242296303545686859469 5982090861113829632572301)
          ·
            refine ⟨2243284072917686112214613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5982090861113829632572301 2243284072917686112214613)
            ·
              refine ⟨26288485229504134127515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2243284072917686112214613 26288485229504134127515)
              ·
                rfl

theorem cell19_259183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_259183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259183 prefixEnd_259183 := by exact prefixLift 259183
  have htrace : WordTrace (prefixWord ++ tailWord_259183) baseStart_259183 baseEnd_259183 := by
    simpa [prefixWord, tailWord_259183, baseEnd_259183] using wordTrace_append hprefix tailTrace_259183
  have hstable : (prefixWord ++ tailWord_259183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259183).length < 2 ^ (prefixWord ++ tailWord_259183).sum := by decide
  have hdescent : baseEnd_259183 < baseStart_259183 := by decide
  rcases family_descends (prefixWord ++ tailWord_259183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259219 : List Nat := [1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_259219 : Nat := 118140960795 + 259219 * 2 ^ 59
def prefixEnd_259219 : Nat := 4983230072969 + 3 ^ 40 * 259219 * 2
def baseEnd_259219 : Nat := 78876409942474985582447

theorem tailTrace_259219 : CollatzResearch.WordTrace tailWord_259219 prefixEnd_259219 78876409942474985582447 := by
  unfold tailWord_259219
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454493647901308925708711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6302995765267539283805807 9454493647901308925708711)
  ·
    refine ⟨14181740471851963388563067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454493647901308925708711 14181740471851963388563067)
    ·
      refine ⟨21272610707777945082844601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181740471851963388563067 21272610707777945082844601)
      ·
        refine ⟨15954458030833458812133451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21272610707777945082844601 15954458030833458812133451)
        ·
          refine ⟨23931687046250188218200177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15954458030833458812133451 23931687046250188218200177)
          ·
            refine ⟨17948765284687641163650133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23931687046250188218200177 17948765284687641163650133)
            ·
              refine ⟨210337093179933294886525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 17948765284687641163650133 210337093179933294886525)
              ·
                refine ⟨78876409942474985582447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210337093179933294886525 78876409942474985582447)
                ·
                  rfl

theorem cell19_259219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_259219 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259219 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259219 prefixEnd_259219 := by exact prefixLift 259219
  have htrace : WordTrace (prefixWord ++ tailWord_259219) baseStart_259219 baseEnd_259219 := by
    simpa [prefixWord, tailWord_259219, baseEnd_259219] using wordTrace_append hprefix tailTrace_259219
  have hstable : (prefixWord ++ tailWord_259219).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259219).length < 2 ^ (prefixWord ++ tailWord_259219).sum := by decide
  have hdescent : baseEnd_259219 < baseStart_259219 := by decide
  rcases family_descends (prefixWord ++ tailWord_259219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259234 : List Nat := [3, 3, 1, 3, 3, 1, 5]
def baseStart_259234 : Nat := 118140960795 + 259234 * 2 ^ 59
def prefixEnd_259234 : Nat := 4983230072969 + 3 ^ 40 * 259234 * 2
def baseEnd_259234 : Nat := 26293658071653131749691

theorem tailTrace_259234 : CollatzResearch.WordTrace tailWord_259234 prefixEnd_259234 26293658071653131749691 := by
  unfold tailWord_259234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363760185711741621876189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6303360495231310991669837 2363760185711741621876189)
  ·
    refine ⟨886410069641903108203571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2363760185711741621876189 886410069641903108203571)
    ·
      refine ⟨1329615104462854662305357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886410069641903108203571 1329615104462854662305357)
      ·
        refine ⟨498605664173570498364509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1329615104462854662305357 498605664173570498364509)
        ·
          refine ⟨186977124065088936886691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498605664173570498364509 186977124065088936886691)
          ·
            refine ⟨280465686097633405330037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186977124065088936886691 280465686097633405330037)
            ·
              refine ⟨26293658071653131749691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280465686097633405330037 26293658071653131749691)
              ·
                rfl

theorem cell19_259234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_259234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259234 prefixEnd_259234 := by exact prefixLift 259234
  have htrace : WordTrace (prefixWord ++ tailWord_259234) baseStart_259234 baseEnd_259234 := by
    simpa [prefixWord, tailWord_259234, baseEnd_259234] using wordTrace_append hprefix tailTrace_259234
  have hstable : (prefixWord ++ tailWord_259234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259234).length < 2 ^ (prefixWord ++ tailWord_259234).sum := by decide
  have hdescent : baseEnd_259234 < baseStart_259234 := by decide
  rcases family_descends (prefixWord ++ tailWord_259234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259257 : List Nat := [1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_259257 : Nat := 118140960795 + 259257 * 2 ^ 59
def prefixEnd_259257 : Nat := 4983230072969 + 3 ^ 40 * 259257 * 2
def baseEnd_259257 : Nat := 78887972766102156737899

theorem tailTrace_259257 : CollatzResearch.WordTrace tailWord_259257 prefixEnd_259257 78887972766102156737899 := by
  unfold tailWord_259257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455879621763641415592025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6303919747842427610394683 9455879621763641415592025)
  ·
    refine ⟨7091909716322731061694019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9455879621763641415592025 7091909716322731061694019)
    ·
      refine ⟨10637864574484096592541029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091909716322731061694019 10637864574484096592541029)
      ·
        refine ⟨1994599607715768111101443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10637864574484096592541029 1994599607715768111101443)
        ·
          refine ⟨2991899411573652166652165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994599607715768111101443 2991899411573652166652165)
          ·
            refine ⟨560981139670059781247281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2991899411573652166652165 560981139670059781247281)
            ·
              refine ⟨420735854752544835935461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560981139670059781247281 420735854752544835935461)
              ·
                refine ⟨78887972766102156737899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420735854752544835935461 78887972766102156737899)
                ·
                  rfl

theorem cell19_259257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_259257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259257 prefixEnd_259257 := by exact prefixLift 259257
  have htrace : WordTrace (prefixWord ++ tailWord_259257) baseStart_259257 baseEnd_259257 := by
    simpa [prefixWord, tailWord_259257, baseEnd_259257] using wordTrace_append hprefix tailTrace_259257
  have hstable : (prefixWord ++ tailWord_259257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259257).length < 2 ^ (prefixWord ++ tailWord_259257).sum := by decide
  have hdescent : baseEnd_259257 < baseStart_259257 := by decide
  rcases family_descends (prefixWord ++ tailWord_259257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259293 : List Nat := [1, 4, 3, 2, 3, 6]
def baseStart_259293 : Nat := 118140960795 + 259293 * 2 ^ 59
def prefixEnd_259293 : Nat := 4983230072969 + 3 ^ 40 * 259293 * 2
def baseEnd_259293 : Nat := 8766547446673859993089

theorem tailTrace_259293 : CollatzResearch.WordTrace tailWord_259293 prefixEnd_259293 8766547446673859993089 := by
  unfold tailWord_259293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457192649633219563902533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6304795099755479709268355 9457192649633219563902533)
  ·
    refine ⟨1773223621806228668231725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9457192649633219563902533 1773223621806228668231725)
    ·
      refine ⟨664958858177335750586897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1773223621806228668231725 664958858177335750586897)
      ·
        refine ⟨498719143633001812940173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664958858177335750586897 498719143633001812940173)
        ·
          refine ⟨187019678862375679852565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498719143633001812940173 187019678862375679852565)
          ·
            refine ⟨8766547446673859993089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187019678862375679852565 8766547446673859993089)
            ·
              rfl

theorem cell19_259293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_259293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259293 prefixEnd_259293 := by exact prefixLift 259293
  have htrace : WordTrace (prefixWord ++ tailWord_259293) baseStart_259293 baseEnd_259293 := by
    simpa [prefixWord, tailWord_259293, baseEnd_259293] using wordTrace_append hprefix tailTrace_259293
  have hstable : (prefixWord ++ tailWord_259293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259293).length < 2 ^ (prefixWord ++ tailWord_259293).sum := by decide
  have hdescent : baseEnd_259293 < baseStart_259293 := by decide
  rcases family_descends (prefixWord ++ tailWord_259293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259297 : List Nat := [1, 2, 3, 1, 3, 9]
def baseStart_259297 : Nat := 118140960795 + 259297 * 2 ^ 59
def prefixEnd_259297 : Nat := 4983230072969 + 3 ^ 40 * 259297 * 2
def baseEnd_259297 : Nat := 8766682684377101760989

theorem tailTrace_259297 : CollatzResearch.WordTrace tailWord_259297 prefixEnd_259297 8766682684377101760989 := by
  unfold tailWord_259297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457338541618728247048145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6304892361079152164698763 9457338541618728247048145)
  ·
    refine ⟨7093003906214046185286109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9457338541618728247048145 7093003906214046185286109)
    ·
      refine ⟨2659876464830267319482291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7093003906214046185286109 2659876464830267319482291)
      ·
        refine ⟨3989814697245400979223437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659876464830267319482291 3989814697245400979223437)
        ·
          refine ⟨1496180511467025367208789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3989814697245400979223437 1496180511467025367208789)
          ·
            refine ⟨8766682684377101760989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1496180511467025367208789 8766682684377101760989)
            ·
              rfl

theorem cell19_259297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_259297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259297 prefixEnd_259297 := by exact prefixLift 259297
  have htrace : WordTrace (prefixWord ++ tailWord_259297) baseStart_259297 baseEnd_259297 := by
    simpa [prefixWord, tailWord_259297, baseEnd_259297] using wordTrace_append hprefix tailTrace_259297
  have hstable : (prefixWord ++ tailWord_259297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259297).length < 2 ^ (prefixWord ++ tailWord_259297).sum := by decide
  have hdescent : baseEnd_259297 < baseStart_259297 := by decide
  rcases family_descends (prefixWord ++ tailWord_259297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259333 : List Nat := [1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_259333 : Nat := 118140960795 + 259333 * 2 ^ 59
def prefixEnd_259333 : Nat := 4983230072969 + 3 ^ 40 * 259333 * 2
def baseEnd_259333 : Nat := 78911098413356499048803

theorem tailTrace_259333 : CollatzResearch.WordTrace tailWord_259333 prefixEnd_259333 78911098413356499048803 := by
  unfold tailWord_259333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458651569488306395358653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305767712992204263572435 9458651569488306395358653)
  ·
    refine ⟨3546994338558114898259495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9458651569488306395358653 3546994338558114898259495)
    ·
      refine ⟨5320491507837172347389243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546994338558114898259495 5320491507837172347389243)
      ·
        refine ⟨7980737261755758521083865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320491507837172347389243 7980737261755758521083865)
        ·
          refine ⟨5985552946316818890812899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980737261755758521083865 5985552946316818890812899)
          ·
            refine ⟨8978329419475228336219349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985552946316818890812899 8978329419475228336219349)
            ·
              refine ⟨210429595768950664130141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8978329419475228336219349 210429595768950664130141)
              ·
                refine ⟨78911098413356499048803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210429595768950664130141 78911098413356499048803)
                ·
                  rfl

theorem cell19_259333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_259333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259333 prefixEnd_259333 := by exact prefixLift 259333
  have htrace : WordTrace (prefixWord ++ tailWord_259333) baseStart_259333 baseEnd_259333 := by
    simpa [prefixWord, tailWord_259333, baseEnd_259333] using wordTrace_append hprefix tailTrace_259333
  have hstable : (prefixWord ++ tailWord_259333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259333).length < 2 ^ (prefixWord ++ tailWord_259333).sum := by decide
  have hdescent : baseEnd_259333 < baseStart_259333 := by decide
  rcases family_descends (prefixWord ++ tailWord_259333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259382 : List Nat := [5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_259382 : Nat := 118140960795 + 259382 * 2 ^ 59
def prefixEnd_259382 : Nat := 4983230072969 + 3 ^ 40 * 259382 * 2
def baseEnd_259382 : Nat := 78926008370138903959781

theorem tailTrace_259382 : CollatzResearch.WordTrace tailWord_259382 prefixEnd_259382 78926008370138903959781 := by
  unfold tailWord_259382
  simp only [CollatzResearch.WordTrace]
  refine ⟨591277421644424235243275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6306959164207191842594933 591277421644424235243275)
  ·
    refine ⟨886916132466636352864913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591277421644424235243275 886916132466636352864913)
    ·
      refine ⟨665187099349977264648685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886916132466636352864913 665187099349977264648685)
      ·
        refine ⟨249445162256241474243257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665187099349977264648685 249445162256241474243257)
        ·
          refine ⟨187083871692181105682443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249445162256241474243257 187083871692181105682443)
          ·
            refine ⟨280625807538271658523665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187083871692181105682443 280625807538271658523665)
            ·
              refine ⟨210469355653703743892749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280625807538271658523665 210469355653703743892749)
              ·
                refine ⟨78926008370138903959781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210469355653703743892749 78926008370138903959781)
                ·
                  rfl

theorem cell19_259382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_259382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259382 prefixEnd_259382 := by exact prefixLift 259382
  have htrace : WordTrace (prefixWord ++ tailWord_259382) baseStart_259382 baseEnd_259382 := by
    simpa [prefixWord, tailWord_259382, baseEnd_259382] using wordTrace_append hprefix tailTrace_259382
  have hstable : (prefixWord ++ tailWord_259382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259382).length < 2 ^ (prefixWord ++ tailWord_259382).sum := by decide
  have hdescent : baseEnd_259382 < baseStart_259382 := by decide
  rcases family_descends (prefixWord ++ tailWord_259382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259388 : List Nat := [2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_259388 : Nat := 118140960795 + 259388 * 2 ^ 59
def prefixEnd_259388 : Nat := 4983230072969 + 3 ^ 40 * 259388 * 2
def baseEnd_259388 : Nat := 78927834079132667826431

theorem tailTrace_259388 : CollatzResearch.WordTrace tailWord_259388 prefixEnd_259388 78927834079132667826431 := by
  unfold tailWord_259388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730328792144525394305409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6307105056192700525740545 4730328792144525394305409)
  ·
    refine ⟨3547746594108394045729057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730328792144525394305409 3547746594108394045729057)
    ·
      refine ⟨2660809945581295534296793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3547746594108394045729057 2660809945581295534296793)
      ·
        refine ⟨1995607459185971650722595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2660809945581295534296793 1995607459185971650722595)
        ·
          refine ⟨2993411188778957476083893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995607459185971650722595 2993411188778957476083893)
          ·
            refine ⟨280632298948027263382865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2993411188778957476083893 280632298948027263382865)
            ·
              refine ⟨210474224211020447537149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280632298948027263382865 210474224211020447537149)
              ·
                refine ⟨78927834079132667826431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210474224211020447537149 78927834079132667826431)
                ·
                  rfl

theorem cell19_259388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_259388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259388 prefixEnd_259388 := by exact prefixLift 259388
  have htrace : WordTrace (prefixWord ++ tailWord_259388) baseStart_259388 baseEnd_259388 := by
    simpa [prefixWord, tailWord_259388, baseEnd_259388] using wordTrace_append hprefix tailTrace_259388
  have hstable : (prefixWord ++ tailWord_259388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259388).length < 2 ^ (prefixWord ++ tailWord_259388).sum := by decide
  have hdescent : baseEnd_259388 < baseStart_259388 := by decide
  rcases family_descends (prefixWord ++ tailWord_259388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259390 : List Nat := [4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_259390 : Nat := 118140960795 + 259390 * 2 ^ 59
def prefixEnd_259390 : Nat := 4983230072969 + 3 ^ 40 * 259390 * 2
def baseEnd_259390 : Nat := 78928442648797255781981

theorem tailTrace_259390 : CollatzResearch.WordTrace tailWord_259390 prefixEnd_259390 78928442648797255781981 := by
  unfold tailWord_259390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182591316285225641272953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6307153686854536753455749 1182591316285225641272953)
  ·
    refine ⟨886943487213919230954715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1182591316285225641272953 886943487213919230954715)
    ·
      refine ⟨1330415230820878846432073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886943487213919230954715 1330415230820878846432073)
      ·
        refine ⟨997811423115659134824055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330415230820878846432073 997811423115659134824055)
        ·
          refine ⟨1496717134673488702236083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997811423115659134824055 1496717134673488702236083)
          ·
            refine ⟨2245075702010233053354125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496717134673488702236083 2245075702010233053354125)
            ·
              refine ⟨841903388253837395007797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245075702010233053354125 841903388253837395007797)
              ·
                refine ⟨78928442648797255781981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841903388253837395007797 78928442648797255781981)
                ·
                  rfl

theorem cell19_259390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_259390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259390 prefixEnd_259390 := by exact prefixLift 259390
  have htrace : WordTrace (prefixWord ++ tailWord_259390) baseStart_259390 baseEnd_259390 := by
    simpa [prefixWord, tailWord_259390, baseEnd_259390] using wordTrace_append hprefix tailTrace_259390
  have hstable : (prefixWord ++ tailWord_259390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259390).length < 2 ^ (prefixWord ++ tailWord_259390).sum := by decide
  have hdescent : baseEnd_259390 < baseStart_259390 := by decide
  rcases family_descends (prefixWord ++ tailWord_259390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259392 : List Nat := [2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_259392 : Nat := 118140960795 + 259392 * 2 ^ 59
def prefixEnd_259392 : Nat := 4983230072969 + 3 ^ 40 * 259392 * 2
def baseEnd_259392 : Nat := 78929051218461843737531

theorem tailTrace_259392 : CollatzResearch.WordTrace tailWord_259392 prefixEnd_259392 78929051218461843737531 := by
  unfold tailWord_259392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730401738137279735878215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6307202317516372981170953 4730401738137279735878215)
  ·
    refine ⟨7095602607205919603817323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4730401738137279735878215 7095602607205919603817323)
    ·
      refine ⟨10643403910808879405725985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095602607205919603817323 10643403910808879405725985)
      ·
        refine ⟨7982552933106659554294489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10643403910808879405725985 7982552933106659554294489)
        ·
          refine ⟨5986914699829994665720867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7982552933106659554294489 5986914699829994665720867)
          ·
            refine ⟨8980372049744991998581301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986914699829994665720867 8980372049744991998581301)
            ·
              refine ⟨841909879663592999866997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8980372049744991998581301 841909879663592999866997)
              ·
                refine ⟨78929051218461843737531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841909879663592999866997 78929051218461843737531)
                ·
                  rfl

theorem cell19_259392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_259392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259392 prefixEnd_259392 := by exact prefixLift 259392
  have htrace : WordTrace (prefixWord ++ tailWord_259392) baseStart_259392 baseEnd_259392 := by
    simpa [prefixWord, tailWord_259392, baseEnd_259392] using wordTrace_append hprefix tailTrace_259392
  have hstable : (prefixWord ++ tailWord_259392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259392).length < 2 ^ (prefixWord ++ tailWord_259392).sum := by decide
  have hdescent : baseEnd_259392 < baseStart_259392 := by decide
  rcases family_descends (prefixWord ++ tailWord_259392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259405 : List Nat := [1, 6, 1, 3, 1, 2, 5]
def baseStart_259405 : Nat := 118140960795 + 259405 * 2 ^ 59
def prefixEnd_259405 : Nat := 4983230072969 + 3 ^ 40 * 259405 * 2
def baseEnd_259405 : Nat := 26311002307093888482869

theorem tailTrace_259405 : CollatzResearch.WordTrace tailWord_259405 prefixEnd_259405 26311002307093888482869 := by
  unfold tailWord_259405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461277625227462691979669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307518416818308461319779 9461277625227462691979669)
  ·
    refine ⟨443497388682537313686547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9461277625227462691979669 443497388682537313686547)
    ·
      refine ⟨665246083023805970529821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443497388682537313686547 665246083023805970529821)
      ·
        refine ⟨249467281133927238948683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665246083023805970529821 249467281133927238948683)
        ·
          refine ⟨374200921700890858423025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249467281133927238948683 374200921700890858423025)
          ·
            refine ⟨280650691275668143817269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374200921700890858423025 280650691275668143817269)
            ·
              refine ⟨26311002307093888482869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280650691275668143817269 26311002307093888482869)
              ·
                rfl

theorem cell19_259405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_259405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259405 prefixEnd_259405 := by exact prefixLift 259405
  have htrace : WordTrace (prefixWord ++ tailWord_259405) baseStart_259405 baseEnd_259405 := by
    simpa [prefixWord, tailWord_259405, baseEnd_259405] using wordTrace_append hprefix tailTrace_259405
  have hstable : (prefixWord ++ tailWord_259405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259405).length < 2 ^ (prefixWord ++ tailWord_259405).sum := by decide
  have hdescent : baseEnd_259405 < baseStart_259405 := by decide
  rcases family_descends (prefixWord ++ tailWord_259405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259428 : List Nat := [2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_259428 : Nat := 118140960795 + 259428 * 2 ^ 59
def prefixEnd_259428 : Nat := 4983230072969 + 3 ^ 40 * 259428 * 2
def baseEnd_259428 : Nat := 78940005472424426937433

theorem tailTrace_259428 : CollatzResearch.WordTrace tailWord_259428 prefixEnd_259428 78940005472424426937433 := by
  unfold tailWord_259428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731058252072068810033469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6308077669429425080044625 4731058252072068810033469)
  ·
    refine ⟨1774146844527025803762551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4731058252072068810033469 1774146844527025803762551)
    ·
      refine ⟨2661220266790538705643827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774146844527025803762551 2661220266790538705643827)
      ·
        refine ⟨3991830400185808058465741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661220266790538705643827 3991830400185808058465741)
        ·
          refine ⟨1496936400069678021924653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991830400185808058465741 1496936400069678021924653)
          ·
            refine ⟨561351150026129258221745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1496936400069678021924653 561351150026129258221745)
            ·
              refine ⟨421013362519596943666309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561351150026129258221745 421013362519596943666309)
              ·
                refine ⟨78940005472424426937433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421013362519596943666309 78940005472424426937433)
                ·
                  rfl

theorem cell19_259428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_259428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259428 prefixEnd_259428 := by exact prefixLift 259428
  have htrace : WordTrace (prefixWord ++ tailWord_259428) baseStart_259428 baseEnd_259428 := by
    simpa [prefixWord, tailWord_259428, baseEnd_259428] using wordTrace_append hprefix tailTrace_259428
  have hstable : (prefixWord ++ tailWord_259428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259428).length < 2 ^ (prefixWord ++ tailWord_259428).sum := by decide
  have hdescent : baseEnd_259428 < baseStart_259428 := by decide
  rcases family_descends (prefixWord ++ tailWord_259428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259449 : List Nat := [1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_259449 : Nat := 118140960795 + 259449 * 2 ^ 59
def prefixEnd_259449 : Nat := 4983230072969 + 3 ^ 40 * 259449 * 2
def baseEnd_259449 : Nat := 78946395453902600470709

theorem tailTrace_259449 : CollatzResearch.WordTrace tailWord_259449 prefixEnd_259449 78946395453902600470709 := by
  unfold tailWord_259449
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462882437068058206581401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6308588291378705471054267 9462882437068058206581401)
  ·
    refine ⟨7097161827801043654936051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9462882437068058206581401 7097161827801043654936051)
    ·
      refine ⟨10645742741701565482404077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097161827801043654936051 10645742741701565482404077)
      ·
        refine ⟨3992153528138087055901529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10645742741701565482404077 3992153528138087055901529)
        ·
          refine ⟨2994115146103565291926147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3992153528138087055901529 2994115146103565291926147)
          ·
            refine ⟨4491172719155347937889221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994115146103565291926147 4491172719155347937889221)
            ·
              refine ⟨842094884841627738354229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4491172719155347937889221 842094884841627738354229)
              ·
                refine ⟨78946395453902600470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842094884841627738354229 78946395453902600470709)
                ·
                  rfl

theorem cell19_259449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_259449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259449 prefixEnd_259449 := by exact prefixLift 259449
  have htrace : WordTrace (prefixWord ++ tailWord_259449) baseStart_259449 baseEnd_259449 := by
    simpa [prefixWord, tailWord_259449, baseEnd_259449] using wordTrace_append hprefix tailTrace_259449
  have hstable : (prefixWord ++ tailWord_259449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259449).length < 2 ^ (prefixWord ++ tailWord_259449).sum := by decide
  have hdescent : baseEnd_259449 < baseStart_259449 := by decide
  rcases family_descends (prefixWord ++ tailWord_259449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259485 : List Nat := [1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_259485 : Nat := 118140960795 + 259485 * 2 ^ 59
def prefixEnd_259485 : Nat := 4983230072969 + 3 ^ 40 * 259485 * 2
def baseEnd_259485 : Nat := 78957349707865183670611

theorem tailTrace_259485 : CollatzResearch.WordTrace tailWord_259485 prefixEnd_259485 78957349707865183670611 := by
  unfold tailWord_259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464195464937636354891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6309463643291757569927939 9464195464937636354891909)
  ·
    refine ⟨1774536649675806816542233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9464195464937636354891909 1774536649675806816542233)
    ·
      refine ⟨1330902487256855112406675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774536649675806816542233 1330902487256855112406675)
      ·
        refine ⟨1996353730885282668610013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330902487256855112406675 1996353730885282668610013)
        ·
          refine ⟨748632649081981000728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1996353730885282668610013 748632649081981000728755)
          ·
            refine ⟨1122948973622971501093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748632649081981000728755 1122948973622971501093133)
            ·
              refine ⟨421105865108614312909925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122948973622971501093133 421105865108614312909925)
              ·
                refine ⟨78957349707865183670611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421105865108614312909925 78957349707865183670611)
                ·
                  rfl

theorem cell19_259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_259485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259485 prefixEnd_259485 := by exact prefixLift 259485
  have htrace : WordTrace (prefixWord ++ tailWord_259485) baseStart_259485 baseEnd_259485 := by
    simpa [prefixWord, tailWord_259485, baseEnd_259485] using wordTrace_append hprefix tailTrace_259485
  have hstable : (prefixWord ++ tailWord_259485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259485).length < 2 ^ (prefixWord ++ tailWord_259485).sum := by decide
  have hdescent : baseEnd_259485 < baseStart_259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259559 : List Nat := [1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_259559 : Nat := 118140960795 + 259559 * 2 ^ 59
def prefixEnd_259559 : Nat := 4983230072969 + 3 ^ 40 * 259559 * 2
def baseEnd_259559 : Nat := 78979866785454938025965

theorem tailTrace_259559 : CollatzResearch.WordTrace tailWord_259559 prefixEnd_259559 78979866785454938025965 := by
  unfold tailWord_259559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466894466669546993085731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311262977779697995390487 9466894466669546993085731)
  ·
    refine ⟨14200341700004320489628597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9466894466669546993085731 14200341700004320489628597)
    ·
      refine ⟨1331282034375405045902681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14200341700004320489628597 1331282034375405045902681)
      ·
        refine ⟨998461525781553784427011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331282034375405045902681 998461525781553784427011)
        ·
          refine ⟨1497692288672330676640517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998461525781553784427011 1497692288672330676640517)
          ·
            refine ⟨280817304126062001870097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1497692288672330676640517 280817304126062001870097)
            ·
              refine ⟨210612978094546501402573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280817304126062001870097 210612978094546501402573)
              ·
                refine ⟨78979866785454938025965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210612978094546501402573 78979866785454938025965)
                ·
                  rfl

theorem cell19_259559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_259559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259559 prefixEnd_259559 := by exact prefixLift 259559
  have htrace : WordTrace (prefixWord ++ tailWord_259559) baseStart_259559 baseEnd_259559 := by
    simpa [prefixWord, tailWord_259559, baseEnd_259559] using wordTrace_append hprefix tailTrace_259559
  have hstable : (prefixWord ++ tailWord_259559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259559).length < 2 ^ (prefixWord ++ tailWord_259559).sum := by decide
  have hdescent : baseEnd_259559 < baseStart_259559 := by decide
  rcases family_descends (prefixWord ++ tailWord_259559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259601 : List Nat := [1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_259601 : Nat := 118140960795 + 259601 * 2 ^ 59
def prefixEnd_259601 : Nat := 4983230072969 + 3 ^ 40 * 259601 * 2
def baseEnd_259601 : Nat := 78992646748411285092517

theorem tailTrace_259601 : CollatzResearch.WordTrace tailWord_259601 prefixEnd_259601 78992646748411285092517 := by
  unfold tailWord_259601
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468426332517388166114657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312284221678258777409771 9468426332517388166114657)
  ·
    refine ⟨7101319749388041124585993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9468426332517388166114657 7101319749388041124585993)
    ·
      refine ⟨5325989812041030843439495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7101319749388041124585993 5325989812041030843439495)
      ·
        refine ⟨7988984718061546265159243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325989812041030843439495 7988984718061546265159243)
        ·
          refine ⟨11983477077092319397738865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988984718061546265159243 11983477077092319397738865)
          ·
            refine ⟨8987607807819239548304149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11983477077092319397738865 8987607807819239548304149)
            ·
              refine ⟨421294115991526853826757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8987607807819239548304149 421294115991526853826757)
              ·
                refine ⟨78992646748411285092517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421294115991526853826757 78992646748411285092517)
                ·
                  rfl

theorem cell19_259601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_259601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259601 prefixEnd_259601 := by exact prefixLift 259601
  have htrace : WordTrace (prefixWord ++ tailWord_259601) baseStart_259601 baseEnd_259601 := by
    simpa [prefixWord, tailWord_259601, baseEnd_259601] using wordTrace_append hprefix tailTrace_259601
  have hstable : (prefixWord ++ tailWord_259601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259601).length < 2 ^ (prefixWord ++ tailWord_259601).sum := by decide
  have hdescent : baseEnd_259601 < baseStart_259601 := by decide
  rcases family_descends (prefixWord ++ tailWord_259601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259694 : List Nat := [4, 1, 2, 2, 3, 1, 6]
def baseStart_259694 : Nat := 118140960795 + 259694 * 2 ^ 59
def prefixEnd_259694 : Nat := 4983230072969 + 3 ^ 40 * 259694 * 2
def baseEnd_259694 : Nat := 26340315079271541675199

theorem tailTrace_259694 : CollatzResearch.WordTrace tailWord_259694 prefixEnd_259694 26340315079271541675199 := by
  unfold tailWord_259694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183977290147558131156267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6314545547453643366166757 1183977290147558131156267)
  ·
    refine ⟨1775965935221337196734401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183977290147558131156267 1775965935221337196734401)
    ·
      refine ⟨1331974451416002897550801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775965935221337196734401 1331974451416002897550801)
      ·
        refine ⟨998980838562002173163101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331974451416002897550801 998980838562002173163101)
        ·
          refine ⟨374617814460750814936163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 998980838562002173163101 374617814460750814936163)
          ·
            refine ⟨561926721691126222404245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374617814460750814936163 561926721691126222404245)
            ·
              refine ⟨26340315079271541675199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561926721691126222404245 26340315079271541675199)
              ·
                rfl

theorem cell19_259694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_259694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259694 prefixEnd_259694 := by exact prefixLift 259694
  have htrace : WordTrace (prefixWord ++ tailWord_259694) baseStart_259694 baseEnd_259694 := by
    simpa [prefixWord, tailWord_259694, baseEnd_259694] using wordTrace_append hprefix tailTrace_259694
  have hstable : (prefixWord ++ tailWord_259694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259694).length < 2 ^ (prefixWord ++ tailWord_259694).sum := by decide
  have hdescent : baseEnd_259694 < baseStart_259694 := by decide
  rcases family_descends (prefixWord ++ tailWord_259694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259696 : List Nat := [2, 1, 1, 1, 6, 2, 6]
def baseStart_259696 : Nat := 118140960795 + 259696 * 2 ^ 59
def prefixEnd_259696 : Nat := 4983230072969 + 3 ^ 40 * 259696 * 2
def baseEnd_259696 : Nat := 26340517935826404327049

theorem tailTrace_259696 : CollatzResearch.WordTrace tailWord_259696 prefixEnd_259696 26340517935826404327049 := by
  unfold tailWord_259696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735945633586609695411471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6314594178115479593881961 4735945633586609695411471)
  ·
    refine ⟨7103918450379914543117207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735945633586609695411471 7103918450379914543117207)
    ·
      refine ⟨10655877675569871814675811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103918450379914543117207 10655877675569871814675811)
      ·
        refine ⟨15983816513354807722013717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655877675569871814675811 15983816513354807722013717)
        ·
          refine ⟨749241399063506611969393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15983816513354807722013717 749241399063506611969393)
          ·
            refine ⟨561931049297629958977045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749241399063506611969393 561931049297629958977045)
            ·
              refine ⟨26340517935826404327049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561931049297629958977045 26340517935826404327049)
              ·
                rfl

theorem cell19_259696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_259696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_259696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_259696 prefixEnd_259696 := by exact prefixLift 259696
  have htrace : WordTrace (prefixWord ++ tailWord_259696) baseStart_259696 baseEnd_259696 := by
    simpa [prefixWord, tailWord_259696, baseEnd_259696] using wordTrace_append hprefix tailTrace_259696
  have hstable : (prefixWord ++ tailWord_259696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259696).length < 2 ^ (prefixWord ++ tailWord_259696).sum := by decide
  have hdescent : baseEnd_259696 < baseStart_259696 := by decide
  rcases family_descends (prefixWord ++ tailWord_259696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
