import V185TrunkScan20Chunk104

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_638284 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_638284 : Nat := 118140960795 + 638284 * 2 ^ 59
def prefixEnd_638284 : Nat := 4983230072969 + 3 ^ 40 * 638284 * 2
def baseEnd_638284 : Nat := 291330209843987506324081

theorem tailTrace_638284 : CollatzResearch.WordTrace tailWord_638284 prefixEnd_638284 291330209843987506324081 := by
  unfold tailWord_638284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11640065009806776536780953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15520086679742368715707937 11640065009806776536780953)
  ·
    refine ⟨8730048757355082402585715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11640065009806776536780953 8730048757355082402585715)
    ·
      refine ⟨13095073136032623603878573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8730048757355082402585715 13095073136032623603878573)
      ·
        refine ⟨4910652426012233851454465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13095073136032623603878573 4910652426012233851454465)
        ·
          refine ⟨3682989319509175388590849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4910652426012233851454465 3682989319509175388590849)
          ·
            refine ⟨2762241989631881541443137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3682989319509175388590849 2762241989631881541443137)
            ·
              refine ⟨2071681492223911156082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762241989631881541443137 2071681492223911156082353)
              ·
                refine ⟨1553761119167933367061765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071681492223911156082353 1553761119167933367061765)
                ·
                  refine ⟨291330209843987506324081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1553761119167933367061765 291330209843987506324081)
                  ·
                    rfl

theorem cell20_638284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_638284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638284 prefixEnd_638284 := by exact prefixLift 638284
  have htrace : WordTrace (prefixWord ++ tailWord_638284) baseStart_638284 baseEnd_638284 := by
    simpa [prefixWord, tailWord_638284, baseEnd_638284] using wordTrace_append hprefix tailTrace_638284
  have hstable : (prefixWord ++ tailWord_638284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638284).length < 2 ^ (prefixWord ++ tailWord_638284).sum := by decide
  have hdescent : baseEnd_638284 < baseStart_638284 := by decide
  rcases family_descends (prefixWord ++ tailWord_638284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638298 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_638298 : Nat := 118140960795 + 638298 * 2 ^ 59
def prefixEnd_638298 : Nat := 4983230072969 + 3 ^ 40 * 638298 * 2
def baseEnd_638298 : Nat := 291336599825465679857357

theorem tailTrace_638298 : CollatzResearch.WordTrace tailWord_638298 prefixEnd_638298 291336599825465679857357 := by
  unfold tailWord_638298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820160160390708366142887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15520427094375222309714365 5820160160390708366142887)
  ·
    refine ⟨8730240240586062549214331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820160160390708366142887 8730240240586062549214331)
    ·
      refine ⟨13095360360879093823821497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8730240240586062549214331 13095360360879093823821497)
      ·
        refine ⟨9821520270659320367866123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13095360360879093823821497 9821520270659320367866123)
        ·
          refine ⟨14732280405988980551799185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9821520270659320367866123 14732280405988980551799185)
          ·
            refine ⟨11049210304491735413849389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14732280405988980551799185 11049210304491735413849389)
            ·
              refine ⟨4143453864184400780193521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11049210304491735413849389 4143453864184400780193521)
              ·
                refine ⟨3107590398138300585145141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143453864184400780193521 3107590398138300585145141)
                ·
                  refine ⟨291336599825465679857357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3107590398138300585145141 291336599825465679857357)
                  ·
                    rfl

theorem cell20_638298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_638298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638298 prefixEnd_638298 := by exact prefixLift 638298
  have htrace : WordTrace (prefixWord ++ tailWord_638298) baseStart_638298 baseEnd_638298 := by
    simpa [prefixWord, tailWord_638298, baseEnd_638298] using wordTrace_append hprefix tailTrace_638298
  have hstable : (prefixWord ++ tailWord_638298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638298).length < 2 ^ (prefixWord ++ tailWord_638298).sum := by decide
  have hdescent : baseEnd_638298 < baseStart_638298 := by decide
  rcases family_descends (prefixWord ++ tailWord_638298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638305 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_638305 : Nat := 118140960795 + 638305 * 2 ^ 59
def prefixEnd_638305 : Nat := 4983230072969 + 3 ^ 40 * 638305 * 2
def baseEnd_638305 : Nat := 291339794816204766623995

theorem tailTrace_638305 : CollatzResearch.WordTrace tailWord_638305 prefixEnd_638305 291339794816204766623995 := by
  unfold tailWord_638305
  simp only [CollatzResearch.WordTrace]
  refine ⟨23280895952537473660076369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15520597301691649106717579 23280895952537473660076369)
  ·
    refine ⟨17460671964403105245057277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23280895952537473660076369 17460671964403105245057277)
    ·
      refine ⟨6547751986651164466896479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17460671964403105245057277 6547751986651164466896479)
      ·
        refine ⟨9821627979976746700344719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547751986651164466896479 9821627979976746700344719)
        ·
          refine ⟨14732441969965120050517079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9821627979976746700344719 14732441969965120050517079)
          ·
            refine ⟨22098662954947680075775619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14732441969965120050517079 22098662954947680075775619)
            ·
              refine ⟨33147994432421520113663429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22098662954947680075775619 33147994432421520113663429)
              ·
                refine ⟨6215248956079035021311893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33147994432421520113663429 6215248956079035021311893)
                ·
                  refine ⟨291339794816204766623995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6215248956079035021311893 291339794816204766623995)
                  ·
                    rfl

theorem cell20_638305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_638305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638305 prefixEnd_638305 := by exact prefixLift 638305
  have htrace : WordTrace (prefixWord ++ tailWord_638305) baseStart_638305 baseEnd_638305 := by
    simpa [prefixWord, tailWord_638305, baseEnd_638305] using wordTrace_append hprefix tailTrace_638305
  have hstable : (prefixWord ++ tailWord_638305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638305).length < 2 ^ (prefixWord ++ tailWord_638305).sum := by decide
  have hdescent : baseEnd_638305 < baseStart_638305 := by decide
  rcases family_descends (prefixWord ++ tailWord_638305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638370 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_638370 : Nat := 118140960795 + 638370 * 2 ^ 59
def prefixEnd_638370 : Nat := 4983230072969 + 3 ^ 40 * 638370 * 2
def baseEnd_638370 : Nat := 291369462587353429457063

theorem tailTrace_638370 : CollatzResearch.WordTrace tailWord_638370 prefixEnd_638370 291369462587353429457063 := by
  unfold tailWord_638370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820816674325497440298141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15522177798201326507461709 5820816674325497440298141)
  ·
    refine ⟨2182806252872061540111803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5820816674325497440298141 2182806252872061540111803)
    ·
      refine ⟨3274209379308092310167705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182806252872061540111803 3274209379308092310167705)
      ·
        refine ⟨2455657034481069232625779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3274209379308092310167705 2455657034481069232625779)
        ·
          refine ⟨3683485551721603848938669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455657034481069232625779 3683485551721603848938669)
          ·
            refine ⟨1381307081895601443352001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3683485551721603848938669 1381307081895601443352001)
            ·
              refine ⟨1035980311421701082514001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381307081895601443352001 1035980311421701082514001)
              ·
                refine ⟨776985233566275811885501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035980311421701082514001 776985233566275811885501)
                ·
                  refine ⟨291369462587353429457063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776985233566275811885501 291369462587353429457063)
                  ·
                    rfl

theorem cell20_638370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_638370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638370 prefixEnd_638370 := by exact prefixLift 638370
  have htrace : WordTrace (prefixWord ++ tailWord_638370) baseStart_638370 baseEnd_638370 := by
    simpa [prefixWord, tailWord_638370, baseEnd_638370] using wordTrace_append hprefix tailTrace_638370
  have hstable : (prefixWord ++ tailWord_638370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638370).length < 2 ^ (prefixWord ++ tailWord_638370).sum := by decide
  have hdescent : baseEnd_638370 < baseStart_638370 := by decide
  rcases family_descends (prefixWord ++ tailWord_638370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638422 : List Nat := [5, 2, 1, 1, 1, 3, 7]
def baseStart_638422 : Nat := 118140960795 + 638422 * 2 ^ 59
def prefixEnd_638422 : Nat := 4983230072969 + 3 ^ 40 * 638422 * 2
def baseEnd_638422 : Nat := 32377021867141373302613

theorem tailTrace_638422 : CollatzResearch.WordTrace tailWord_638422 prefixEnd_638422 32377021867141373302613 := by
  unfold tailWord_638422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455322705819600165130345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15523442195409068428057013 1455322705819600165130345)
  ·
    refine ⟨1091492029364700123847759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1455322705819600165130345 1091492029364700123847759)
    ·
      refine ⟨1637238044047050185771639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091492029364700123847759 1637238044047050185771639)
      ·
        refine ⟨2455857066070575278657459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637238044047050185771639 2455857066070575278657459)
        ·
          refine ⟨3683785599105862917986189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455857066070575278657459 3683785599105862917986189)
          ·
            refine ⟨1381419599664698594244821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3683785599105862917986189 1381419599664698594244821)
            ·
              refine ⟨32377021867141373302613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1381419599664698594244821 32377021867141373302613)
              ·
                rfl

theorem cell20_638422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_638422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638422 prefixEnd_638422 := by exact prefixLift 638422
  have htrace : WordTrace (prefixWord ++ tailWord_638422) baseStart_638422 baseEnd_638422 := by
    simpa [prefixWord, tailWord_638422, baseEnd_638422] using wordTrace_append hprefix tailTrace_638422
  have hstable : (prefixWord ++ tailWord_638422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638422).length < 2 ^ (prefixWord ++ tailWord_638422).sum := by decide
  have hdescent : baseEnd_638422 < baseStart_638422 := by decide
  rcases family_descends (prefixWord ++ tailWord_638422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638429 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_638429 : Nat := 118140960795 + 638429 * 2 ^ 59
def prefixEnd_638429 : Nat := 4983230072969 + 3 ^ 40 * 638429 * 2
def baseEnd_638429 : Nat := 291396391795011446490155

theorem tailTrace_638429 : CollatzResearch.WordTrace tailWord_638429 prefixEnd_638429 291396391795011446490155 := by
  unfold tailWord_638429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23285418604088242837590341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15523612402725495225060227 23285418604088242837590341)
  ·
    refine ⟨4366015988266545532048189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23285418604088242837590341 4366015988266545532048189)
    ·
      refine ⟨1637255995599954574518071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4366015988266545532048189 1637255995599954574518071)
      ·
        refine ⟨2455883993399931861777107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637255995599954574518071 2455883993399931861777107)
        ·
          refine ⟨3683825990099897792665661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455883993399931861777107 3683825990099897792665661)
          ·
            refine ⟨1381434746287461672249623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3683825990099897792665661 1381434746287461672249623)
            ·
              refine ⟨2072152119431192508374435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381434746287461672249623 2072152119431192508374435)
              ·
                refine ⟨3108228179146788762561653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072152119431192508374435 3108228179146788762561653)
                ·
                  refine ⟨291396391795011446490155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108228179146788762561653 291396391795011446490155)
                  ·
                    rfl

theorem cell20_638429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_638429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638429 prefixEnd_638429 := by exact prefixLift 638429
  have htrace : WordTrace (prefixWord ++ tailWord_638429) baseStart_638429 baseEnd_638429 := by
    simpa [prefixWord, tailWord_638429, baseEnd_638429] using wordTrace_append hprefix tailTrace_638429
  have hstable : (prefixWord ++ tailWord_638429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638429).length < 2 ^ (prefixWord ++ tailWord_638429).sum := by decide
  have hdescent : baseEnd_638429 < baseStart_638429 := by decide
  rcases family_descends (prefixWord ++ tailWord_638429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638446 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_638446 : Nat := 118140960795 + 638446 * 2 ^ 59
def prefixEnd_638446 : Nat := 4983230072969 + 3 ^ 40 * 638446 * 2
def baseEnd_638446 : Nat := 291404151058234942923419

theorem tailTrace_638446 : CollatzResearch.WordTrace tailWord_638446 prefixEnd_638446 291404151058234942923419 := by
  unfold tailWord_638446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910754830628331842619899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15524025763351103160639461 2910754830628331842619899)
  ·
    refine ⟨4366132245942497763929849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910754830628331842619899 4366132245942497763929849)
    ·
      refine ⟨3274599184456873322947387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4366132245942497763929849 3274599184456873322947387)
      ·
        refine ⟨4911898776685309984421081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274599184456873322947387 4911898776685309984421081)
        ·
          refine ⟨3683924082513982488315811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911898776685309984421081 3683924082513982488315811)
          ·
            refine ⟨5525886123770973732473717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683924082513982488315811 5525886123770973732473717)
            ·
              refine ⟨518051824103528787419411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5525886123770973732473717 518051824103528787419411)
              ·
                refine ⟨777077736155293181129117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518051824103528787419411 777077736155293181129117)
                ·
                  refine ⟨291404151058234942923419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777077736155293181129117 291404151058234942923419)
                  ·
                    rfl

theorem cell20_638446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_638446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638446 prefixEnd_638446 := by exact prefixLift 638446
  have htrace : WordTrace (prefixWord ++ tailWord_638446) baseStart_638446 baseEnd_638446 := by
    simpa [prefixWord, tailWord_638446, baseEnd_638446] using wordTrace_append hprefix tailTrace_638446
  have hstable : (prefixWord ++ tailWord_638446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638446).length < 2 ^ (prefixWord ++ tailWord_638446).sum := by decide
  have hdescent : baseEnd_638446 < baseStart_638446 := by decide
  rcases family_descends (prefixWord ++ tailWord_638446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638453 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_638453 : Nat := 118140960795 + 638453 * 2 ^ 59
def prefixEnd_638453 : Nat := 4983230072969 + 3 ^ 40 * 638453 * 2
def baseEnd_638453 : Nat := 291407346048974029690057

theorem tailTrace_638453 : CollatzResearch.WordTrace tailWord_638453 prefixEnd_638453 291407346048974029690057 := by
  unfold tailWord_638453
  simp only [CollatzResearch.WordTrace]
  refine ⟨23286293956001294936464013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15524195970667529957642675 23286293956001294936464013)
  ·
    refine ⟨8732360233500485601174005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23286293956001294936464013 8732360233500485601174005)
    ·
      refine ⟨818658771890670525110063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8732360233500485601174005 818658771890670525110063)
      ·
        refine ⟨1227988157836005787665095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818658771890670525110063 1227988157836005787665095)
        ·
          refine ⟨1841982236754008681497643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227988157836005787665095 1841982236754008681497643)
          ·
            refine ⟨2762973355131013022246465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841982236754008681497643 2762973355131013022246465)
            ·
              refine ⟨2072230016348259766684849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762973355131013022246465 2072230016348259766684849)
              ·
                refine ⟨1554172512261194825013637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072230016348259766684849 1554172512261194825013637)
                ·
                  refine ⟨291407346048974029690057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554172512261194825013637 291407346048974029690057)
                  ·
                    rfl

theorem cell20_638453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_638453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638453 prefixEnd_638453 := by exact prefixLift 638453
  have htrace : WordTrace (prefixWord ++ tailWord_638453) baseStart_638453 baseEnd_638453 := by
    simpa [prefixWord, tailWord_638453, baseEnd_638453] using wordTrace_append hprefix tailTrace_638453
  have hstable : (prefixWord ++ tailWord_638453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638453).length < 2 ^ (prefixWord ++ tailWord_638453).sum := by decide
  have hdescent : baseEnd_638453 < baseStart_638453 := by decide
  rcases family_descends (prefixWord ++ tailWord_638453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638529 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 2]
def baseStart_638529 : Nat := 118140960795 + 638529 * 2 ^ 59
def prefixEnd_638529 : Nat := 4983230072969 + 3 ^ 40 * 638529 * 2
def baseEnd_638529 : Nat := 291442034519855543156413

theorem tailTrace_638529 : CollatzResearch.WordTrace tailWord_638529 prefixEnd_638529 291442034519855543156413 := by
  unfold tailWord_638529
  simp only [CollatzResearch.WordTrace]
  refine ⟨23289065903725959916230641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15526043935817306610820427 23289065903725959916230641)
  ·
    refine ⟨17466799427794469937172981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23289065903725959916230641 17466799427794469937172981)
    ·
      refine ⟨1637512446355731556609967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17466799427794469937172981 1637512446355731556609967)
      ·
        refine ⟨2456268669533597334914951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637512446355731556609967 2456268669533597334914951)
        ·
          refine ⟨3684403004300396002372427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456268669533597334914951 3684403004300396002372427)
          ·
            refine ⟨5526604506450594003558641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684403004300396002372427 5526604506450594003558641)
            ·
              refine ⟨4144953379837945502668981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526604506450594003558641 4144953379837945502668981)
              ·
                refine ⟨388589379359807390875217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4144953379837945502668981 388589379359807390875217)
                ·
                  refine ⟨291442034519855543156413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388589379359807390875217 291442034519855543156413)
                  ·
                    rfl

theorem cell20_638529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_638529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638529 prefixEnd_638529 := by exact prefixLift 638529
  have htrace : WordTrace (prefixWord ++ tailWord_638529) baseStart_638529 baseEnd_638529 := by
    simpa [prefixWord, tailWord_638529, baseEnd_638529] using wordTrace_append hprefix tailTrace_638529
  have hstable : (prefixWord ++ tailWord_638529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638529).length < 2 ^ (prefixWord ++ tailWord_638529).sum := by decide
  have hdescent : baseEnd_638529 < baseStart_638529 := by decide
  rcases family_descends (prefixWord ++ tailWord_638529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638540 : List Nat := [2, 2, 1, 3, 1, 11]
def baseStart_638540 : Nat := 118140960795 + 638540 * 2 ^ 59
def prefixEnd_638540 : Nat := 4983230072969 + 3 ^ 40 * 638540 * 2
def baseEnd_638540 : Nat := 10794335378503273844063

theorem tailTrace_638540 : CollatzResearch.WordTrace tailWord_638540 prefixEnd_638540 10794335378503273844063 := by
  unfold tailWord_638540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644733553343054397440537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15526311404457405863254049 11644733553343054397440537)
  ·
    refine ⟨8733550165007290798080403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11644733553343054397440537 8733550165007290798080403)
    ·
      refine ⟨13100325247510936197120605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733550165007290798080403 13100325247510936197120605)
      ·
        refine ⟨4912621967816601073920227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13100325247510936197120605 4912621967816601073920227)
        ·
          refine ⟨7368932951724901610880341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912621967816601073920227 7368932951724901610880341)
          ·
            refine ⟨10794335378503273844063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7368932951724901610880341 10794335378503273844063)
            ·
              rfl

theorem cell20_638540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 11].length) (baseStart_638540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638540 prefixEnd_638540 := by exact prefixLift 638540
  have htrace : WordTrace (prefixWord ++ tailWord_638540) baseStart_638540 baseEnd_638540 := by
    simpa [prefixWord, tailWord_638540, baseEnd_638540] using wordTrace_append hprefix tailTrace_638540
  have hstable : (prefixWord ++ tailWord_638540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638540).length < 2 ^ (prefixWord ++ tailWord_638540).sum := by decide
  have hdescent : baseEnd_638540 < baseStart_638540 := by decide
  rcases family_descends (prefixWord ++ tailWord_638540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638546 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_638546 : Nat := 118140960795 + 638546 * 2 ^ 59
def prefixEnd_638546 : Nat := 4983230072969 + 3 ^ 40 * 638546 * 2
def baseEnd_638546 : Nat := 291449793783079039589677

theorem tailTrace_638546 : CollatzResearch.WordTrace tailWord_638546 prefixEnd_638546 291449793783079039589677 := by
  unfold tailWord_638546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822421486166092954899873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15526457296442914546399661 5822421486166092954899873)
  ·
    refine ⟨4366816114624569716174905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5822421486166092954899873 4366816114624569716174905)
    ·
      refine ⟨3275112085968427287131179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4366816114624569716174905 3275112085968427287131179)
      ·
        refine ⟨4912668128952640930696769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275112085968427287131179 4912668128952640930696769)
        ·
          refine ⟨3684501096714480698022577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4912668128952640930696769 3684501096714480698022577)
          ·
            refine ⟨2763375822535860523516933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684501096714480698022577 2763375822535860523516933)
            ·
              refine ⟨518132966725473848159425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2763375822535860523516933 518132966725473848159425)
              ·
                refine ⟨388599725044105386119569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518132966725473848159425 388599725044105386119569)
                ·
                  refine ⟨291449793783079039589677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388599725044105386119569 291449793783079039589677)
                  ·
                    rfl

theorem cell20_638546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_638546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638546 prefixEnd_638546 := by exact prefixLift 638546
  have htrace : WordTrace (prefixWord ++ tailWord_638546) baseStart_638546 baseEnd_638546 := by
    simpa [prefixWord, tailWord_638546, baseEnd_638546] using wordTrace_append hprefix tailTrace_638546
  have hstable : (prefixWord ++ tailWord_638546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638546).length < 2 ^ (prefixWord ++ tailWord_638546).sum := by decide
  have hdescent : baseEnd_638546 < baseStart_638546 := by decide
  rcases family_descends (prefixWord ++ tailWord_638546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638660 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_638660 : Nat := 118140960795 + 638660 * 2 ^ 59
def prefixEnd_638660 : Nat := 4983230072969 + 3 ^ 40 * 638660 * 2
def baseEnd_638660 : Nat := 291501826489401309789211

theorem tailTrace_638660 : CollatzResearch.WordTrace tailWord_638660 prefixEnd_638660 291501826489401309789211 := by
  unfold tailWord_638660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646921933125684644624717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15529229244167579526166289 11646921933125684644624717)
  ·
    refine ⟨4367595724922131741734269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11646921933125684644624717 4367595724922131741734269)
    ·
      refine ⟨1637848396845799403150351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4367595724922131741734269 1637848396845799403150351)
      ·
        refine ⟨2456772595268699104725527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637848396845799403150351 2456772595268699104725527)
        ·
          refine ⟨3685158892903048657088291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456772595268699104725527 3685158892903048657088291)
          ·
            refine ⟨5527738339354572985632437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685158892903048657088291 5527738339354572985632437)
            ·
              refine ⟨518225469314491217403041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5527738339354572985632437 518225469314491217403041)
              ·
                refine ⟨388669101985868413052281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518225469314491217403041 388669101985868413052281)
                ·
                  refine ⟨291501826489401309789211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388669101985868413052281 291501826489401309789211)
                  ·
                    rfl

theorem cell20_638660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_638660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638660 prefixEnd_638660 := by exact prefixLift 638660
  have htrace : WordTrace (prefixWord ++ tailWord_638660) baseStart_638660 baseEnd_638660 := by
    simpa [prefixWord, tailWord_638660, baseEnd_638660] using wordTrace_append hprefix tailTrace_638660
  have hstable : (prefixWord ++ tailWord_638660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638660).length < 2 ^ (prefixWord ++ tailWord_638660).sum := by decide
  have hdescent : baseEnd_638660 < baseStart_638660 := by decide
  rcases family_descends (prefixWord ++ tailWord_638660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638674 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_638674 : Nat := 118140960795 + 638674 * 2 ^ 59
def prefixEnd_638674 : Nat := 4983230072969 + 3 ^ 40 * 638674 * 2
def baseEnd_638674 : Nat := 291508216470879483322487

theorem tailTrace_638674 : CollatzResearch.WordTrace tailWord_638674 prefixEnd_638674 291508216470879483322487 := by
  unfold tailWord_638674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823588622050162420064769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15529569658800433120172717 5823588622050162420064769)
  ·
    refine ⟨4367691466537621815048577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5823588622050162420064769 4367691466537621815048577)
    ·
      refine ⟨3275768599903216361286433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4367691466537621815048577 3275768599903216361286433)
      ·
        refine ⟨2456826449927412270964825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3275768599903216361286433 2456826449927412270964825)
        ·
          refine ⟨1842619837445559203223619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2456826449927412270964825 1842619837445559203223619)
          ·
            refine ⟨2763929756168338804835429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842619837445559203223619 2763929756168338804835429)
            ·
              refine ⟨518236829281563525906643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2763929756168338804835429 518236829281563525906643)
              ·
                refine ⟨777355243922345288859965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518236829281563525906643 777355243922345288859965)
                ·
                  refine ⟨291508216470879483322487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777355243922345288859965 291508216470879483322487)
                  ·
                    rfl

theorem cell20_638674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_638674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638674 prefixEnd_638674 := by exact prefixLift 638674
  have htrace : WordTrace (prefixWord ++ tailWord_638674) baseStart_638674 baseEnd_638674 := by
    simpa [prefixWord, tailWord_638674, baseEnd_638674] using wordTrace_append hprefix tailTrace_638674
  have hstable : (prefixWord ++ tailWord_638674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638674).length < 2 ^ (prefixWord ++ tailWord_638674).sum := by decide
  have hdescent : baseEnd_638674 < baseStart_638674 := by decide
  rcases family_descends (prefixWord ++ tailWord_638674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638692 : List Nat := [2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_638692 : Nat := 118140960795 + 638692 * 2 ^ 59
def prefixEnd_638692 : Nat := 4983230072969 + 3 ^ 40 * 638692 * 2
def baseEnd_638692 : Nat := 97172144053783806907471

theorem tailTrace_638692 : CollatzResearch.WordTrace tailWord_638692 prefixEnd_638692 97172144053783806907471 := by
  unfold tailWord_638692
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647505501067719377207165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15530007334756959169609553 11647505501067719377207165)
  ·
    refine ⟨4367814562900394766452687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11647505501067719377207165 4367814562900394766452687)
    ·
      refine ⟨6551721844350592149679031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367814562900394766452687 6551721844350592149679031)
      ·
        refine ⟨9827582766525888224518547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6551721844350592149679031 9827582766525888224518547)
        ·
          refine ⟨14741374149788832336777821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9827582766525888224518547 14741374149788832336777821)
          ·
            refine ⟨5528015306170812126291683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14741374149788832336777821 5528015306170812126291683)
            ·
              refine ⟨8292022959256218189437525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5528015306170812126291683 8292022959256218189437525)
              ·
                refine ⟨97172144053783806907471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8292022959256218189437525 97172144053783806907471)
                ·
                  rfl

theorem cell20_638692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_638692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638692 prefixEnd_638692 := by exact prefixLift 638692
  have htrace : WordTrace (prefixWord ++ tailWord_638692) baseStart_638692 baseEnd_638692 := by
    simpa [prefixWord, tailWord_638692, baseEnd_638692] using wordTrace_append hprefix tailTrace_638692
  have hstable : (prefixWord ++ tailWord_638692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638692).length < 2 ^ (prefixWord ++ tailWord_638692).sum := by decide
  have hdescent : baseEnd_638692 < baseStart_638692 := by decide
  rcases family_descends (prefixWord ++ tailWord_638692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638699 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_638699 : Nat := 118140960795 + 638699 * 2 ^ 59
def prefixEnd_638699 : Nat := 4983230072969 + 3 ^ 40 * 638699 * 2
def baseEnd_638699 : Nat := 291519627152090507489051

theorem tailTrace_638699 : CollatzResearch.WordTrace tailWord_638699 prefixEnd_638699 291519627152090507489051 := by
  unfold tailWord_638699
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295266313110078949919151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15530177542073385966612767 23295266313110078949919151)
  ·
    refine ⟨34942899469665118424878727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23295266313110078949919151 34942899469665118424878727)
    ·
      refine ⟨52414349204497677637318091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34942899469665118424878727 52414349204497677637318091)
      ·
        refine ⟨78621523806746516455977137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52414349204497677637318091 78621523806746516455977137)
        ·
          refine ⟨58966142855059887341982853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78621523806746516455977137 58966142855059887341982853)
          ·
            refine ⟨11056151785323728876621785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58966142855059887341982853 11056151785323728876621785)
            ·
              refine ⟨8292113838992796657466339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11056151785323728876621785 8292113838992796657466339)
              ·
                refine ⟨12438170758489194986199509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8292113838992796657466339 12438170758489194986199509)
                ·
                  refine ⟨291519627152090507489051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438170758489194986199509 291519627152090507489051)
                  ·
                    rfl

theorem cell20_638699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_638699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638699 prefixEnd_638699 := by exact prefixLift 638699
  have htrace : WordTrace (prefixWord ++ tailWord_638699) baseStart_638699 baseEnd_638699 := by
    simpa [prefixWord, tailWord_638699, baseEnd_638699] using wordTrace_append hprefix tailTrace_638699
  have hstable : (prefixWord ++ tailWord_638699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638699).length < 2 ^ (prefixWord ++ tailWord_638699).sum := by decide
  have hdescent : baseEnd_638699 < baseStart_638699 := by decide
  rcases family_descends (prefixWord ++ tailWord_638699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638709 : List Nat := [1, 3, 6, 10]
def baseStart_638709 : Nat := 118140960795 + 638709 * 2 ^ 59
def prefixEnd_638709 : Nat := 4983230072969 + 3 ^ 40 * 638709 * 2
def baseEnd_638709 : Nat := 1199688030553806243439

theorem tailTrace_638709 : CollatzResearch.WordTrace tailWord_638709 prefixEnd_638709 1199688030553806243439 := by
  unfold tailWord_638709
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295631043073850657783181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15530420695382567105188787 23295631043073850657783181)
  ·
    refine ⟨8735861641152693996668693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23295631043073850657783181 8735861641152693996668693)
    ·
      refine ⟨409493514429032531093845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8735861641152693996668693 409493514429032531093845)
      ·
        refine ⟨1199688030553806243439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 409493514429032531093845 1199688030553806243439)
        ·
          rfl

theorem cell20_638709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 10].length) (baseStart_638709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638709 prefixEnd_638709 := by exact prefixLift 638709
  have htrace : WordTrace (prefixWord ++ tailWord_638709) baseStart_638709 baseEnd_638709 := by
    simpa [prefixWord, tailWord_638709, baseEnd_638709] using wordTrace_append hprefix tailTrace_638709
  have hstable : (prefixWord ++ tailWord_638709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638709).length < 2 ^ (prefixWord ++ tailWord_638709).sum := by decide
  have hdescent : baseEnd_638709 < baseStart_638709 := by decide
  rcases family_descends (prefixWord ++ tailWord_638709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638719 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 2]
def baseStart_638719 : Nat := 118140960795 + 638719 * 2 ^ 59
def prefixEnd_638719 : Nat := 4983230072969 + 3 ^ 40 * 638719 * 2
def baseEnd_638719 : Nat := 291528755697059326822303

theorem tailTrace_638719 : CollatzResearch.WordTrace tailWord_638719 prefixEnd_638719 291528755697059326822303 := by
  unfold tailWord_638719
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295995773037622365647211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15530663848691748243764807 23295995773037622365647211)
  ·
    refine ⟨34943993659556433548470817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23295995773037622365647211 34943993659556433548470817)
    ·
      refine ⟨26207995244667325161353113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34943993659556433548470817 26207995244667325161353113)
      ·
        refine ⟨19655996433500493871014835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26207995244667325161353113 19655996433500493871014835)
        ·
          refine ⟨29483994650250740806522253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19655996433500493871014835 29483994650250740806522253)
          ·
            refine ⟨11056497993844027802445845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29483994650250740806522253 11056497993844027802445845)
            ·
              refine ⟨518273343461438803239649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11056497993844027802445845 518273343461438803239649)
              ·
                refine ⟨388705007596079102429737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518273343461438803239649 388705007596079102429737)
                ·
                  refine ⟨291528755697059326822303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388705007596079102429737 291528755697059326822303)
                  ·
                    rfl

theorem cell20_638719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2].length) (baseStart_638719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638719 prefixEnd_638719 := by exact prefixLift 638719
  have htrace : WordTrace (prefixWord ++ tailWord_638719) baseStart_638719 baseEnd_638719 := by
    simpa [prefixWord, tailWord_638719, baseEnd_638719] using wordTrace_append hprefix tailTrace_638719
  have hstable : (prefixWord ++ tailWord_638719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638719).length < 2 ^ (prefixWord ++ tailWord_638719).sum := by decide
  have hdescent : baseEnd_638719 < baseStart_638719 := by decide
  rcases family_descends (prefixWord ++ tailWord_638719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638737 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_638737 : Nat := 118140960795 + 638737 * 2 ^ 59
def prefixEnd_638737 : Nat := 4983230072969 + 3 ^ 40 * 638737 * 2
def baseEnd_638737 : Nat := 291536971387531264222229

theorem tailTrace_638737 : CollatzResearch.WordTrace tailWord_638737 prefixEnd_638737 291536971387531264222229 := by
  unfold tailWord_638737
  simp only [CollatzResearch.WordTrace]
  refine ⟨23296652286972411439802465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15531101524648274293201643 23296652286972411439802465)
  ·
    refine ⟨17472489215229308579851849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23296652286972411439802465 17472489215229308579851849)
    ·
      refine ⟨13104366911421981434888887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17472489215229308579851849 13104366911421981434888887)
      ·
        refine ⟨19656550367132972152333331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13104366911421981434888887 19656550367132972152333331)
        ·
          refine ⟨29484825550699458228499997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19656550367132972152333331 29484825550699458228499997)
          ·
            refine ⟨11056809581512296835687499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29484825550699458228499997 11056809581512296835687499)
            ·
              refine ⟨16585214372268445253531249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056809581512296835687499 16585214372268445253531249)
              ·
                refine ⟨12438910779201333940148437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16585214372268445253531249 12438910779201333940148437)
                ·
                  refine ⟨291536971387531264222229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438910779201333940148437 291536971387531264222229)
                  ·
                    rfl

theorem cell20_638737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_638737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638737 prefixEnd_638737 := by exact prefixLift 638737
  have htrace : WordTrace (prefixWord ++ tailWord_638737) baseStart_638737 baseEnd_638737 := by
    simpa [prefixWord, tailWord_638737, baseEnd_638737] using wordTrace_append hprefix tailTrace_638737
  have hstable : (prefixWord ++ tailWord_638737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638737).length < 2 ^ (prefixWord ++ tailWord_638737).sum := by decide
  have hdescent : baseEnd_638737 < baseStart_638737 := by decide
  rcases family_descends (prefixWord ++ tailWord_638737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638754 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_638754 : Nat := 118140960795 + 638754 * 2 ^ 59
def prefixEnd_638754 : Nat := 4983230072969 + 3 ^ 40 * 638754 * 2
def baseEnd_638754 : Nat := 291544730650754760655493

theorem tailTrace_638754 : CollatzResearch.WordTrace tailWord_638754 prefixEnd_638754 291544730650754760655493 := by
  unfold tailWord_638754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824318081977705835792829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15531514885273882228780877 5824318081977705835792829)
  ·
    refine ⟨2184119280741639688422311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5824318081977705835792829 2184119280741639688422311)
    ·
      refine ⟨3276178921112459532633467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184119280741639688422311 3276178921112459532633467)
      ·
        refine ⟨4914268381668689298950201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276178921112459532633467 4914268381668689298950201)
        ·
          refine ⟨3685701286251516974212651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4914268381668689298950201 3685701286251516974212651)
          ·
            refine ⟨5528551929377275461318977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685701286251516974212651 5528551929377275461318977)
            ·
              refine ⟨4146413947032956595989233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528551929377275461318977 4146413947032956595989233)
              ·
                refine ⟨3109810460274717446991925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146413947032956595989233 3109810460274717446991925)
                ·
                  refine ⟨291544730650754760655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3109810460274717446991925 291544730650754760655493)
                  ·
                    rfl

theorem cell20_638754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_638754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638754 prefixEnd_638754 := by exact prefixLift 638754
  have htrace : WordTrace (prefixWord ++ tailWord_638754) baseStart_638754 baseEnd_638754 := by
    simpa [prefixWord, tailWord_638754, baseEnd_638754] using wordTrace_append hprefix tailTrace_638754
  have hstable : (prefixWord ++ tailWord_638754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638754).length < 2 ^ (prefixWord ++ tailWord_638754).sum := by decide
  have hdescent : baseEnd_638754 < baseStart_638754 := by decide
  rcases family_descends (prefixWord ++ tailWord_638754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638757 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 2]
def baseStart_638757 : Nat := 118140960795 + 638757 * 2 ^ 59
def prefixEnd_638757 : Nat := 4983230072969 + 3 ^ 40 * 638757 * 2
def baseEnd_638757 : Nat := 291546099932500083555481

theorem tailTrace_638757 : CollatzResearch.WordTrace tailWord_638757 prefixEnd_638757 291546099932500083555481 := by
  unfold tailWord_638757
  simp only [CollatzResearch.WordTrace]
  refine ⟨23297381746899954855530525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15531587831266636570353683 23297381746899954855530525)
  ·
    refine ⟨8736518155087483070823947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23297381746899954855530525 8736518155087483070823947)
    ·
      refine ⟨13104777232631224606235921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736518155087483070823947 13104777232631224606235921)
      ·
        refine ⟨9828582924473418454676941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13104777232631224606235921 9828582924473418454676941)
        ·
          refine ⟨3685718596677531920503853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9828582924473418454676941 3685718596677531920503853)
          ·
            refine ⟨1382144473754074470188945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3685718596677531920503853 1382144473754074470188945)
            ·
              refine ⟨1036608355315555852641709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382144473754074470188945 1036608355315555852641709)
              ·
                refine ⟨388728133243333444740641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036608355315555852641709 388728133243333444740641)
                ·
                  refine ⟨291546099932500083555481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388728133243333444740641 291546099932500083555481)
                  ·
                    rfl

theorem cell20_638757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_638757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638757 prefixEnd_638757 := by exact prefixLift 638757
  have htrace : WordTrace (prefixWord ++ tailWord_638757) baseStart_638757 baseEnd_638757 := by
    simpa [prefixWord, tailWord_638757, baseEnd_638757] using wordTrace_append hprefix tailTrace_638757
  have hstable : (prefixWord ++ tailWord_638757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638757).length < 2 ^ (prefixWord ++ tailWord_638757).sum := by decide
  have hdescent : baseEnd_638757 < baseStart_638757 := by decide
  rcases family_descends (prefixWord ++ tailWord_638757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638774 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_638774 : Nat := 118140960795 + 638774 * 2 ^ 59
def prefixEnd_638774 : Nat := 4983230072969 + 3 ^ 40 * 638774 * 2
def baseEnd_638774 : Nat := 291553859195723579988745

theorem tailTrace_638774 : CollatzResearch.WordTrace tailWord_638774 prefixEnd_638774 291553859195723579988745 := by
  unfold tailWord_638774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456125111739897922431211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15532001191892244505932917 1456125111739897922431211)
  ·
    refine ⟨2184187667609846883646817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1456125111739897922431211 2184187667609846883646817)
    ·
      refine ⟨1638140750707385162735113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2184187667609846883646817 1638140750707385162735113)
      ·
        refine ⟨1228605563030538872051335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1638140750707385162735113 1228605563030538872051335)
        ·
          refine ⟨1842908344545808308077003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228605563030538872051335 1842908344545808308077003)
          ·
            refine ⟨2764362516818712462115505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842908344545808308077003 2764362516818712462115505)
            ·
              refine ⟨2073271887614034346586629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764362516818712462115505 2073271887614034346586629)
              ·
                refine ⟨388738478927631439984993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2073271887614034346586629 388738478927631439984993)
                ·
                  refine ⟨291553859195723579988745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388738478927631439984993 291553859195723579988745)
                  ·
                    rfl

theorem cell20_638774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_638774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638774 prefixEnd_638774 := by exact prefixLift 638774
  have htrace : WordTrace (prefixWord ++ tailWord_638774) baseStart_638774 baseEnd_638774 := by
    simpa [prefixWord, tailWord_638774, baseEnd_638774] using wordTrace_append hprefix tailTrace_638774
  have hstable : (prefixWord ++ tailWord_638774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638774).length < 2 ^ (prefixWord ++ tailWord_638774).sum := by decide
  have hdescent : baseEnd_638774 < baseStart_638774 := by decide
  rcases family_descends (prefixWord ++ tailWord_638774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638778 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_638778 : Nat := 118140960795 + 638778 * 2 ^ 59
def prefixEnd_638778 : Nat := 4983230072969 + 3 ^ 40 * 638778 * 2
def baseEnd_638778 : Nat := 291555684904717343855395

theorem tailTrace_638778 : CollatzResearch.WordTrace tailWord_638778 prefixEnd_638778 291555684904717343855395 := by
  unfold tailWord_638778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824536919955968860511247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15532098453215916961363325 5824536919955968860511247)
  ·
    refine ⟨8736805379933953290766871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824536919955968860511247 8736805379933953290766871)
    ·
      refine ⟨13105208069900929936150307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736805379933953290766871 13105208069900929936150307)
      ·
        refine ⟨19657812104851394904225461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13105208069900929936150307 19657812104851394904225461)
        ·
          refine ⟨1842919884829818272271137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19657812104851394904225461 1842919884829818272271137)
          ·
            refine ⟨1382189913622363704203353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842919884829818272271137 1382189913622363704203353)
            ·
              refine ⟨1036642435216772778152515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382189913622363704203353 1036642435216772778152515)
              ·
                refine ⟨1554963652825159167228773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036642435216772778152515 1554963652825159167228773)
                ·
                  refine ⟨291555684904717343855395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554963652825159167228773 291555684904717343855395)
                  ·
                    rfl

theorem cell20_638778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_638778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638778 prefixEnd_638778 := by exact prefixLift 638778
  have htrace : WordTrace (prefixWord ++ tailWord_638778) baseStart_638778 baseEnd_638778 := by
    simpa [prefixWord, tailWord_638778, baseEnd_638778] using wordTrace_append hprefix tailTrace_638778
  have hstable : (prefixWord ++ tailWord_638778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638778).length < 2 ^ (prefixWord ++ tailWord_638778).sum := by decide
  have hdescent : baseEnd_638778 < baseStart_638778 := by decide
  rcases family_descends (prefixWord ++ tailWord_638778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638802 : List Nat := [3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_638802 : Nat := 118140960795 + 638802 * 2 ^ 59
def prefixEnd_638802 : Nat := 4983230072969 + 3 ^ 40 * 638802 * 2
def baseEnd_638802 : Nat := 97188879719559975685099

theorem tailTrace_638802 : CollatzResearch.WordTrace tailWord_638802 prefixEnd_638802 97188879719559975685099 := by
  unfold tailWord_638802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824755757934231885229665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15532682021157951693945773 5824755757934231885229665)
  ·
    refine ⟨4368566818450673913922249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5824755757934231885229665 4368566818450673913922249)
    ·
      refine ⟨3276425113838005435441687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4368566818450673913922249 3276425113838005435441687)
      ·
        refine ⟨4914637670757008153162531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276425113838005435441687 4914637670757008153162531)
        ·
          refine ⟨7371956506135512229743797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914637670757008153162531 7371956506135512229743797)
          ·
            refine ⟨691120922450204271538481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7371956506135512229743797 691120922450204271538481)
            ·
              refine ⟨518340691837653203653861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691120922450204271538481 518340691837653203653861)
              ·
                refine ⟨97188879719559975685099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518340691837653203653861 97188879719559975685099)
                ·
                  rfl

theorem cell20_638802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_638802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638802 prefixEnd_638802 := by exact prefixLift 638802
  have htrace : WordTrace (prefixWord ++ tailWord_638802) baseStart_638802 baseEnd_638802 := by
    simpa [prefixWord, tailWord_638802, baseEnd_638802] using wordTrace_append hprefix tailTrace_638802
  have hstable : (prefixWord ++ tailWord_638802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638802).length < 2 ^ (prefixWord ++ tailWord_638802).sum := by decide
  have hdescent : baseEnd_638802 < baseStart_638802 := by decide
  rcases family_descends (prefixWord ++ tailWord_638802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638833 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 2]
def baseStart_638833 : Nat := 118140960795 + 638833 * 2 ^ 59
def prefixEnd_638833 : Nat := 4983230072969 + 3 ^ 40 * 638833 * 2
def baseEnd_638833 : Nat := 291580788403381597021837

theorem tailTrace_638833 : CollatzResearch.WordTrace tailWord_638833 prefixEnd_638833 291580788403381597021837 := by
  unfold tailWord_638833
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300153694624619835297153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15533435796416413223531435 23300153694624619835297153)
  ·
    refine ⟨17475115270968464876472865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23300153694624619835297153 17475115270968464876472865)
    ·
      refine ⟨13106336453226348657354649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17475115270968464876472865 13106336453226348657354649)
      ·
        refine ⟨9829752339919761493015987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13106336453226348657354649 9829752339919761493015987)
        ·
          refine ⟨14744628509879642239523981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829752339919761493015987 14744628509879642239523981)
          ·
            refine ⟨5529235691204865839821493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14744628509879642239523981 5529235691204865839821493)
            ·
              refine ⟨518365846050456172483265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5529235691204865839821493 518365846050456172483265)
              ·
                refine ⟨388774384537842129362449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518365846050456172483265 388774384537842129362449)
                ·
                  refine ⟨291580788403381597021837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388774384537842129362449 291580788403381597021837)
                  ·
                    rfl

theorem cell20_638833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_638833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638833 prefixEnd_638833 := by exact prefixLift 638833
  have htrace : WordTrace (prefixWord ++ tailWord_638833) baseStart_638833 baseEnd_638833 := by
    simpa [prefixWord, tailWord_638833, baseEnd_638833] using wordTrace_append hprefix tailTrace_638833
  have hstable : (prefixWord ++ tailWord_638833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638833).length < 2 ^ (prefixWord ++ tailWord_638833).sum := by decide
  have hdescent : baseEnd_638833 < baseStart_638833 := by decide
  rcases family_descends (prefixWord ++ tailWord_638833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638878 : List Nat := [4, 3, 1, 3, 1, 8]
def baseStart_638878 : Nat := 118140960795 + 638878 * 2 ^ 59
def prefixEnd_638878 : Nat := 4983230072969 + 3 ^ 40 * 638878 * 2
def baseEnd_638878 : Nat := 10800049171465238537839

theorem tailTrace_638878 : CollatzResearch.WordTrace tailWord_638878 prefixEnd_638878 10800049171465238537839 := by
  unfold tailWord_638878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912724372432699065085661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15534529986307728347123525 2912724372432699065085661)
  ·
    refine ⟨1092271639662262149407123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2912724372432699065085661 1092271639662262149407123)
    ·
      refine ⟨1638407459493393224110685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092271639662262149407123 1638407459493393224110685)
      ·
        refine ⟨614402797310022459041507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1638407459493393224110685 614402797310022459041507)
        ·
          refine ⟨921604195965033688562261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614402797310022459041507 921604195965033688562261)
          ·
            refine ⟨10800049171465238537839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 921604195965033688562261 10800049171465238537839)
            ·
              rfl

theorem cell20_638878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 8].length) (baseStart_638878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638878 prefixEnd_638878 := by exact prefixLift 638878
  have htrace : WordTrace (prefixWord ++ tailWord_638878) baseStart_638878 baseEnd_638878 := by
    simpa [prefixWord, tailWord_638878, baseEnd_638878] using wordTrace_append hprefix tailTrace_638878
  have hstable : (prefixWord ++ tailWord_638878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638878).length < 2 ^ (prefixWord ++ tailWord_638878).sum := by decide
  have hdescent : baseEnd_638878 < baseStart_638878 := by decide
  rcases family_descends (prefixWord ++ tailWord_638878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638882 : List Nat := [3, 3, 1, 2, 11]
def baseStart_638882 : Nat := 118140960795 + 638882 * 2 ^ 59
def prefixEnd_638882 : Nat := 4983230072969 + 3 ^ 40 * 638882 * 2
def baseEnd_638882 : Nat := 3600038930105619807263

theorem tailTrace_638882 : CollatzResearch.WordTrace tailWord_638882 prefixEnd_638882 3600038930105619807263 := by
  unfold tailWord_638882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825485217861775300957725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15534627247631400802553933 5825485217861775300957725)
  ·
    refine ⟨2184556956698165737859147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5825485217861775300957725 2184556956698165737859147)
    ·
      refine ⟨3276835435047248606788721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184556956698165737859147 3276835435047248606788721)
      ·
        refine ⟨2457626576285436455091541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3276835435047248606788721 2457626576285436455091541)
        ·
          refine ⟨3600038930105619807263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2457626576285436455091541 3600038930105619807263)
          ·
            rfl

theorem cell20_638882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 11].length) (baseStart_638882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638882 prefixEnd_638882 := by exact prefixLift 638882
  have htrace : WordTrace (prefixWord ++ tailWord_638882) baseStart_638882 baseEnd_638882 := by
    simpa [prefixWord, tailWord_638882, baseEnd_638882] using wordTrace_append hprefix tailTrace_638882
  have hstable : (prefixWord ++ tailWord_638882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638882).length < 2 ^ (prefixWord ++ tailWord_638882).sum := by decide
  have hdescent : baseEnd_638882 < baseStart_638882 := by decide
  rcases family_descends (prefixWord ++ tailWord_638882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638896 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_638896 : Nat := 118140960795 + 638896 * 2 ^ 59
def prefixEnd_638896 : Nat := 4983230072969 + 3 ^ 40 * 638896 * 2
def baseEnd_638896 : Nat := 291609543320033377921579

theorem tailTrace_638896 : CollatzResearch.WordTrace tailWord_638896 prefixEnd_638896 291609543320033377921579 := by
  unfold tailWord_638896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651225746698190797420271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15534967662264254396560361 11651225746698190797420271)
  ·
    refine ⟨17476838620047286196130407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651225746698190797420271 17476838620047286196130407)
    ·
      refine ⟨26215257930070929294195611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17476838620047286196130407 26215257930070929294195611)
      ·
        refine ⟨39322886895106393941293417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26215257930070929294195611 39322886895106393941293417)
        ·
          refine ⟨29492165171329795455970063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39322886895106393941293417 29492165171329795455970063)
          ·
            refine ⟨44238247756994693183955095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29492165171329795455970063 44238247756994693183955095)
            ·
              refine ⟨66357371635492039775932643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44238247756994693183955095 66357371635492039775932643)
              ·
                refine ⟨99536057453238059663898965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66357371635492039775932643 99536057453238059663898965)
                ·
                  refine ⟨291609543320033377921579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99536057453238059663898965 291609543320033377921579)
                  ·
                    rfl

theorem cell20_638896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_638896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638896 prefixEnd_638896 := by exact prefixLift 638896
  have htrace : WordTrace (prefixWord ++ tailWord_638896) baseStart_638896 baseEnd_638896 := by
    simpa [prefixWord, tailWord_638896, baseEnd_638896] using wordTrace_append hprefix tailTrace_638896
  have hstable : (prefixWord ++ tailWord_638896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638896).length < 2 ^ (prefixWord ++ tailWord_638896).sum := by decide
  have hdescent : baseEnd_638896 < baseStart_638896 := by decide
  rcases family_descends (prefixWord ++ tailWord_638896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638927 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_638927 : Nat := 118140960795 + 638927 * 2 ^ 59
def prefixEnd_638927 : Nat := 4983230072969 + 3 ^ 40 * 638927 * 2
def baseEnd_638927 : Nat := 291623692564735047888119

theorem tailTrace_638927 : CollatzResearch.WordTrace tailWord_638927 prefixEnd_638927 291623692564735047888119 := by
  unfold tailWord_638927
  simp only [CollatzResearch.WordTrace]
  refine ⟨23303582156284073889219035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15535721437522715926146023 23303582156284073889219035)
  ·
    refine ⟨34955373234426110833828553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23303582156284073889219035 34955373234426110833828553)
    ·
      refine ⟨26216529925819583125371415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34955373234426110833828553 26216529925819583125371415)
      ·
        refine ⟨39324794888729374688057123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26216529925819583125371415 39324794888729374688057123)
        ·
          refine ⟨58987192333094062032085685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39324794888729374688057123 58987192333094062032085685)
          ·
            refine ⟨5530049281227568315508033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58987192333094062032085685 5530049281227568315508033)
            ·
              refine ⟨4147536960920676236631025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530049281227568315508033 4147536960920676236631025)
              ·
                refine ⟨3110652720690507177473269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147536960920676236631025 3110652720690507177473269)
                ·
                  refine ⟨291623692564735047888119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3110652720690507177473269 291623692564735047888119)
                  ·
                    rfl

theorem cell20_638927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_638927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638927 prefixEnd_638927 := by exact prefixLift 638927
  have htrace : WordTrace (prefixWord ++ tailWord_638927) baseStart_638927 baseEnd_638927 := by
    simpa [prefixWord, tailWord_638927, baseEnd_638927] using wordTrace_append hprefix tailTrace_638927
  have hstable : (prefixWord ++ tailWord_638927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638927).length < 2 ^ (prefixWord ++ tailWord_638927).sum := by decide
  have hdescent : baseEnd_638927 < baseStart_638927 := by decide
  rcases family_descends (prefixWord ++ tailWord_638927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638957 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_638957 : Nat := 118140960795 + 638957 * 2 ^ 59
def prefixEnd_638957 : Nat := 4983230072969 + 3 ^ 40 * 638957 * 2
def baseEnd_638957 : Nat := 291637385382188276887997

theorem tailTrace_638957 : CollatzResearch.WordTrace tailWord_638957 prefixEnd_638957 291637385382188276887997 := by
  unfold tailWord_638957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23304676346175389012811125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15536450897450259341874083 23304676346175389012811125)
  ·
    refine ⟨2184813407453942719951043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23304676346175389012811125 2184813407453942719951043)
    ·
      refine ⟨3277220111180914079926565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184813407453942719951043 3277220111180914079926565)
      ·
        refine ⟨614478770846421389986231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3277220111180914079926565 614478770846421389986231)
        ·
          refine ⟨921718156269632084979347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614478770846421389986231 921718156269632084979347)
          ·
            refine ⟨1382577234404448127469021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921718156269632084979347 1382577234404448127469021)
            ·
              refine ⟨518466462901668047800883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382577234404448127469021 518466462901668047800883)
              ·
                refine ⟨777699694352502071701325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518466462901668047800883 777699694352502071701325)
                ·
                  refine ⟨291637385382188276887997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777699694352502071701325 291637385382188276887997)
                  ·
                    rfl

theorem cell20_638957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_638957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_638957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_638957 prefixEnd_638957 := by exact prefixLift 638957
  have htrace : WordTrace (prefixWord ++ tailWord_638957) baseStart_638957 baseEnd_638957 := by
    simpa [prefixWord, tailWord_638957, baseEnd_638957] using wordTrace_append hprefix tailTrace_638957
  have hstable : (prefixWord ++ tailWord_638957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638957).length < 2 ^ (prefixWord ++ tailWord_638957).sum := by decide
  have hdescent : baseEnd_638957 < baseStart_638957 := by decide
  rcases family_descends (prefixWord ++ tailWord_638957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639016 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_639016 : Nat := 118140960795 + 639016 * 2 ^ 59
def prefixEnd_639016 : Nat := 4983230072969 + 3 ^ 40 * 639016 * 2
def baseEnd_639016 : Nat := 291664314589846293921089

theorem tailTrace_639016 : CollatzResearch.WordTrace tailWord_639016 prefixEnd_639016 291664314589846293921089 := by
  unfold tailWord_639016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653414126480821044604451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15537885501974428059472601 11653414126480821044604451)
  ·
    refine ⟨17480121189721231566906677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11653414126480821044604451 17480121189721231566906677)
    ·
      refine ⟨1638761361536365459397501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17480121189721231566906677 1638761361536365459397501)
      ·
        refine ⟨614535510576137047274063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1638761361536365459397501 614535510576137047274063)
        ·
          refine ⟨921803265864205570911095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614535510576137047274063 921803265864205570911095)
          ·
            refine ⟨1382704898796308356366643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921803265864205570911095 1382704898796308356366643)
            ·
              refine ⟨2074057348194462534549965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382704898796308356366643 2074057348194462534549965)
              ·
                refine ⟨777771505572923450456237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074057348194462534549965 777771505572923450456237)
                ·
                  refine ⟨291664314589846293921089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777771505572923450456237 291664314589846293921089)
                  ·
                    rfl

theorem cell20_639016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_639016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639016 prefixEnd_639016 := by exact prefixLift 639016
  have htrace : WordTrace (prefixWord ++ tailWord_639016) baseStart_639016 baseEnd_639016 := by
    simpa [prefixWord, tailWord_639016, baseEnd_639016] using wordTrace_append hprefix tailTrace_639016
  have hstable : (prefixWord ++ tailWord_639016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639016).length < 2 ^ (prefixWord ++ tailWord_639016).sum := by decide
  have hdescent : baseEnd_639016 < baseStart_639016 := by decide
  rcases family_descends (prefixWord ++ tailWord_639016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639048 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_639048 : Nat := 118140960795 + 639048 * 2 ^ 59
def prefixEnd_639048 : Nat := 4983230072969 + 3 ^ 40 * 639048 * 2
def baseEnd_639048 : Nat := 291678920261796404854291

theorem tailTrace_639048 : CollatzResearch.WordTrace tailWord_639048 prefixEnd_639048 291678920261796404854291 := by
  unfold tailWord_639048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653997694422855777186899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15538663592563807702915865 11653997694422855777186899)
  ·
    refine ⟨17480996541634283665780349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11653997694422855777186899 17480996541634283665780349)
    ·
      refine ⟨6555373703112856374667631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17480996541634283665780349 6555373703112856374667631)
      ·
        refine ⟨9833060554669284562001447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555373703112856374667631 9833060554669284562001447)
        ·
          refine ⟨14749590832003926843002171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833060554669284562001447 14749590832003926843002171)
          ·
            refine ⟨22124386248005890264503257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14749590832003926843002171 22124386248005890264503257)
            ·
              refine ⟨16593289686004417698377443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22124386248005890264503257 16593289686004417698377443)
              ·
                refine ⟨24889934529006626547566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16593289686004417698377443 24889934529006626547566165)
                ·
                  refine ⟨291678920261796404854291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24889934529006626547566165 291678920261796404854291)
                  ·
                    rfl

theorem cell20_639048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_639048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639048 prefixEnd_639048 := by exact prefixLift 639048
  have htrace : WordTrace (prefixWord ++ tailWord_639048) baseStart_639048 baseEnd_639048 := by
    simpa [prefixWord, tailWord_639048, baseEnd_639048] using wordTrace_append hprefix tailTrace_639048
  have hstable : (prefixWord ++ tailWord_639048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639048).length < 2 ^ (prefixWord ++ tailWord_639048).sum := by decide
  have hdescent : baseEnd_639048 < baseStart_639048 := by decide
  rcases family_descends (prefixWord ++ tailWord_639048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639061 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 2]
def baseStart_639061 : Nat := 118140960795 + 639061 * 2 ^ 59
def prefixEnd_639061 : Nat := 4983230072969 + 3 ^ 40 * 639061 * 2
def baseEnd_639061 : Nat := 291684853816026137420905

theorem tailTrace_639061 : CollatzResearch.WordTrace tailWord_639061 prefixEnd_639061 291684853816026137420905 := by
  unfold tailWord_639061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23308469537798614774597037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15538979691865743183064691 23308469537798614774597037)
  ·
    refine ⟨8740676076674480540473889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23308469537798614774597037 8740676076674480540473889)
    ·
      refine ⟨6555507057505860405355417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8740676076674480540473889 6555507057505860405355417)
      ·
        refine ⟨4916630293129395304016563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6555507057505860405355417 4916630293129395304016563)
        ·
          refine ⟨7374945439694092956024845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916630293129395304016563 7374945439694092956024845)
          ·
            refine ⟨2765604539885284858509317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7374945439694092956024845 2765604539885284858509317)
            ·
              refine ⟨518550851228490910970497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2765604539885284858509317 518550851228490910970497)
              ·
                refine ⟨388913138421368183227873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518550851228490910970497 388913138421368183227873)
                ·
                  refine ⟨291684853816026137420905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388913138421368183227873 291684853816026137420905)
                  ·
                    rfl

theorem cell20_639061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_639061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639061 prefixEnd_639061 := by exact prefixLift 639061
  have htrace : WordTrace (prefixWord ++ tailWord_639061) baseStart_639061 baseEnd_639061 := by
    simpa [prefixWord, tailWord_639061, baseEnd_639061] using wordTrace_append hprefix tailTrace_639061
  have hstable : (prefixWord ++ tailWord_639061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639061).length < 2 ^ (prefixWord ++ tailWord_639061).sum := by decide
  have hdescent : baseEnd_639061 < baseStart_639061 := by decide
  rcases family_descends (prefixWord ++ tailWord_639061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639072 : List Nat := [2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_639072 : Nat := 118140960795 + 639072 * 2 ^ 59
def prefixEnd_639072 : Nat := 4983230072969 + 3 ^ 40 * 639072 * 2
def baseEnd_639072 : Nat := 97229958171919662684731

theorem tailTrace_639072 : CollatzResearch.WordTrace tailWord_639072 prefixEnd_639072 97229958171919662684731 := by
  unfold tailWord_639072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654435370379381826623735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15539247160505842435498313 11654435370379381826623735)
  ·
    refine ⟨17481653055569072739935603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11654435370379381826623735 17481653055569072739935603)
    ·
      refine ⟨26222479583353609109903405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17481653055569072739935603 26222479583353609109903405)
      ·
        refine ⟨9833429843757603416213777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26222479583353609109903405 9833429843757603416213777)
        ·
          refine ⟨7375072382818202562160333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9833429843757603416213777 7375072382818202562160333)
          ·
            refine ⟨2765652143556825960810125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7375072382818202562160333 2765652143556825960810125)
            ·
              refine ⟨1037119553833809735303797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2765652143556825960810125 1037119553833809735303797)
              ·
                refine ⟨97229958171919662684731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1037119553833809735303797 97229958171919662684731)
                ·
                  rfl

theorem cell20_639072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_639072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639072 prefixEnd_639072 := by exact prefixLift 639072
  have htrace : WordTrace (prefixWord ++ tailWord_639072) baseStart_639072 baseEnd_639072 := by
    simpa [prefixWord, tailWord_639072, baseEnd_639072] using wordTrace_append hprefix tailTrace_639072
  have hstable : (prefixWord ++ tailWord_639072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639072).length < 2 ^ (prefixWord ++ tailWord_639072).sum := by decide
  have hdescent : baseEnd_639072 < baseStart_639072 := by decide
  rcases family_descends (prefixWord ++ tailWord_639072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639082 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_639082 : Nat := 118140960795 + 639082 * 2 ^ 59
def prefixEnd_639082 : Nat := 4983230072969 + 3 ^ 40 * 639082 * 2
def baseEnd_639082 : Nat := 291694438788243397720819

theorem tailTrace_639082 : CollatzResearch.WordTrace tailWord_639082 prefixEnd_639082 291694438788243397720819 := by
  unfold tailWord_639082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827308867680633840277875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15539490313815023574074333 5827308867680633840277875)
  ·
    refine ⟨8740963301520950760416813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827308867680633840277875 8740963301520950760416813)
    ·
      refine ⟨3277861238070356535156305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8740963301520950760416813 3277861238070356535156305)
      ·
        refine ⟨2458395928552767401367229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3277861238070356535156305 2458395928552767401367229)
        ·
          refine ⟨921898473207287775512711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2458395928552767401367229 921898473207287775512711)
          ·
            refine ⟨1382847709810931663269067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921898473207287775512711 1382847709810931663269067)
            ·
              refine ⟨2074271564716397494903601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382847709810931663269067 2074271564716397494903601)
              ·
                refine ⟨1555703673537298121177701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074271564716397494903601 1555703673537298121177701)
                ·
                  refine ⟨291694438788243397720819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555703673537298121177701 291694438788243397720819)
                  ·
                    rfl

theorem cell20_639082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_639082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639082 prefixEnd_639082 := by exact prefixLift 639082
  have htrace : WordTrace (prefixWord ++ tailWord_639082) baseStart_639082 baseEnd_639082 := by
    simpa [prefixWord, tailWord_639082, baseEnd_639082] using wordTrace_append hprefix tailTrace_639082
  have hstable : (prefixWord ++ tailWord_639082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639082).length < 2 ^ (prefixWord ++ tailWord_639082).sum := by decide
  have hdescent : baseEnd_639082 < baseStart_639082 := by decide
  rcases family_descends (prefixWord ++ tailWord_639082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639130 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_639130 : Nat := 118140960795 + 639130 * 2 ^ 59
def prefixEnd_639130 : Nat := 4983230072969 + 3 ^ 40 * 639130 * 2
def baseEnd_639130 : Nat := 291716347296168564120623

theorem tailTrace_639130 : CollatzResearch.WordTrace tailWord_639130 prefixEnd_639130 291716347296168564120623 := by
  unfold tailWord_639130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827746543637159889714711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15540657449699093039239229 5827746543637159889714711)
  ·
    refine ⟨8741619815455739834572067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827746543637159889714711 8741619815455739834572067)
    ·
      refine ⟨13112429723183609751858101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741619815455739834572067 13112429723183609751858101)
      ·
        refine ⟨1229290286548463414236697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13112429723183609751858101 1229290286548463414236697)
        ·
          refine ⟨921967714911347560677523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229290286548463414236697 921967714911347560677523)
          ·
            refine ⟨1382951572367021341016285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921967714911347560677523 1382951572367021341016285)
            ·
              refine ⟨518606839637633002881107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382951572367021341016285 518606839637633002881107)
              ·
                refine ⟨777910259456449504321661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518606839637633002881107 777910259456449504321661)
                ·
                  refine ⟨291716347296168564120623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777910259456449504321661 291716347296168564120623)
                  ·
                    rfl

theorem cell20_639130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_639130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639130 prefixEnd_639130 := by exact prefixLift 639130
  have htrace : WordTrace (prefixWord ++ tailWord_639130) baseStart_639130 baseEnd_639130 := by
    simpa [prefixWord, tailWord_639130, baseEnd_639130] using wordTrace_append hprefix tailTrace_639130
  have hstable : (prefixWord ++ tailWord_639130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639130).length < 2 ^ (prefixWord ++ tailWord_639130).sum := by decide
  have hdescent : baseEnd_639130 < baseStart_639130 := by decide
  rcases family_descends (prefixWord ++ tailWord_639130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639150 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_639150 : Nat := 118140960795 + 639150 * 2 ^ 59
def prefixEnd_639150 : Nat := 4983230072969 + 3 ^ 40 * 639150 * 2
def baseEnd_639150 : Nat := 291725475841137383453875

theorem tailTrace_639150 : CollatzResearch.WordTrace tailWord_639150 prefixEnd_639150 291725475841137383453875 := by
  unfold tailWord_639150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913964454309522871823363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15541143756317455316391269 2913964454309522871823363)
  ·
    refine ⟨4370946681464284307735045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913964454309522871823363 4370946681464284307735045)
    ·
      refine ⟨819552502774553307700321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4370946681464284307735045 819552502774553307700321)
      ·
        refine ⟨614664377080914980775241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819552502774553307700321 614664377080914980775241)
        ·
          refine ⟨460998282810686235581431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614664377080914980775241 460998282810686235581431)
          ·
            refine ⟨691497424216029353372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460998282810686235581431 691497424216029353372147)
            ·
              refine ⟨1037246136324044030058221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691497424216029353372147 1037246136324044030058221)
              ·
                refine ⟨388967301121516511271833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1037246136324044030058221 388967301121516511271833)
                ·
                  refine ⟨291725475841137383453875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388967301121516511271833 291725475841137383453875)
                  ·
                    rfl

theorem cell20_639150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_639150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639150 prefixEnd_639150 := by exact prefixLift 639150
  have htrace : WordTrace (prefixWord ++ tailWord_639150) baseStart_639150 baseEnd_639150 := by
    simpa [prefixWord, tailWord_639150, baseEnd_639150] using wordTrace_append hprefix tailTrace_639150
  have hstable : (prefixWord ++ tailWord_639150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639150).length < 2 ^ (prefixWord ++ tailWord_639150).sum := by decide
  have hdescent : baseEnd_639150 < baseStart_639150 := by decide
  rcases family_descends (prefixWord ++ tailWord_639150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639162 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_639162 : Nat := 118140960795 + 639162 * 2 ^ 59
def prefixEnd_639162 : Nat := 4983230072969 + 3 ^ 40 * 639162 * 2
def baseEnd_639162 : Nat := 291730952968118675053825

theorem tailTrace_639162 : CollatzResearch.WordTrace tailWord_639162 prefixEnd_639162 291730952968118675053825 := by
  unfold tailWord_639162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828038327608177256005935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15541435540288472682682493 5828038327608177256005935)
  ·
    refine ⟨8742057491412265884008903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5828038327608177256005935 8742057491412265884008903)
    ·
      refine ⟨13113086237118398826013355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742057491412265884008903 13113086237118398826013355)
      ·
        refine ⟨19669629355677598239020033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13113086237118398826013355 19669629355677598239020033)
        ·
          refine ⟨14752222016758198679265025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19669629355677598239020033 14752222016758198679265025)
          ·
            refine ⟨11064166512568649009448769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14752222016758198679265025 11064166512568649009448769)
            ·
              refine ⟨8298124884426486757086577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11064166512568649009448769 8298124884426486757086577)
              ·
                refine ⟨6223593663319865067814933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298124884426486757086577 6223593663319865067814933)
                ·
                  refine ⟨291730952968118675053825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6223593663319865067814933 291730952968118675053825)
                  ·
                    rfl

theorem cell20_639162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_639162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639162 prefixEnd_639162 := by exact prefixLift 639162
  have htrace : WordTrace (prefixWord ++ tailWord_639162) baseStart_639162 baseEnd_639162 := by
    simpa [prefixWord, tailWord_639162, baseEnd_639162] using wordTrace_append hprefix tailTrace_639162
  have hstable : (prefixWord ++ tailWord_639162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639162).length < 2 ^ (prefixWord ++ tailWord_639162).sum := by decide
  have hdescent : baseEnd_639162 < baseStart_639162 := by decide
  rcases family_descends (prefixWord ++ tailWord_639162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639172 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_639172 : Nat := 118140960795 + 639172 * 2 ^ 59
def prefixEnd_639172 : Nat := 4983230072969 + 3 ^ 40 * 639172 * 2
def baseEnd_639172 : Nat := 291735517240603084720451

theorem tailTrace_639172 : CollatzResearch.WordTrace tailWord_639172 prefixEnd_639172 291735517240603084720451 := by
  unfold tailWord_639172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656259020198240365943885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15541678693597653821258513 11656259020198240365943885)
  ·
    refine ⟨4371097132574340137228957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11656259020198240365943885 4371097132574340137228957)
    ·
      refine ⟨1639161424715377551460859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4371097132574340137228957 1639161424715377551460859)
      ·
        refine ⟨2458742137073066327191289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639161424715377551460859 2458742137073066327191289)
        ·
          refine ⟨1844056602804799745393467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458742137073066327191289 1844056602804799745393467)
          ·
            refine ⟨2766084904207199618090201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844056602804799745393467 2766084904207199618090201)
            ·
              refine ⟨2074563678155399713567651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766084904207199618090201 2074563678155399713567651)
              ·
                refine ⟨3111845517233099570351477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074563678155399713567651 3111845517233099570351477)
                ·
                  refine ⟨291735517240603084720451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3111845517233099570351477 291735517240603084720451)
                  ·
                    rfl

theorem cell20_639172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_639172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639172 prefixEnd_639172 := by exact prefixLift 639172
  have htrace : WordTrace (prefixWord ++ tailWord_639172) baseStart_639172 baseEnd_639172 := by
    simpa [prefixWord, tailWord_639172, baseEnd_639172] using wordTrace_append hprefix tailTrace_639172
  have hstable : (prefixWord ++ tailWord_639172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639172).length < 2 ^ (prefixWord ++ tailWord_639172).sum := by decide
  have hdescent : baseEnd_639172 < baseStart_639172 := by decide
  rcases family_descends (prefixWord ++ tailWord_639172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639186 : List Nat := [3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_639186 : Nat := 118140960795 + 639186 * 2 ^ 59
def prefixEnd_639186 : Nat := 4983230072969 + 3 ^ 40 * 639186 * 2
def baseEnd_639186 : Nat := 97247302407360419417909

theorem tailTrace_639186 : CollatzResearch.WordTrace tailWord_639186 prefixEnd_639186 97247302407360419417909 := by
  unfold tailWord_639186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828257165586440280724353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15542019108230507415264941 5828257165586440280724353)
  ·
    refine ⟨4371192874189830210543265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5828257165586440280724353 4371192874189830210543265)
    ·
      refine ⟨3278394655642372657907449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4371192874189830210543265 3278394655642372657907449)
      ·
        refine ⟨2458795991731779493430587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3278394655642372657907449 2458795991731779493430587)
        ·
          refine ⟨3688193987597669240145881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458795991731779493430587 3688193987597669240145881)
          ·
            refine ⟨2766145490698251930109411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688193987597669240145881 2766145490698251930109411)
            ·
              refine ⟨4149218236047377895164117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766145490698251930109411 4149218236047377895164117)
              ·
                refine ⟨97247302407360419417909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4149218236047377895164117 97247302407360419417909)
                ·
                  rfl

theorem cell20_639186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_639186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639186 prefixEnd_639186 := by exact prefixLift 639186
  have htrace : WordTrace (prefixWord ++ tailWord_639186) baseStart_639186 baseEnd_639186 := by
    simpa [prefixWord, tailWord_639186, baseEnd_639186] using wordTrace_append hprefix tailTrace_639186
  have hstable : (prefixWord ++ tailWord_639186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639186).length < 2 ^ (prefixWord ++ tailWord_639186).sum := by decide
  have hdescent : baseEnd_639186 < baseStart_639186 := by decide
  rcases family_descends (prefixWord ++ tailWord_639186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639189 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_639189 : Nat := 118140960795 + 639189 * 2 ^ 59
def prefixEnd_639189 : Nat := 4983230072969 + 3 ^ 40 * 639189 * 2
def baseEnd_639189 : Nat := 291743276503826581153715

theorem tailTrace_639189 : CollatzResearch.WordTrace tailWord_639189 prefixEnd_639189 291743276503826581153715 := by
  unfold tailWord_639189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313138081334892635256621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15542092054223261756837747 23313138081334892635256621)
  ·
    refine ⟨8742426780500584738221233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23313138081334892635256621 8742426780500584738221233)
    ·
      refine ⟨6556820085375438553665925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8742426780500584738221233 6556820085375438553665925)
      ·
        refine ⟨1229403766007894728812361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6556820085375438553665925 1229403766007894728812361)
        ·
          refine ⟨922052824505921046609271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229403766007894728812361 922052824505921046609271)
          ·
            refine ⟨1383079236758881569913907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922052824505921046609271 1383079236758881569913907)
            ·
              refine ⟨2074618855138322354870861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383079236758881569913907 2074618855138322354870861)
              ·
                refine ⟨777982070676870883076573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074618855138322354870861 777982070676870883076573)
                ·
                  refine ⟨291743276503826581153715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777982070676870883076573 291743276503826581153715)
                  ·
                    rfl

theorem cell20_639189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_639189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639189 prefixEnd_639189 := by exact prefixLift 639189
  have htrace : WordTrace (prefixWord ++ tailWord_639189) baseStart_639189 baseEnd_639189 := by
    simpa [prefixWord, tailWord_639189, baseEnd_639189] using wordTrace_append hprefix tailTrace_639189
  have hstable : (prefixWord ++ tailWord_639189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639189).length < 2 ^ (prefixWord ++ tailWord_639189).sum := by decide
  have hdescent : baseEnd_639189 < baseStart_639189 := by decide
  rcases family_descends (prefixWord ++ tailWord_639189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639200 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_639200 : Nat := 118140960795 + 639200 * 2 ^ 59
def prefixEnd_639200 : Nat := 4983230072969 + 3 ^ 40 * 639200 * 2
def baseEnd_639200 : Nat := 291748297203559431787003

theorem tailTrace_639200 : CollatzResearch.WordTrace tailWord_639200 prefixEnd_639200 291748297203559431787003 := by
  unfold tailWord_639200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656769642147520756953527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15542359522863361009271369 11656769642147520756953527)
  ·
    refine ⟨17485154463221281135430291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11656769642147520756953527 17485154463221281135430291)
    ·
      refine ⟨26227731694831921703145437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17485154463221281135430291 26227731694831921703145437)
      ·
        refine ⟨9835399385561970638679539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26227731694831921703145437 9835399385561970638679539)
        ·
          refine ⟨14753099078342955958019309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835399385561970638679539 14753099078342955958019309)
          ·
            refine ⟨5532412154378608484257241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14753099078342955958019309 5532412154378608484257241)
            ·
              refine ⟨4149309115783956363192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532412154378608484257241 4149309115783956363192931)
              ·
                refine ⟨6223963673675934544789397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149309115783956363192931 6223963673675934544789397)
                ·
                  refine ⟨291748297203559431787003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6223963673675934544789397 291748297203559431787003)
                  ·
                    rfl

theorem cell20_639200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_639200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639200 prefixEnd_639200 := by exact prefixLift 639200
  have htrace : WordTrace (prefixWord ++ tailWord_639200) baseStart_639200 baseEnd_639200 := by
    simpa [prefixWord, tailWord_639200, baseEnd_639200] using wordTrace_append hprefix tailTrace_639200
  have hstable : (prefixWord ++ tailWord_639200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639200).length < 2 ^ (prefixWord ++ tailWord_639200).sum := by decide
  have hdescent : baseEnd_639200 < baseStart_639200 := by decide
  rcases family_descends (prefixWord ++ tailWord_639200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639255 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_639255 : Nat := 118140960795 + 639255 * 2 ^ 59
def prefixEnd_639255 : Nat := 4983230072969 + 3 ^ 40 * 639255 * 2
def baseEnd_639255 : Nat := 291773400702223684953445

theorem tailTrace_639255 : CollatzResearch.WordTrace tailWord_639255 prefixEnd_639255 291773400702223684953445 := by
  unfold tailWord_639255
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315545299095785907159219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15543696866063857271439479 23315545299095785907159219)
  ·
    refine ⟨34973317948643678860738829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23315545299095785907159219 34973317948643678860738829)
    ·
      refine ⟨13114994230741379572777061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34973317948643678860738829 13114994230741379572777061)
      ·
        refine ⟨2459061418264008669895699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13114994230741379572777061 2459061418264008669895699)
        ·
          refine ⟨3688592127396013004843549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459061418264008669895699 3688592127396013004843549)
          ·
            refine ⟨1383222047773504876816331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3688592127396013004843549 1383222047773504876816331)
            ·
              refine ⟨2074833071660257315224497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383222047773504876816331 2074833071660257315224497)
              ·
                refine ⟨1556124803745192986418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074833071660257315224497 1556124803745192986418373)
                ·
                  refine ⟨291773400702223684953445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556124803745192986418373 291773400702223684953445)
                  ·
                    rfl

theorem cell20_639255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_639255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639255 prefixEnd_639255 := by exact prefixLift 639255
  have htrace : WordTrace (prefixWord ++ tailWord_639255) baseStart_639255 baseEnd_639255 := by
    simpa [prefixWord, tailWord_639255, baseEnd_639255] using wordTrace_append hprefix tailTrace_639255
  have hstable : (prefixWord ++ tailWord_639255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639255).length < 2 ^ (prefixWord ++ tailWord_639255).sum := by decide
  have hdescent : baseEnd_639255 < baseStart_639255 := by decide
  rcases family_descends (prefixWord ++ tailWord_639255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639282 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_639282 : Nat := 118140960795 + 639282 * 2 ^ 59
def prefixEnd_639282 : Nat := 4983230072969 + 3 ^ 40 * 639282 * 2
def baseEnd_639282 : Nat := 291785724237931591053335

theorem tailTrace_639282 : CollatzResearch.WordTrace tailWord_639282 prefixEnd_639282 291785724237931591053335 := by
  unfold tailWord_639282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829132517499492379598025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15544353379998646345594733 5829132517499492379598025)
  ·
    refine ⟨4371849388124619284698519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5829132517499492379598025 4371849388124619284698519)
    ·
      refine ⟨6557774082186928927047779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371849388124619284698519 6557774082186928927047779)
      ·
        refine ⟨9836661123280393390571669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557774082186928927047779 9836661123280393390571669)
        ·
          refine ⟨461093490153768440183047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9836661123280393390571669 461093490153768440183047)
          ·
            refine ⟨691640235230652660274571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461093490153768440183047 691640235230652660274571)
            ·
              refine ⟨1037460352845978990411857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691640235230652660274571 1037460352845978990411857)
              ·
                refine ⟨778095264634484242808893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037460352845978990411857 778095264634484242808893)
                ·
                  refine ⟨291785724237931591053335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778095264634484242808893 291785724237931591053335)
                  ·
                    rfl

theorem cell20_639282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_639282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639282 prefixEnd_639282 := by exact prefixLift 639282
  have htrace : WordTrace (prefixWord ++ tailWord_639282) baseStart_639282 baseEnd_639282 := by
    simpa [prefixWord, tailWord_639282, baseEnd_639282] using wordTrace_append hprefix tailTrace_639282
  have hstable : (prefixWord ++ tailWord_639282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639282).length < 2 ^ (prefixWord ++ tailWord_639282).sum := by decide
  have hdescent : baseEnd_639282 < baseStart_639282 := by decide
  rcases family_descends (prefixWord ++ tailWord_639282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639283 : List Nat := [1, 1, 1, 2, 5, 1, 9]
def baseStart_639283 : Nat := 118140960795 + 639283 * 2 ^ 59
def prefixEnd_639283 : Nat := 4983230072969 + 3 ^ 40 * 639283 * 2
def baseEnd_639283 : Nat := 32420686740575559113333

theorem tailTrace_639283 : CollatzResearch.WordTrace tailWord_639283 prefixEnd_639283 32420686740575559113333 := by
  unfold tailWord_639283
  simp only [CollatzResearch.WordTrace]
  refine ⟨23316566542994346689178503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15544377695329564459452335 23316566542994346689178503)
  ·
    refine ⟨34974849814491520033767755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23316566542994346689178503 34974849814491520033767755)
    ·
      refine ⟨52462274721737280050651633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34974849814491520033767755 52462274721737280050651633)
      ·
        refine ⟨39346706041302960037988725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52462274721737280050651633 39346706041302960037988725)
        ·
          refine ⟨3688753691372152503561443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39346706041302960037988725 3688753691372152503561443)
          ·
            refine ⟨5533130537058228755342165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688753691372152503561443 5533130537058228755342165)
            ·
              refine ⟨32420686740575559113333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5533130537058228755342165 32420686740575559113333)
              ·
                rfl

theorem cell20_639283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_639283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639283 prefixEnd_639283 := by exact prefixLift 639283
  have htrace : WordTrace (prefixWord ++ tailWord_639283) baseStart_639283 baseEnd_639283 := by
    simpa [prefixWord, tailWord_639283, baseEnd_639283] using wordTrace_append hprefix tailTrace_639283
  have hstable : (prefixWord ++ tailWord_639283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639283).length < 2 ^ (prefixWord ++ tailWord_639283).sum := by decide
  have hdescent : baseEnd_639283 < baseStart_639283 := by decide
  rcases family_descends (prefixWord ++ tailWord_639283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639338 : List Nat := [3, 1, 3, 3, 1, 1, 8]
def baseStart_639338 : Nat := 118140960795 + 639338 * 2 ^ 59
def prefixEnd_639338 : Nat := 4983230072969 + 3 ^ 40 * 639338 * 2
def baseEnd_639338 : Nat := 32423476018204920576271

theorem tailTrace_639338 : CollatzResearch.WordTrace tailWord_639338 prefixEnd_639338 32423476018204920576271 := by
  unfold tailWord_639338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829643139448772770607667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15545715038530060721620445 5829643139448772770607667)
  ·
    refine ⟨8744464709173159155911501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5829643139448772770607667 8744464709173159155911501)
    ·
      refine ⟨3279174265939934683466813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8744464709173159155911501 3279174265939934683466813)
      ·
        refine ⟨1229690349727475506300055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3279174265939934683466813 1229690349727475506300055)
        ·
          refine ⟨1844535524591213259450083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229690349727475506300055 1844535524591213259450083)
          ·
            refine ⟨2766803286886819889175125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844535524591213259450083 2766803286886819889175125)
            ·
              refine ⟨32423476018204920576271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2766803286886819889175125 32423476018204920576271)
              ·
                rfl

theorem cell20_639338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_639338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639338 prefixEnd_639338 := by exact prefixLift 639338
  have htrace : WordTrace (prefixWord ++ tailWord_639338) baseStart_639338 baseEnd_639338 := by
    simpa [prefixWord, tailWord_639338, baseEnd_639338] using wordTrace_append hprefix tailTrace_639338
  have hstable : (prefixWord ++ tailWord_639338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639338).length < 2 ^ (prefixWord ++ tailWord_639338).sum := by decide
  have hdescent : baseEnd_639338 < baseStart_639338 := by decide
  rcases family_descends (prefixWord ++ tailWord_639338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639345 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_639345 : Nat := 118140960795 + 639345 * 2 ^ 59
def prefixEnd_639345 : Nat := 4983230072969 + 3 ^ 40 * 639345 * 2
def baseEnd_639345 : Nat := 291814479154583371953077

theorem tailTrace_639345 : CollatzResearch.WordTrace tailWord_639345 prefixEnd_639345 291814479154583371953077 := by
  unfold tailWord_639345
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318827868769731277935489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15545885245846487518623659 23318827868769731277935489)
  ·
    refine ⟨17489120901577298458451617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23318827868769731277935489 17489120901577298458451617)
    ·
      refine ⟨13116840676182973843838713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17489120901577298458451617 13116840676182973843838713)
      ·
        refine ⟨9837630507137230382879035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13116840676182973843838713 9837630507137230382879035)
        ·
          refine ⟨14756445760705845574318553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9837630507137230382879035 14756445760705845574318553)
          ·
            refine ⟨11067334320529384180738915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14756445760705845574318553 11067334320529384180738915)
            ·
              refine ⟨16601001480794076271108373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11067334320529384180738915 16601001480794076271108373)
              ·
                refine ⟨778171944412222325208205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16601001480794076271108373 778171944412222325208205)
                ·
                  refine ⟨291814479154583371953077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778171944412222325208205 291814479154583371953077)
                  ·
                    rfl

theorem cell20_639345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_639345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639345 prefixEnd_639345 := by exact prefixLift 639345
  have htrace : WordTrace (prefixWord ++ tailWord_639345) baseStart_639345 baseEnd_639345 := by
    simpa [prefixWord, tailWord_639345, baseEnd_639345] using wordTrace_append hprefix tailTrace_639345
  have hstable : (prefixWord ++ tailWord_639345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639345).length < 2 ^ (prefixWord ++ tailWord_639345).sum := by decide
  have hdescent : baseEnd_639345 < baseStart_639345 := by decide
  rcases family_descends (prefixWord ++ tailWord_639345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639393 : List Nat := [1, 2, 3, 5, 2, 7]
def baseStart_639393 : Nat := 118140960795 + 639393 * 2 ^ 59
def prefixEnd_639393 : Nat := 4983230072969 + 3 ^ 40 * 639393 * 2
def baseEnd_639393 : Nat := 10808755098611427346403

theorem tailTrace_639393 : CollatzResearch.WordTrace tailWord_639393 prefixEnd_639393 10808755098611427346403 := by
  unfold tailWord_639393
  simp only [CollatzResearch.WordTrace]
  refine ⟨23320578572595835475682833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15547052381730556983788555 23320578572595835475682833)
  ·
    refine ⟨17490433929446876606762125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23320578572595835475682833 17490433929446876606762125)
    ·
      refine ⟨6558912723542578727535797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17490433929446876606762125 6558912723542578727535797)
      ·
        refine ⟨614898067832116755706481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6558912723542578727535797 614898067832116755706481)
        ·
          refine ⟨461173550874087566779861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614898067832116755706481 461173550874087566779861)
          ·
            refine ⟨10808755098611427346403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 461173550874087566779861 10808755098611427346403)
            ·
              rfl

theorem cell20_639393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 7].length) (baseStart_639393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639393 prefixEnd_639393 := by exact prefixLift 639393
  have htrace : WordTrace (prefixWord ++ tailWord_639393) baseStart_639393 baseEnd_639393 := by
    simpa [prefixWord, tailWord_639393, baseEnd_639393] using wordTrace_append hprefix tailTrace_639393
  have hstable : (prefixWord ++ tailWord_639393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639393).length < 2 ^ (prefixWord ++ tailWord_639393).sum := by decide
  have hdescent : baseEnd_639393 < baseStart_639393 := by decide
  rcases family_descends (prefixWord ++ tailWord_639393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639473 : List Nat := [1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_639473 : Nat := 118140960795 + 639473 * 2 ^ 59
def prefixEnd_639473 : Nat := 4983230072969 + 3 ^ 40 * 639473 * 2
def baseEnd_639473 : Nat := 97290967280794605228629

theorem tailTrace_639473 : CollatzResearch.WordTrace tailWord_639473 prefixEnd_639473 97290967280794605228629 := by
  unfold tailWord_639473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23323496412306009138595073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15548997608204006092396715 23323496412306009138595073)
  ·
    refine ⟨17492622309229506853946305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23323496412306009138595073 17492622309229506853946305)
    ·
      refine ⟨13119466731922130140459729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17492622309229506853946305 13119466731922130140459729)
      ·
        refine ⟨9839600048941597605344797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13119466731922130140459729 9839600048941597605344797)
        ·
          refine ⟨3689850018353099102004299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9839600048941597605344797 3689850018353099102004299)
          ·
            refine ⟨5534775027529648653006449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689850018353099102004299 5534775027529648653006449)
            ·
              refine ⟨4151081270647236489754837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534775027529648653006449 4151081270647236489754837)
              ·
                refine ⟨97290967280794605228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4151081270647236489754837 97290967280794605228629)
                ·
                  rfl

theorem cell20_639473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_639473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639473 prefixEnd_639473 := by exact prefixLift 639473
  have htrace : WordTrace (prefixWord ++ tailWord_639473) baseStart_639473 baseEnd_639473 := by
    simpa [prefixWord, tailWord_639473, baseEnd_639473] using wordTrace_append hprefix tailTrace_639473
  have hstable : (prefixWord ++ tailWord_639473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639473).length < 2 ^ (prefixWord ++ tailWord_639473).sum := by decide
  have hdescent : baseEnd_639473 < baseStart_639473 := by decide
  rcases family_descends (prefixWord ++ tailWord_639473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639500 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_639500 : Nat := 118140960795 + 639500 * 2 ^ 59
def prefixEnd_639500 : Nat := 4983230072969 + 3 ^ 40 * 639500 * 2
def baseEnd_639500 : Nat := 291885225378091721785777

theorem tailTrace_639500 : CollatzResearch.WordTrace tailWord_639500 prefixEnd_639500 291885225378091721785777 := by
  unfold tailWord_639500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662240591604096374913977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15549654122138795166551969 11662240591604096374913977)
  ·
    refine ⟨8746680443703072281185483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11662240591604096374913977 8746680443703072281185483)
    ·
      refine ⟨13120020665554608421778225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746680443703072281185483 13120020665554608421778225)
      ·
        refine ⟨9840015499165956316333669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13120020665554608421778225 9840015499165956316333669)
        ·
          refine ⟨1845002906093616809312563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9840015499165956316333669 1845002906093616809312563)
          ·
            refine ⟨2767504359140425213968845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845002906093616809312563 2767504359140425213968845)
            ·
              refine ⟨1037814134677659455238317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2767504359140425213968845 1037814134677659455238317)
              ·
                refine ⟨389180300504122295714369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1037814134677659455238317 389180300504122295714369)
                ·
                  refine ⟨291885225378091721785777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389180300504122295714369 291885225378091721785777)
                  ·
                    rfl

theorem cell20_639500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_639500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639500 prefixEnd_639500 := by exact prefixLift 639500
  have htrace : WordTrace (prefixWord ++ tailWord_639500) baseStart_639500 baseEnd_639500 := by
    simpa [prefixWord, tailWord_639500, baseEnd_639500] using wordTrace_append hprefix tailTrace_639500
  have hstable : (prefixWord ++ tailWord_639500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639500).length < 2 ^ (prefixWord ++ tailWord_639500).sum := by decide
  have hdescent : baseEnd_639500 < baseStart_639500 := by decide
  rcases family_descends (prefixWord ++ tailWord_639500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639517 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 2]
def baseStart_639517 : Nat := 118140960795 + 639517 * 2 ^ 59
def prefixEnd_639517 : Nat := 4983230072969 + 3 ^ 40 * 639517 * 2
def baseEnd_639517 : Nat := 291892984641315218219041

theorem tailTrace_639517 : CollatzResearch.WordTrace tailWord_639517 prefixEnd_639517 291892984641315218219041 := by
  unfold tailWord_639517
  simp only [CollatzResearch.WordTrace]
  refine ⟨23325101224146604653196805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15550067482764403102131203 23325101224146604653196805)
  ·
    refine ⟨4373456479527488372474401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23325101224146604653196805 4373456479527488372474401)
    ·
      refine ⟨3280092359645616279355801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4373456479527488372474401 3280092359645616279355801)
      ·
        refine ⟨2460069269734212209516851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3280092359645616279355801 2460069269734212209516851)
        ·
          refine ⟨3690103904601318314275277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460069269734212209516851 3690103904601318314275277)
          ·
            refine ⟨1383788964225494367853229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3690103904601318314275277 1383788964225494367853229)
            ·
              refine ⟨518920861584560387944961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383788964225494367853229 518920861584560387944961)
              ·
                refine ⟨389190646188420290958721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518920861584560387944961 389190646188420290958721)
                ·
                  refine ⟨291892984641315218219041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389190646188420290958721 291892984641315218219041)
                  ·
                    rfl

theorem cell20_639517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_639517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639517 prefixEnd_639517 := by exact prefixLift 639517
  have htrace : WordTrace (prefixWord ++ tailWord_639517) baseStart_639517 baseEnd_639517 := by
    simpa [prefixWord, tailWord_639517, baseEnd_639517] using wordTrace_append hprefix tailTrace_639517
  have hstable : (prefixWord ++ tailWord_639517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639517).length < 2 ^ (prefixWord ++ tailWord_639517).sum := by decide
  have hdescent : baseEnd_639517 < baseStart_639517 := by decide
  rcases family_descends (prefixWord ++ tailWord_639517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639527 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_639527 : Nat := 118140960795 + 639527 * 2 ^ 59
def prefixEnd_639527 : Nat := 4983230072969 + 3 ^ 40 * 639527 * 2
def baseEnd_639527 : Nat := 291897548913799627885667

theorem tailTrace_639527 : CollatzResearch.WordTrace tailWord_639527 prefixEnd_639527 291897548913799627885667 := by
  unfold tailWord_639527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23325465954110376361060835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15550310636073584240707223 23325465954110376361060835)
  ·
    refine ⟨34988198931165564541591253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23325465954110376361060835 34988198931165564541591253)
    ·
      refine ⟨820035912449192918943545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34988198931165564541591253 820035912449192918943545)
      ·
        refine ⟨615026934336894689207659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 820035912449192918943545 615026934336894689207659)
        ·
          refine ⟨922540401505342033811489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615026934336894689207659 922540401505342033811489)
          ·
            refine ⟨691905301129006525358617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922540401505342033811489 691905301129006525358617)
            ·
              refine ⟨518928975846754894018963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691905301129006525358617 518928975846754894018963)
              ·
                refine ⟨778393463770132341028445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518928975846754894018963 778393463770132341028445)
                ·
                  refine ⟨291897548913799627885667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778393463770132341028445 291897548913799627885667)
                  ·
                    rfl

theorem cell20_639527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_639527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639527 prefixEnd_639527 := by exact prefixLift 639527
  have htrace : WordTrace (prefixWord ++ tailWord_639527) baseStart_639527 baseEnd_639527 := by
    simpa [prefixWord, tailWord_639527, baseEnd_639527] using wordTrace_append hprefix tailTrace_639527
  have hstable : (prefixWord ++ tailWord_639527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639527).length < 2 ^ (prefixWord ++ tailWord_639527).sum := by decide
  have hdescent : baseEnd_639527 < baseStart_639527 := by decide
  rcases family_descends (prefixWord ++ tailWord_639527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639528 : List Nat := [2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_639528 : Nat := 118140960795 + 639528 * 2 ^ 59
def prefixEnd_639528 : Nat := 4983230072969 + 3 ^ 40 * 639528 * 2
def baseEnd_639528 : Nat := 97299335113682689617443

theorem tailTrace_639528 : CollatzResearch.WordTrace tailWord_639528 prefixEnd_639528 97299335113682689617443 := by
  unfold tailWord_639528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662751213553376765923619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15550334951404502354564825 11662751213553376765923619)
  ·
    refine ⟨17494126820330065148885429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11662751213553376765923619 17494126820330065148885429)
    ·
      refine ⟨1640074389405943607708009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17494126820330065148885429 1640074389405943607708009)
      ·
        refine ⟨1230055792054457705781007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640074389405943607708009 1230055792054457705781007)
        ·
          refine ⟨1845083688081686558671511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230055792054457705781007 1845083688081686558671511)
          ·
            refine ⟨2767625532122529838007267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845083688081686558671511 2767625532122529838007267)
            ·
              refine ⟨4151438298183794757010901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767625532122529838007267 4151438298183794757010901)
              ·
                refine ⟨97299335113682689617443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4151438298183794757010901 97299335113682689617443)
                ·
                  rfl

theorem cell20_639528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_639528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639528 prefixEnd_639528 := by exact prefixLift 639528
  have htrace : WordTrace (prefixWord ++ tailWord_639528) baseStart_639528 baseEnd_639528 := by
    simpa [prefixWord, tailWord_639528, baseEnd_639528] using wordTrace_append hprefix tailTrace_639528
  have hstable : (prefixWord ++ tailWord_639528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639528).length < 2 ^ (prefixWord ++ tailWord_639528).sum := by decide
  have hdescent : baseEnd_639528 < baseStart_639528 := by decide
  rcases family_descends (prefixWord ++ tailWord_639528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639573 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_639573 : Nat := 118140960795 + 639573 * 2 ^ 59
def prefixEnd_639573 : Nat := 4983230072969 + 3 ^ 40 * 639573 * 2
def baseEnd_639573 : Nat := 291918544567227912352145

theorem tailTrace_639573 : CollatzResearch.WordTrace tailWord_639573 prefixEnd_639573 291918544567227912352145 := by
  unfold tailWord_639573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23327143711943726217235373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15551429141295817478156915 23327143711943726217235373)
  ·
    refine ⟨8747678891978897331463265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23327143711943726217235373 8747678891978897331463265)
    ·
      refine ⟨6560759168984172998597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8747678891978897331463265 6560759168984172998597449)
      ·
        refine ⟨4920569376738129748948087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6560759168984172998597449 4920569376738129748948087)
        ·
          refine ⟨7380854065107194623422131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4920569376738129748948087 7380854065107194623422131)
          ·
            refine ⟨11071281097660791935133197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7380854065107194623422131 11071281097660791935133197)
            ·
              refine ⟨4151730411622796975674949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11071281097660791935133197 4151730411622796975674949)
              ·
                refine ⟨778449452179274432939053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4151730411622796975674949 778449452179274432939053)
                ·
                  refine ⟨291918544567227912352145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778449452179274432939053 291918544567227912352145)
                  ·
                    rfl

theorem cell20_639573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_639573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639573 prefixEnd_639573 := by exact prefixLift 639573
  have htrace : WordTrace (prefixWord ++ tailWord_639573) baseStart_639573 baseEnd_639573 := by
    simpa [prefixWord, tailWord_639573, baseEnd_639573] using wordTrace_append hprefix tailTrace_639573
  have hstable : (prefixWord ++ tailWord_639573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639573).length < 2 ^ (prefixWord ++ tailWord_639573).sum := by decide
  have hdescent : baseEnd_639573 < baseStart_639573 := by decide
  rcases family_descends (prefixWord ++ tailWord_639573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639576 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_639576 : Nat := 118140960795 + 639576 * 2 ^ 59
def prefixEnd_639576 : Nat := 4983230072969 + 3 ^ 40 * 639576 * 2
def baseEnd_639576 : Nat := 291919913848973235252133

theorem tailTrace_639576 : CollatzResearch.WordTrace tailWord_639576 prefixEnd_639576 291919913848973235252133 := by
  unfold tailWord_639576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11663626565466428864797291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15551502087288571819729721 11663626565466428864797291)
  ·
    refine ⟨17495439848199643297195937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11663626565466428864797291 17495439848199643297195937)
    ·
      refine ⟨13121579886149732472896953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17495439848199643297195937 13121579886149732472896953)
      ·
        refine ⟨9841184914612299354672715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13121579886149732472896953 9841184914612299354672715)
        ·
          refine ⟨14761777371918449032009073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841184914612299354672715 14761777371918449032009073)
          ·
            refine ⟨11071333028938836774006805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14761777371918449032009073 11071333028938836774006805)
            ·
              refine ⟨518968735731507973781569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11071333028938836774006805 518968735731507973781569)
              ·
                refine ⟨389226551798630980336177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518968735731507973781569 389226551798630980336177)
                ·
                  refine ⟨291919913848973235252133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389226551798630980336177 291919913848973235252133)
                  ·
                    rfl

theorem cell20_639576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_639576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639576 prefixEnd_639576 := by exact prefixLift 639576
  have htrace : WordTrace (prefixWord ++ tailWord_639576) baseStart_639576 baseEnd_639576 := by
    simpa [prefixWord, tailWord_639576, baseEnd_639576] using wordTrace_append hprefix tailTrace_639576
  have hstable : (prefixWord ++ tailWord_639576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639576).length < 2 ^ (prefixWord ++ tailWord_639576).sum := by decide
  have hdescent : baseEnd_639576 < baseStart_639576 := by decide
  rcases family_descends (prefixWord ++ tailWord_639576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639597 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_639597 : Nat := 118140960795 + 639597 * 2 ^ 59
def prefixEnd_639597 : Nat := 4983230072969 + 3 ^ 40 * 639597 * 2
def baseEnd_639597 : Nat := 291929498821190495552047

theorem tailTrace_639597 : CollatzResearch.WordTrace tailWord_639597 prefixEnd_639597 291929498821190495552047 := by
  unfold tailWord_639597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23328019063856778316109045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15552012709237852210739363 23328019063856778316109045)
  ·
    refine ⟨2187001787236572967135223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23328019063856778316109045 2187001787236572967135223)
    ·
      refine ⟨3280502680854859450702835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187001787236572967135223 3280502680854859450702835)
      ·
        refine ⟨4920754021282289176054253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280502680854859450702835 4920754021282289176054253)
        ·
          refine ⟨1845282757980858441020345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4920754021282289176054253 1845282757980858441020345)
          ·
            refine ⟨1383962068485643830765259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845282757980858441020345 1383962068485643830765259)
            ·
              refine ⟨2075943102728465746147889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383962068485643830765259 2075943102728465746147889)
              ·
                refine ⟨1556957327046349309610917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075943102728465746147889 1556957327046349309610917)
                ·
                  refine ⟨291929498821190495552047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1556957327046349309610917 291929498821190495552047)
                  ·
                    rfl

theorem cell20_639597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_639597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639597 prefixEnd_639597 := by exact prefixLift 639597
  have htrace : WordTrace (prefixWord ++ tailWord_639597) baseStart_639597 baseEnd_639597 := by
    simpa [prefixWord, tailWord_639597, baseEnd_639597] using wordTrace_append hprefix tailTrace_639597
  have hstable : (prefixWord ++ tailWord_639597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639597).length < 2 ^ (prefixWord ++ tailWord_639597).sum := by decide
  have hdescent : baseEnd_639597 < baseStart_639597 := by decide
  rcases family_descends (prefixWord ++ tailWord_639597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639655 : List Nat := [1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_639655 : Nat := 118140960795 + 639655 * 2 ^ 59
def prefixEnd_639655 : Nat := 4983230072969 + 3 ^ 40 * 639655 * 2
def baseEnd_639655 : Nat := 97318657200533357206159

theorem tailTrace_639655 : CollatzResearch.WordTrace tailWord_639655 prefixEnd_639655 97318657200533357206159 := by
  unfold tailWord_639655
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330134497646654221720419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553422998431102814480279 23330134497646654221720419)
  ·
    refine ⟨34995201746469981332580629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23330134497646654221720419 34995201746469981332580629)
    ·
      refine ⟨1640400081865780374964717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34995201746469981332580629 1640400081865780374964717)
      ·
        refine ⟨615150030699667640611769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1640400081865780374964717 615150030699667640611769)
        ·
          refine ⟨461362523024750730458827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615150030699667640611769 461362523024750730458827)
          ·
            refine ⟨692043784537126095688241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461362523024750730458827 692043784537126095688241)
            ·
              refine ⟨519032838402844571766181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692043784537126095688241 519032838402844571766181)
              ·
                refine ⟨97318657200533357206159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519032838402844571766181 97318657200533357206159)
                ·
                  rfl

theorem cell20_639655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_639655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639655 prefixEnd_639655 := by exact prefixLift 639655
  have htrace : WordTrace (prefixWord ++ tailWord_639655) baseStart_639655 baseEnd_639655 := by
    simpa [prefixWord, tailWord_639655, baseEnd_639655] using wordTrace_append hprefix tailTrace_639655
  have hstable : (prefixWord ++ tailWord_639655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639655).length < 2 ^ (prefixWord ++ tailWord_639655).sum := by decide
  have hdescent : baseEnd_639655 < baseStart_639655 := by decide
  rcases family_descends (prefixWord ++ tailWord_639655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639663 : List Nat := [1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_639663 : Nat := 118140960795 + 639663 * 2 ^ 59
def prefixEnd_639663 : Nat := 4983230072969 + 3 ^ 40 * 639663 * 2
def baseEnd_639663 : Nat := 97319874339862533117259

theorem tailTrace_639663 : CollatzResearch.WordTrace tailWord_639663 prefixEnd_639663 97319874339862533117259 := by
  unfold tailWord_639663
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330426281617671588011643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553617521078447725341095 23330426281617671588011643)
  ·
    refine ⟨34995639422426507382017465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23330426281617671588011643 34995639422426507382017465)
    ·
      refine ⟨26246729566819880536513099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34995639422426507382017465 26246729566819880536513099)
      ·
        refine ⟨39370094350229820804769649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26246729566819880536513099 39370094350229820804769649)
        ·
          refine ⟨29527570762672365603577237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39370094350229820804769649 29527570762672365603577237)
          ·
            refine ⟨1384104879500267137667683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29527570762672365603577237 1384104879500267137667683)
            ·
              refine ⟨2076157319250400706501525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384104879500267137667683 2076157319250400706501525)
              ·
                refine ⟨97319874339862533117259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2076157319250400706501525 97319874339862533117259)
                ·
                  rfl

theorem cell20_639663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_639663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639663 prefixEnd_639663 := by exact prefixLift 639663
  have htrace : WordTrace (prefixWord ++ tailWord_639663) baseStart_639663 baseEnd_639663 := by
    simpa [prefixWord, tailWord_639663, baseEnd_639663] using wordTrace_append hprefix tailTrace_639663
  have hstable : (prefixWord ++ tailWord_639663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639663).length < 2 ^ (prefixWord ++ tailWord_639663).sum := by decide
  have hdescent : baseEnd_639663 < baseStart_639663 := by decide
  rcases family_descends (prefixWord ++ tailWord_639663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639669 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 2]
def baseStart_639669 : Nat := 118140960795 + 639669 * 2 ^ 59
def prefixEnd_639669 : Nat := 4983230072969 + 3 ^ 40 * 639669 * 2
def baseEnd_639669 : Nat := 291962361583078245151753

theorem tailTrace_639669 : CollatzResearch.WordTrace tailWord_639669 prefixEnd_639669 291962361583078245151753 := by
  unfold tailWord_639669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330645119595934612730061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553763413063956408486707 23330645119595934612730061)
  ·
    refine ⟨8748991919848475479773773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23330645119595934612730061 8748991919848475479773773)
    ·
      refine ⟨3280871969943178304915165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8748991919848475479773773 3280871969943178304915165)
      ·
        refine ⟨1230326988728691864343187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3280871969943178304915165 1230326988728691864343187)
        ·
          refine ⟨1845490483093037796514781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230326988728691864343187 1845490483093037796514781)
          ·
            refine ⟨692058931159889173693043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1845490483093037796514781 692058931159889173693043)
            ·
              refine ⟨1038088396739833760539565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692058931159889173693043 1038088396739833760539565)
              ·
                refine ⟨389283148777437660202337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038088396739833760539565 389283148777437660202337)
                ·
                  refine ⟨291962361583078245151753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389283148777437660202337 291962361583078245151753)
                  ·
                    rfl

theorem cell20_639669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_639669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639669 prefixEnd_639669 := by exact prefixLift 639669
  have htrace : WordTrace (prefixWord ++ tailWord_639669) baseStart_639669 baseEnd_639669 := by
    simpa [prefixWord, tailWord_639669, baseEnd_639669] using wordTrace_append hprefix tailTrace_639669
  have hstable : (prefixWord ++ tailWord_639669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639669).length < 2 ^ (prefixWord ++ tailWord_639669).sum := by decide
  have hdescent : baseEnd_639669 < baseStart_639669 := by decide
  rcases family_descends (prefixWord ++ tailWord_639669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639686 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_639686 : Nat := 118140960795 + 639686 * 2 ^ 59
def prefixEnd_639686 : Nat := 4983230072969 + 3 ^ 40 * 639686 * 2
def baseEnd_639686 : Nat := 291970120846301741585017

theorem tailTrace_639686 : CollatzResearch.WordTrace tailWord_639686 prefixEnd_639686 291970120846301741585017 := by
  unfold tailWord_639686
  simp only [CollatzResearch.WordTrace]
  refine ⟨729102036266698328628091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15554176773689564344065941 729102036266698328628091)
  ·
    refine ⟨1093653054400047492942137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729102036266698328628091 1093653054400047492942137)
    ·
      refine ⟨820239790800035619706603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1093653054400047492942137 820239790800035619706603)
      ·
        refine ⟨1230359686200053429559905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820239790800035619706603 1230359686200053429559905)
        ·
          refine ⟨922769764650040072169929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230359686200053429559905 922769764650040072169929)
          ·
            refine ⟨692077323487530054127447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922769764650040072169929 692077323487530054127447)
            ·
              refine ⟨1038115985231295081191171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692077323487530054127447 1038115985231295081191171)
              ·
                refine ⟨1557173977846942621786757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038115985231295081191171 1557173977846942621786757)
                ·
                  refine ⟨291970120846301741585017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557173977846942621786757 291970120846301741585017)
                  ·
                    rfl

theorem cell20_639686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_639686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639686 prefixEnd_639686 := by exact prefixLift 639686
  have htrace : WordTrace (prefixWord ++ tailWord_639686) baseStart_639686 baseEnd_639686 := by
    simpa [prefixWord, tailWord_639686, baseEnd_639686] using wordTrace_append hprefix tailTrace_639686
  have hstable : (prefixWord ++ tailWord_639686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639686).length < 2 ^ (prefixWord ++ tailWord_639686).sum := by decide
  have hdescent : baseEnd_639686 < baseStart_639686 := by decide
  rcases family_descends (prefixWord ++ tailWord_639686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639700 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_639700 : Nat := 118140960795 + 639700 * 2 ^ 59
def prefixEnd_639700 : Nat := 4983230072969 + 3 ^ 40 * 639700 * 2
def baseEnd_639700 : Nat := 291976510827779915118293

theorem tailTrace_639700 : CollatzResearch.WordTrace tailWord_639700 prefixEnd_639700 291976510827779915118293 := by
  unfold tailWord_639700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665887891241813453554277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15554517188322417938072369 11665887891241813453554277)
  ·
    refine ⟨2187353979607840022541427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11665887891241813453554277 2187353979607840022541427)
    ·
      refine ⟨3281030969411760033812141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187353979607840022541427 3281030969411760033812141)
      ·
        refine ⟨1230386613529410012679553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3281030969411760033812141 1230386613529410012679553)
        ·
          refine ⟨922789960147057509509665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230386613529410012679553 922789960147057509509665)
          ·
            refine ⟨692092470110293132132249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922789960147057509509665 692092470110293132132249)
            ·
              refine ⟨519069352582719849099187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692092470110293132132249 519069352582719849099187)
              ·
                refine ⟨778604028874079773648781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519069352582719849099187 778604028874079773648781)
                ·
                  refine ⟨291976510827779915118293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778604028874079773648781 291976510827779915118293)
                  ·
                    rfl

theorem cell20_639700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_639700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639700 prefixEnd_639700 := by exact prefixLift 639700
  have htrace : WordTrace (prefixWord ++ tailWord_639700) baseStart_639700 baseEnd_639700 := by
    simpa [prefixWord, tailWord_639700, baseEnd_639700] using wordTrace_append hprefix tailTrace_639700
  have hstable : (prefixWord ++ tailWord_639700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639700).length < 2 ^ (prefixWord ++ tailWord_639700).sum := by decide
  have hdescent : baseEnd_639700 < baseStart_639700 := by decide
  rcases family_descends (prefixWord ++ tailWord_639700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639704 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_639704 : Nat := 118140960795 + 639704 * 2 ^ 59
def prefixEnd_639704 : Nat := 4983230072969 + 3 ^ 40 * 639704 * 2
def baseEnd_639704 : Nat := 291978336536773678984943

theorem tailTrace_639704 : CollatzResearch.WordTrace tailWord_639704 prefixEnd_639704 291978336536773678984943 := by
  unfold tailWord_639704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665960837234567795127083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15554614449646090393502777 11665960837234567795127083)
  ·
    refine ⟨17498941255851851692690625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11665960837234567795127083 17498941255851851692690625)
    ·
      refine ⟨13124205941888888769517969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17498941255851851692690625 13124205941888888769517969)
      ·
        refine ⟨9843154456416666577138477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13124205941888888769517969 9843154456416666577138477)
        ·
          refine ⟨3691182921156249966426929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9843154456416666577138477 3691182921156249966426929)
          ·
            refine ⟨2768387190867187474820197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691182921156249966426929 2768387190867187474820197)
            ·
              refine ⟨519072598287597651528787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2768387190867187474820197 519072598287597651528787)
              ·
                refine ⟨778608897431396477293181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519072598287597651528787 778608897431396477293181)
                ·
                  refine ⟨291978336536773678984943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778608897431396477293181 291978336536773678984943)
                  ·
                    rfl

theorem cell20_639704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_639704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639704 prefixEnd_639704 := by exact prefixLift 639704
  have htrace : WordTrace (prefixWord ++ tailWord_639704) baseStart_639704 baseEnd_639704 := by
    simpa [prefixWord, tailWord_639704, baseEnd_639704] using wordTrace_append hprefix tailTrace_639704
  have hstable : (prefixWord ++ tailWord_639704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639704).length < 2 ^ (prefixWord ++ tailWord_639704).sum := by decide
  have hdescent : baseEnd_639704 < baseStart_639704 := by decide
  rcases family_descends (prefixWord ++ tailWord_639704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639742 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_639742 : Nat := 118140960795 + 639742 * 2 ^ 59
def prefixEnd_639742 : Nat := 4983230072969 + 3 ^ 40 * 639742 * 2
def baseEnd_639742 : Nat := 291995680772214435718121

theorem tailTrace_639742 : CollatzResearch.WordTrace tailWord_639742 prefixEnd_639742 291995680772214435718121 := by
  unfold tailWord_639742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916663456041433510017185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15555538432220978720091653 2916663456041433510017185)
  ·
    refine ⟨2187497592031075132512889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2916663456041433510017185 2187497592031075132512889)
    ·
      refine ⟨1640623194023306349384667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187497592031075132512889 1640623194023306349384667)
      ·
        refine ⟨2460934791034959524077001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640623194023306349384667 2460934791034959524077001)
        ·
          refine ⟨1845701093276219643057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460934791034959524077001 1845701093276219643057751)
          ·
            refine ⟨2768551639914329464586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845701093276219643057751 2768551639914329464586627)
            ·
              refine ⟨4152827459871494196879941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768551639914329464586627 4152827459871494196879941)
              ·
                refine ⟨778655148725905161914989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4152827459871494196879941 778655148725905161914989)
                ·
                  refine ⟨291995680772214435718121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778655148725905161914989 291995680772214435718121)
                  ·
                    rfl

theorem cell20_639742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_639742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639742 prefixEnd_639742 := by exact prefixLift 639742
  have htrace : WordTrace (prefixWord ++ tailWord_639742) baseStart_639742 baseEnd_639742 := by
    simpa [prefixWord, tailWord_639742, baseEnd_639742] using wordTrace_append hprefix tailTrace_639742
  have hstable : (prefixWord ++ tailWord_639742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639742).length < 2 ^ (prefixWord ++ tailWord_639742).sum := by decide
  have hdescent : baseEnd_639742 < baseStart_639742 := by decide
  rcases family_descends (prefixWord ++ tailWord_639742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639770 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_639770 : Nat := 118140960795 + 639770 * 2 ^ 59
def prefixEnd_639770 : Nat := 4983230072969 + 3 ^ 40 * 639770 * 2
def baseEnd_639770 : Nat := 292008460735170782784673

theorem tailTrace_639770 : CollatzResearch.WordTrace tailWord_639770 prefixEnd_639770 292008460735170782784673 := by
  unfold tailWord_639770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833582223057507215539191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15556219261486685908104509 5833582223057507215539191)
  ·
    refine ⟨8750373334586260823308787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5833582223057507215539191 8750373334586260823308787)
    ·
      refine ⟨13125560001879391234963181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8750373334586260823308787 13125560001879391234963181)
      ·
        refine ⟨4922085000704771713111193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13125560001879391234963181 4922085000704771713111193)
        ·
          refine ⟨3691563750528578784833395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4922085000704771713111193 3691563750528578784833395)
          ·
            refine ⟨5537345625792868177250093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691563750528578784833395 5537345625792868177250093)
            ·
              refine ⟨2076504609672325566468785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537345625792868177250093 2076504609672325566468785)
              ·
                refine ⟨1557378457254244174851589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076504609672325566468785 1557378457254244174851589)
                ·
                  refine ⟨292008460735170782784673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1557378457254244174851589 292008460735170782784673)
                  ·
                    rfl

theorem cell20_639770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_639770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639770 prefixEnd_639770 := by exact prefixLift 639770
  have htrace : WordTrace (prefixWord ++ tailWord_639770) baseStart_639770 baseEnd_639770 := by
    simpa [prefixWord, tailWord_639770, baseEnd_639770] using wordTrace_append hprefix tailTrace_639770
  have hstable : (prefixWord ++ tailWord_639770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639770).length < 2 ^ (prefixWord ++ tailWord_639770).sum := by decide
  have hdescent : baseEnd_639770 < baseStart_639770 := by decide
  rcases family_descends (prefixWord ++ tailWord_639770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639828 : List Nat := [2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_639828 : Nat := 118140960795 + 639828 * 2 ^ 59
def prefixEnd_639828 : Nat := 4983230072969 + 3 ^ 40 * 639828 * 2
def baseEnd_639828 : Nat := 97344977838526786283701

theorem tailTrace_639828 : CollatzResearch.WordTrace tailWord_639828 prefixEnd_639828 97344977838526786283701 := by
  unfold tailWord_639828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668222163009952383884069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15557629550679936511845425 11668222163009952383884069)
  ·
    refine ⟨2187791655564366071978263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11668222163009952383884069 2187791655564366071978263)
    ·
      refine ⟨3281687483346549107967395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187791655564366071978263 3281687483346549107967395)
      ·
        refine ⟨4922531225019823661951093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281687483346549107967395 4922531225019823661951093)
        ·
          refine ⟨461487302345608468307915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4922531225019823661951093 461487302345608468307915)
          ·
            refine ⟨692230953518412702461873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461487302345608468307915 692230953518412702461873)
            ·
              refine ⟨519173215138809526846405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692230953518412702461873 519173215138809526846405)
              ·
                refine ⟨97344977838526786283701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519173215138809526846405 97344977838526786283701)
                ·
                  rfl

theorem cell20_639828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_639828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639828 prefixEnd_639828 := by exact prefixLift 639828
  have htrace : WordTrace (prefixWord ++ tailWord_639828) baseStart_639828 baseEnd_639828 := by
    simpa [prefixWord, tailWord_639828, baseEnd_639828] using wordTrace_append hprefix tailTrace_639828
  have hstable : (prefixWord ++ tailWord_639828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639828).length < 2 ^ (prefixWord ++ tailWord_639828).sum := by decide
  have hdescent : baseEnd_639828 < baseStart_639828 := by decide
  rcases family_descends (prefixWord ++ tailWord_639828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639877 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_639877 : Nat := 118140960795 + 639877 * 2 ^ 59
def prefixEnd_639877 : Nat := 4983230072969 + 3 ^ 40 * 639877 * 2
def baseEnd_639877 : Nat := 292057298450753966217569

theorem tailTrace_639877 : CollatzResearch.WordTrace tailWord_639877 prefixEnd_639877 292057298450753966217569 := by
  unfold tailWord_639877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23338231502842386136301885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15558821001894924090867923 23338231502842386136301885)
  ·
    refine ⟨8751836813565894801113207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23338231502842386136301885 8751836813565894801113207)
    ·
      refine ⟨13127755220348842201669811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8751836813565894801113207 13127755220348842201669811)
      ·
        refine ⟨19691632830523263302504717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13127755220348842201669811 19691632830523263302504717)
        ·
          refine ⟨7384362311446223738439269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19691632830523263302504717 7384362311446223738439269)
          ·
            refine ⟨1384567933396166950957363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7384362311446223738439269 1384567933396166950957363)
            ·
              refine ⟨2076851900094250426436045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384567933396166950957363 2076851900094250426436045)
              ·
                refine ⟨778819462535343909913517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2076851900094250426436045 778819462535343909913517)
                ·
                  refine ⟨292057298450753966217569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778819462535343909913517 292057298450753966217569)
                  ·
                    rfl

theorem cell20_639877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_639877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639877 prefixEnd_639877 := by exact prefixLift 639877
  have htrace : WordTrace (prefixWord ++ tailWord_639877) baseStart_639877 baseEnd_639877 := by
    simpa [prefixWord, tailWord_639877, baseEnd_639877] using wordTrace_append hprefix tailTrace_639877
  have hstable : (prefixWord ++ tailWord_639877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639877).length < 2 ^ (prefixWord ++ tailWord_639877).sum := by decide
  have hdescent : baseEnd_639877 < baseStart_639877 := by decide
  rcases family_descends (prefixWord ++ tailWord_639877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639901 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 2]
def baseStart_639901 : Nat := 118140960795 + 639901 * 2 ^ 59
def prefixEnd_639901 : Nat := 4983230072969 + 3 ^ 40 * 639901 * 2
def baseEnd_639901 : Nat := 292068252704716549417471

theorem tailTrace_639901 : CollatzResearch.WordTrace tailWord_639901 prefixEnd_639901 292068252704716549417471 := by
  unfold tailWord_639901
  simp only [CollatzResearch.WordTrace]
  refine ⟨23339106854755438235175557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15559404569836958823450371 23339106854755438235175557)
  ·
    refine ⟨4376082535266644669095417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23339106854755438235175557 4376082535266644669095417)
    ·
      refine ⟨3282061901449983501821563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4376082535266644669095417 3282061901449983501821563)
      ·
        refine ⟨4923092852174975252732345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282061901449983501821563 4923092852174975252732345)
        ·
          refine ⟨3692319639131231439549259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923092852174975252732345 3692319639131231439549259)
          ·
            refine ⟨5538479458696847159323889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692319639131231439549259 5538479458696847159323889)
            ·
              refine ⟨4153859594022635369492917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538479458696847159323889 4153859594022635369492917)
              ·
                refine ⟨389424336939622065889961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4153859594022635369492917 389424336939622065889961)
                ·
                  refine ⟨292068252704716549417471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389424336939622065889961 292068252704716549417471)
                  ·
                    rfl

theorem cell20_639901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_639901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639901 prefixEnd_639901 := by exact prefixLift 639901
  have htrace : WordTrace (prefixWord ++ tailWord_639901) baseStart_639901 baseEnd_639901 := by
    simpa [prefixWord, tailWord_639901, baseEnd_639901] using wordTrace_append hprefix tailTrace_639901
  have hstable : (prefixWord ++ tailWord_639901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639901).length < 2 ^ (prefixWord ++ tailWord_639901).sum := by decide
  have hdescent : baseEnd_639901 < baseStart_639901 := by decide
  rcases family_descends (prefixWord ++ tailWord_639901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639929 : List Nat := [1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_639929 : Nat := 118140960795 + 639929 * 2 ^ 59
def prefixEnd_639929 : Nat := 4983230072969 + 3 ^ 40 * 639929 * 2
def baseEnd_639929 : Nat := 97360344222557632161341

theorem tailTrace_639929 : CollatzResearch.WordTrace tailWord_639929 prefixEnd_639929 97360344222557632161341 := by
  unfold tailWord_639929
  simp only [CollatzResearch.WordTrace]
  refine ⟨23340128098653999017194841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15560085399102666011463227 23340128098653999017194841)
  ·
    refine ⟨17505096073990499262896131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23340128098653999017194841 17505096073990499262896131)
    ·
      refine ⟨26257644110985748894344197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17505096073990499262896131 26257644110985748894344197)
      ·
        refine ⟨4923308270809827917689537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26257644110985748894344197 4923308270809827917689537)
        ·
          refine ⟨3692481203107370938267153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923308270809827917689537 3692481203107370938267153)
          ·
            refine ⟨2769360902330528203700365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692481203107370938267153 2769360902330528203700365)
            ·
              refine ⟨1038510338373948076387637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2769360902330528203700365 1038510338373948076387637)
              ·
                refine ⟨97360344222557632161341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038510338373948076387637 97360344222557632161341)
                ·
                  rfl

theorem cell20_639929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_639929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639929 prefixEnd_639929 := by exact prefixLift 639929
  have htrace : WordTrace (prefixWord ++ tailWord_639929) baseStart_639929 baseEnd_639929 := by
    simpa [prefixWord, tailWord_639929, baseEnd_639929] using wordTrace_append hprefix tailTrace_639929
  have hstable : (prefixWord ++ tailWord_639929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639929).length < 2 ^ (prefixWord ++ tailWord_639929).sum := by decide
  have hdescent : baseEnd_639929 < baseStart_639929 := by decide
  rcases family_descends (prefixWord ++ tailWord_639929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639943 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_639943 : Nat := 118140960795 + 639943 * 2 ^ 59
def prefixEnd_639943 : Nat := 4983230072969 + 3 ^ 40 * 639943 * 2
def baseEnd_639943 : Nat := 292087422649151070017299

theorem tailTrace_639943 : CollatzResearch.WordTrace tailWord_639943 prefixEnd_639943 292087422649151070017299 := by
  unfold tailWord_639943
  simp only [CollatzResearch.WordTrace]
  refine ⟨23340638720603279408204483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15560425813735519605469655 23340638720603279408204483)
  ·
    refine ⟨35010958080904919112306725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23340638720603279408204483 35010958080904919112306725)
    ·
      refine ⟨6564554640169672333557511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35010958080904919112306725 6564554640169672333557511)
      ·
        refine ⟨9846831960254508500336267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564554640169672333557511 9846831960254508500336267)
        ·
          refine ⟨14770247940381762750504401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9846831960254508500336267 14770247940381762750504401)
          ·
            refine ⟨11077685955286322062878301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14770247940381762750504401 11077685955286322062878301)
            ·
              refine ⟨4154132233232370773579363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11077685955286322062878301 4154132233232370773579363)
              ·
                refine ⟨6231198349848556160369045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154132233232370773579363 6231198349848556160369045)
                ·
                  refine ⟨292087422649151070017299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6231198349848556160369045 292087422649151070017299)
                  ·
                    rfl

theorem cell20_639943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_639943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639943 prefixEnd_639943 := by exact prefixLift 639943
  have htrace : WordTrace (prefixWord ++ tailWord_639943) baseStart_639943 baseEnd_639943 := by
    simpa [prefixWord, tailWord_639943, baseEnd_639943] using wordTrace_append hprefix tailTrace_639943
  have hstable : (prefixWord ++ tailWord_639943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639943).length < 2 ^ (prefixWord ++ tailWord_639943).sum := by decide
  have hdescent : baseEnd_639943 < baseStart_639943 := by decide
  rcases family_descends (prefixWord ++ tailWord_639943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639956 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_639956 : Nat := 118140960795 + 639956 * 2 ^ 59
def prefixEnd_639956 : Nat := 4983230072969 + 3 ^ 40 * 639956 * 2
def baseEnd_639956 : Nat := 292093356203380802583913

theorem tailTrace_639956 : CollatzResearch.WordTrace tailWord_639956 prefixEnd_639956 292093356203380802583913 := by
  unfold tailWord_639956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11670556434778091314213861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15560741913037455085618481 11670556434778091314213861)
  ·
    refine ⟨2188229331520892121415099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11670556434778091314213861 2188229331520892121415099)
    ·
      refine ⟨3282343997281338182122649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188229331520892121415099 3282343997281338182122649)
      ·
        refine ⟨2461757997961003636591987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3282343997281338182122649 2461757997961003636591987)
        ·
          refine ⟨3692636996941505454887981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461757997961003636591987 3692636996941505454887981)
          ·
            refine ⟨1384738873853064545582993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3692636996941505454887981 1384738873853064545582993)
            ·
              refine ⟨1038554155389798409187245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384738873853064545582993 1038554155389798409187245)
              ·
                refine ⟨389457808271174403445217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038554155389798409187245 389457808271174403445217)
                ·
                  refine ⟨292093356203380802583913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389457808271174403445217 292093356203380802583913)
                  ·
                    rfl

theorem cell20_639956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_639956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639956 prefixEnd_639956 := by exact prefixLift 639956
  have htrace : WordTrace (prefixWord ++ tailWord_639956) baseStart_639956 baseEnd_639956 := by
    simpa [prefixWord, tailWord_639956, baseEnd_639956] using wordTrace_append hprefix tailTrace_639956
  have hstable : (prefixWord ++ tailWord_639956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639956).length < 2 ^ (prefixWord ++ tailWord_639956).sum := by decide
  have hdescent : baseEnd_639956 < baseStart_639956 := by decide
  rcases family_descends (prefixWord ++ tailWord_639956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639967 : List Nat := [1, 1, 2, 3, 5, 1, 7]
def baseStart_639967 : Nat := 118140960795 + 639967 * 2 ^ 59
def prefixEnd_639967 : Nat := 4983230072969 + 3 ^ 40 * 639967 * 2
def baseEnd_639967 : Nat := 32455375211457072579689

theorem tailTrace_639967 : CollatzResearch.WordTrace tailWord_639967 prefixEnd_639967 32455375211457072579689 := by
  unfold tailWord_639967
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341514072516331507078155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15561009381677554338052103 23341514072516331507078155)
  ·
    refine ⟨35012271108774497260617233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23341514072516331507078155 35012271108774497260617233)
    ·
      refine ⟨26259203331580872945462925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35012271108774497260617233 26259203331580872945462925)
      ·
        refine ⟨9847201249342827354548597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26259203331580872945462925 9847201249342827354548597)
        ·
          refine ⟨923175117125890064488931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9847201249342827354548597 923175117125890064488931)
          ·
            refine ⟨1384762675688835096733397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923175117125890064488931 1384762675688835096733397)
            ·
              refine ⟨32455375211457072579689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1384762675688835096733397 32455375211457072579689)
              ·
                rfl

theorem cell20_639967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_639967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639967 prefixEnd_639967 := by exact prefixLift 639967
  have htrace : WordTrace (prefixWord ++ tailWord_639967) baseStart_639967 baseEnd_639967 := by
    simpa [prefixWord, tailWord_639967, baseEnd_639967] using wordTrace_append hprefix tailTrace_639967
  have hstable : (prefixWord ++ tailWord_639967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639967).length < 2 ^ (prefixWord ++ tailWord_639967).sum := by decide
  have hdescent : baseEnd_639967 < baseStart_639967 := by decide
  rcases family_descends (prefixWord ++ tailWord_639967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639970 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_639970 : Nat := 118140960795 + 639970 * 2 ^ 59
def prefixEnd_639970 : Nat := 4983230072969 + 3 ^ 40 * 639970 * 2
def baseEnd_639970 : Nat := 292099746184858976117189

theorem tailTrace_639970 : CollatzResearch.WordTrace tailWord_639970 prefixEnd_639970 292099746184858976117189 := by
  unfold tailWord_639970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835405872876365754859341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15561082327670308679624909 5835405872876365754859341)
  ·
    refine ⟨2188277202328637158072253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5835405872876365754859341 2188277202328637158072253)
    ·
      refine ⟨820603950873238934277095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2188277202328637158072253 820603950873238934277095)
      ·
        refine ⟨1230905926309858401415643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820603950873238934277095 1230905926309858401415643)
        ·
          refine ⟨1846358889464787602123465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230905926309858401415643 1846358889464787602123465)
          ·
            refine ⟨1384769167098590701592599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846358889464787602123465 1384769167098590701592599)
            ·
              refine ⟨2077153750647886052388899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384769167098590701592599 2077153750647886052388899)
              ·
                refine ⟨3115730625971829078583349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077153750647886052388899 3115730625971829078583349)
                ·
                  refine ⟨292099746184858976117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115730625971829078583349 292099746184858976117189)
                  ·
                    rfl

theorem cell20_639970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_639970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_639970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_639970 prefixEnd_639970 := by exact prefixLift 639970
  have htrace : WordTrace (prefixWord ++ tailWord_639970) baseStart_639970 baseEnd_639970 := by
    simpa [prefixWord, tailWord_639970, baseEnd_639970] using wordTrace_append hprefix tailTrace_639970
  have hstable : (prefixWord ++ tailWord_639970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639970).length < 2 ^ (prefixWord ++ tailWord_639970).sum := by decide
  have hdescent : baseEnd_639970 < baseStart_639970 := by decide
  rcases family_descends (prefixWord ++ tailWord_639970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640012 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_640012 : Nat := 118140960795 + 640012 * 2 ^ 59
def prefixEnd_640012 : Nat := 4983230072969 + 3 ^ 40 * 640012 * 2
def baseEnd_640012 : Nat := 292118916129293496717017

theorem tailTrace_640012 : CollatzResearch.WordTrace tailWord_640012 prefixEnd_640012 292118916129293496717017 := by
  unfold tailWord_640012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671577678676652096233145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15562103571568869461644193 11671577678676652096233145)
  ·
    refine ⟨8753683259007489072174859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11671577678676652096233145 8753683259007489072174859)
    ·
      refine ⟨13130524888511233608262289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8753683259007489072174859 13130524888511233608262289)
      ·
        refine ⟨9847893666383425206196717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13130524888511233608262289 9847893666383425206196717)
        ·
          refine ⟨3692960124893784452323769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9847893666383425206196717 3692960124893784452323769)
          ·
            refine ⟨2769720093670338339242827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692960124893784452323769 2769720093670338339242827)
            ·
              refine ⟨4154580140505507508864241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769720093670338339242827 4154580140505507508864241)
              ·
                refine ⟨3115935105379130631648181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154580140505507508864241 3115935105379130631648181)
                ·
                  refine ⟨292118916129293496717017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115935105379130631648181 292118916129293496717017)
                  ·
                    rfl

theorem cell20_640012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_640012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640012 prefixEnd_640012 := by exact prefixLift 640012
  have htrace : WordTrace (prefixWord ++ tailWord_640012) baseStart_640012 baseEnd_640012 := by
    simpa [prefixWord, tailWord_640012, baseEnd_640012] using wordTrace_append hprefix tailTrace_640012
  have hstable : (prefixWord ++ tailWord_640012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640012).length < 2 ^ (prefixWord ++ tailWord_640012).sum := by decide
  have hdescent : baseEnd_640012 < baseStart_640012 := by decide
  rcases family_descends (prefixWord ++ tailWord_640012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640018 : List Nat := [3, 2, 5, 1, 1, 2, 6]
def baseStart_640018 : Nat := 118140960795 + 640018 * 2 ^ 59
def prefixEnd_640018 : Nat := 4983230072969 + 3 ^ 40 * 640018 * 2
def baseEnd_640018 : Nat := 32457961632531571390777

theorem tailTrace_640018 : CollatzResearch.WordTrace tailWord_640018 prefixEnd_640018 32457961632531571390777 := by
  unfold tailWord_640018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835843548832891804296177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15562249463554378144789805 5835843548832891804296177)
  ·
    refine ⟨4376882661624668853222133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835843548832891804296177 4376882661624668853222133)
    ·
      refine ⟨410332749527312704989575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4376882661624668853222133 410332749527312704989575)
      ·
        refine ⟨615499124290969057484363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410332749527312704989575 615499124290969057484363)
        ·
          refine ⟨923248686436453586226545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615499124290969057484363 923248686436453586226545)
          ·
            refine ⟨692436514827340189669909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923248686436453586226545 692436514827340189669909)
            ·
              refine ⟨32457961632531571390777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 692436514827340189669909 32457961632531571390777)
              ·
                rfl

theorem cell20_640018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_640018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640018 prefixEnd_640018 := by exact prefixLift 640018
  have htrace : WordTrace (prefixWord ++ tailWord_640018) baseStart_640018 baseEnd_640018 := by
    simpa [prefixWord, tailWord_640018, baseEnd_640018] using wordTrace_append hprefix tailTrace_640018
  have hstable : (prefixWord ++ tailWord_640018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640018).length < 2 ^ (prefixWord ++ tailWord_640018).sum := by decide
  have hdescent : baseEnd_640018 < baseStart_640018 := by decide
  rcases family_descends (prefixWord ++ tailWord_640018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640032 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_640032 : Nat := 118140960795 + 640032 * 2 ^ 59
def prefixEnd_640032 : Nat := 4983230072969 + 3 ^ 40 * 640032 * 2
def baseEnd_640032 : Nat := 292128044674262316050269

theorem tailTrace_640032 : CollatzResearch.WordTrace tailWord_640032 prefixEnd_640032 292128044674262316050269 := by
  unfold tailWord_640032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671942408640423804097175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15562589878187231738796233 11671942408640423804097175)
  ·
    refine ⟨17507913612960635706145763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11671942408640423804097175 17507913612960635706145763)
    ·
      refine ⟨26261870419440953559218645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17507913612960635706145763 26261870419440953559218645)
      ·
        refine ⟨615512587955647349044187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26261870419440953559218645 615512587955647349044187)
        ·
          refine ⟨923268881933471023566281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615512587955647349044187 923268881933471023566281)
          ·
            refine ⟨692451661450103267674711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923268881933471023566281 692451661450103267674711)
            ·
              refine ⟨1038677492175154901512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692451661450103267674711 1038677492175154901512067)
              ·
                refine ⟨1558016238262732352268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038677492175154901512067 1558016238262732352268101)
                ·
                  refine ⟨292128044674262316050269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558016238262732352268101 292128044674262316050269)
                  ·
                    rfl

theorem cell20_640032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_640032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640032 prefixEnd_640032 := by exact prefixLift 640032
  have htrace : WordTrace (prefixWord ++ tailWord_640032) baseStart_640032 baseEnd_640032 := by
    simpa [prefixWord, tailWord_640032, baseEnd_640032] using wordTrace_append hprefix tailTrace_640032
  have hstable : (prefixWord ++ tailWord_640032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640032).length < 2 ^ (prefixWord ++ tailWord_640032).sum := by decide
  have hdescent : baseEnd_640032 < baseStart_640032 := by decide
  rcases family_descends (prefixWord ++ tailWord_640032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640042 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_640042 : Nat := 118140960795 + 640042 * 2 ^ 59
def prefixEnd_640042 : Nat := 4983230072969 + 3 ^ 40 * 640042 * 2
def baseEnd_640042 : Nat := 292132608946746725716895

theorem tailTrace_640042 : CollatzResearch.WordTrace tailWord_640042 prefixEnd_640042 292132608946746725716895 := by
  unfold tailWord_640042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836062386811154829014595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15562833031496412877372253 5836062386811154829014595)
  ·
    refine ⟨8754093580216732243521893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5836062386811154829014595 8754093580216732243521893)
    ·
      refine ⟨1641392546290637295660355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8754093580216732243521893 1641392546290637295660355)
      ·
        refine ⟨2462088819435955943490533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641392546290637295660355 2462088819435955943490533)
        ·
          refine ⟨461641653644241739404475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2462088819435955943490533 461641653644241739404475)
          ·
            refine ⟨692462480466362609106713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461641653644241739404475 692462480466362609106713)
            ·
              refine ⟨519346860349771956830035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692462480466362609106713 519346860349771956830035)
              ·
                refine ⟨779020290524657935245053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519346860349771956830035 779020290524657935245053)
                ·
                  refine ⟨292132608946746725716895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779020290524657935245053 292132608946746725716895)
                  ·
                    rfl

theorem cell20_640042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_640042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640042 prefixEnd_640042 := by exact prefixLift 640042
  have htrace : WordTrace (prefixWord ++ tailWord_640042) baseStart_640042 baseEnd_640042 := by
    simpa [prefixWord, tailWord_640042, baseEnd_640042] using wordTrace_append hprefix tailTrace_640042
  have hstable : (prefixWord ++ tailWord_640042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640042).length < 2 ^ (prefixWord ++ tailWord_640042).sum := by decide
  have hdescent : baseEnd_640042 < baseStart_640042 := by decide
  rcases family_descends (prefixWord ++ tailWord_640042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640064 : List Nat := [2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_640064 : Nat := 118140960795 + 640064 * 2 ^ 59
def prefixEnd_640064 : Nat := 4983230072969 + 3 ^ 40 * 640064 * 2
def baseEnd_640064 : Nat := 97380883448737475661157

theorem tailTrace_640064 : CollatzResearch.WordTrace tailWord_640064 prefixEnd_640064 97380883448737475661157 := by
  unfold tailWord_640064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672525976582458536679623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15563367968776611382239497 11672525976582458536679623)
  ·
    refine ⟨17508788964873687805019435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11672525976582458536679623 17508788964873687805019435)
    ·
      refine ⟨26263183447310531707529153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17508788964873687805019435 26263183447310531707529153)
      ·
        refine ⟨19697387585482898780646865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26263183447310531707529153 19697387585482898780646865)
        ·
          refine ⟨14773040689112174085485149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19697387585482898780646865 14773040689112174085485149)
          ·
            refine ⟨5539890258417065282056931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14773040689112174085485149 5539890258417065282056931)
            ·
              refine ⟨8309835387625597923085397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5539890258417065282056931 8309835387625597923085397)
              ·
                refine ⟨97380883448737475661157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8309835387625597923085397 97380883448737475661157)
                ·
                  rfl

theorem cell20_640064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_640064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640064 prefixEnd_640064 := by exact prefixLift 640064
  have htrace : WordTrace (prefixWord ++ tailWord_640064) baseStart_640064 baseEnd_640064 := by
    simpa [prefixWord, tailWord_640064, baseEnd_640064] using wordTrace_append hprefix tailTrace_640064
  have hstable : (prefixWord ++ tailWord_640064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640064).length < 2 ^ (prefixWord ++ tailWord_640064).sum := by decide
  have hdescent : baseEnd_640064 < baseStart_640064 := by decide
  rcases family_descends (prefixWord ++ tailWord_640064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640094 : List Nat := [4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_640094 : Nat := 118140960795 + 640094 * 2 ^ 59
def prefixEnd_640094 : Nat := 4983230072969 + 3 ^ 40 * 640094 * 2
def baseEnd_640094 : Nat := 97385447721221885327783

theorem tailTrace_640094 : CollatzResearch.WordTrace tailWord_640094 prefixEnd_640094 97385447721221885327783 := by
  unfold tailWord_640094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918268267882029024618917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15564097428704154797967557 2918268267882029024618917)
  ·
    refine ⟨547175300227880442116047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2918268267882029024618917 547175300227880442116047)
    ·
      refine ⟨820762950341820663174071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547175300227880442116047 820762950341820663174071)
      ·
        refine ⟨1231144425512730994761107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820762950341820663174071 1231144425512730994761107)
        ·
          refine ⟨1846716638269096492141661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231144425512730994761107 1846716638269096492141661)
          ·
            refine ⟨692518739350911184553123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1846716638269096492141661 692518739350911184553123)
            ·
              refine ⟨1038778109026366776829685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692518739350911184553123 1038778109026366776829685)
              ·
                refine ⟨97385447721221885327783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038778109026366776829685 97385447721221885327783)
                ·
                  rfl

theorem cell20_640094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_640094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640094 prefixEnd_640094 := by exact prefixLift 640094
  have htrace : WordTrace (prefixWord ++ tailWord_640094) baseStart_640094 baseEnd_640094 := by
    simpa [prefixWord, tailWord_640094, baseEnd_640094] using wordTrace_append hprefix tailTrace_640094
  have hstable : (prefixWord ++ tailWord_640094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640094).length < 2 ^ (prefixWord ++ tailWord_640094).sum := by decide
  have hdescent : baseEnd_640094 < baseStart_640094 := by decide
  rcases family_descends (prefixWord ++ tailWord_640094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640095 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_640095 : Nat := 118140960795 + 640095 * 2 ^ 59
def prefixEnd_640095 : Nat := 4983230072969 + 3 ^ 40 * 640095 * 2
def baseEnd_640095 : Nat := 292156799590914096950011

theorem tailTrace_640095 : CollatzResearch.WordTrace tailWord_640095 prefixEnd_640095 292156799590914096950011 := by
  unfold tailWord_640095
  simp only [CollatzResearch.WordTrace]
  refine ⟨23346182616052609367737739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15564121744035072911825159 23346182616052609367737739)
  ·
    refine ⟨35019273924078914051606609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23346182616052609367737739 35019273924078914051606609)
    ·
      refine ⟨26264455443059185538704957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35019273924078914051606609 26264455443059185538704957)
      ·
        refine ⟨9849170791147194577014359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26264455443059185538704957 9849170791147194577014359)
        ·
          refine ⟨14773756186720791865521539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9849170791147194577014359 14773756186720791865521539)
          ·
            refine ⟨22160634280081187798282309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14773756186720791865521539 22160634280081187798282309)
            ·
              refine ⟨4155118927515222712177933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22160634280081187798282309 4155118927515222712177933)
              ·
                refine ⟨1558169597818208517066725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155118927515222712177933 1558169597818208517066725)
                ·
                  refine ⟨292156799590914096950011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1558169597818208517066725 292156799590914096950011)
                  ·
                    rfl

theorem cell20_640095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_640095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640095 prefixEnd_640095 := by exact prefixLift 640095
  have htrace : WordTrace (prefixWord ++ tailWord_640095) baseStart_640095 baseEnd_640095 := by
    simpa [prefixWord, tailWord_640095, baseEnd_640095] using wordTrace_append hprefix tailTrace_640095
  have hstable : (prefixWord ++ tailWord_640095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640095).length < 2 ^ (prefixWord ++ tailWord_640095).sum := by decide
  have hdescent : baseEnd_640095 < baseStart_640095 := by decide
  rcases family_descends (prefixWord ++ tailWord_640095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640098 : List Nat := [3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_640098 : Nat := 118140960795 + 640098 * 2 ^ 59
def prefixEnd_640098 : Nat := 4983230072969 + 3 ^ 40 * 640098 * 2
def baseEnd_640098 : Nat := 97386056290886473283333

theorem tailTrace_640098 : CollatzResearch.WordTrace tailWord_640098 prefixEnd_640098 97386056290886473283333 := by
  unfold tailWord_640098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836573008760435220024237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15564194690027827253397965 5836573008760435220024237)
  ·
    refine ⟨2188714878285163207509089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5836573008760435220024237 2188714878285163207509089)
    ·
      refine ⟨1641536158713872405631817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2188714878285163207509089 1641536158713872405631817)
      ·
        refine ⟨1231152119035404304223863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1641536158713872405631817 1231152119035404304223863)
        ·
          refine ⟨1846728178553106456335795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231152119035404304223863 1846728178553106456335795)
          ·
            refine ⟨2770092267829659684503693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846728178553106456335795 2770092267829659684503693)
            ·
              refine ⟨1038784600436122381688885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2770092267829659684503693 1038784600436122381688885)
              ·
                refine ⟨97386056290886473283333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038784600436122381688885 97386056290886473283333)
                ·
                  rfl

theorem cell20_640098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_640098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640098 prefixEnd_640098 := by exact prefixLift 640098
  have htrace : WordTrace (prefixWord ++ tailWord_640098) baseStart_640098 baseEnd_640098 := by
    simpa [prefixWord, tailWord_640098, baseEnd_640098] using wordTrace_append hprefix tailTrace_640098
  have hstable : (prefixWord ++ tailWord_640098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640098).length < 2 ^ (prefixWord ++ tailWord_640098).sum := by decide
  have hdescent : baseEnd_640098 < baseStart_640098 := by decide
  rcases family_descends (prefixWord ++ tailWord_640098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640119 : List Nat := [1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_640119 : Nat := 118140960795 + 640119 * 2 ^ 59
def prefixEnd_640119 : Nat := 4983230072969 + 3 ^ 40 * 640119 * 2
def baseEnd_640119 : Nat := 97389251281625560049971

theorem tailTrace_640119 : CollatzResearch.WordTrace tailWord_640119 prefixEnd_640119 97389251281625560049971 := by
  unfold tailWord_640119
  simp only [CollatzResearch.WordTrace]
  refine ⟨23347057967965661466611411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15564705311977107644407607 23347057967965661466611411)
  ·
    refine ⟨35020586951948492199917117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23347057967965661466611411 35020586951948492199917117)
    ·
      refine ⟨13132720106980684574968919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35020586951948492199917117 13132720106980684574968919)
      ·
        refine ⟨19699080160471026862453379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13132720106980684574968919 19699080160471026862453379)
        ·
          refine ⟨29548620240706540293680069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19699080160471026862453379 29548620240706540293680069)
          ·
            refine ⟨5540366295132476305065013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29548620240706540293680069 5540366295132476305065013)
            ·
              refine ⟨519409340168669653599845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5540366295132476305065013 519409340168669653599845)
              ·
                refine ⟨97389251281625560049971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519409340168669653599845 97389251281625560049971)
                ·
                  rfl

theorem cell20_640119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_640119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640119 prefixEnd_640119 := by exact prefixLift 640119
  have htrace : WordTrace (prefixWord ++ tailWord_640119) baseStart_640119 baseEnd_640119 := by
    simpa [prefixWord, tailWord_640119, baseEnd_640119] using wordTrace_append hprefix tailTrace_640119
  have hstable : (prefixWord ++ tailWord_640119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640119).length < 2 ^ (prefixWord ++ tailWord_640119).sum := by decide
  have hdescent : baseEnd_640119 < baseStart_640119 := by decide
  rcases family_descends (prefixWord ++ tailWord_640119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640129 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 2]
def baseStart_640129 : Nat := 118140960795 + 640129 * 2 ^ 59
def prefixEnd_640129 : Nat := 4983230072969 + 3 ^ 40 * 640129 * 2
def baseEnd_640129 : Nat := 292172318117361089816539

theorem tailTrace_640129 : CollatzResearch.WordTrace tailWord_640129 prefixEnd_640129 292172318117361089816539 := by
  unfold tailWord_640129
  simp only [CollatzResearch.WordTrace]
  refine ⟨23347422697929433174475441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15564948465286288782983627 23347422697929433174475441)
  ·
    refine ⟨17510567023447074880856581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23347422697929433174475441 17510567023447074880856581)
    ·
      refine ⟨3283231316896326540160609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17510567023447074880856581 3283231316896326540160609)
      ·
        refine ⟨2462423487672244905120457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283231316896326540160609 2462423487672244905120457)
        ·
          refine ⟨1846817615754183678840343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462423487672244905120457 1846817615754183678840343)
          ·
            refine ⟨2770226423631275518260515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846817615754183678840343 2770226423631275518260515)
            ·
              refine ⟨4155339635446913277390773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770226423631275518260515 4155339635446913277390773)
              ·
                refine ⟨389563090823148119755385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4155339635446913277390773 389563090823148119755385)
                ·
                  refine ⟨292172318117361089816539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389563090823148119755385 292172318117361089816539)
                  ·
                    rfl

theorem cell20_640129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_640129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640129 prefixEnd_640129 := by exact prefixLift 640129
  have htrace : WordTrace (prefixWord ++ tailWord_640129) baseStart_640129 baseEnd_640129 := by
    simpa [prefixWord, tailWord_640129, baseEnd_640129] using wordTrace_append hprefix tailTrace_640129
  have hstable : (prefixWord ++ tailWord_640129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640129).length < 2 ^ (prefixWord ++ tailWord_640129).sum := by decide
  have hdescent : baseEnd_640129 < baseStart_640129 := by decide
  rcases family_descends (prefixWord ++ tailWord_640129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640202 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_640202 : Nat := 118140960795 + 640202 * 2 ^ 59
def prefixEnd_640202 : Nat := 4983230072969 + 3 ^ 40 * 640202 * 2
def baseEnd_640202 : Nat := 292205637306497280382907

theorem tailTrace_640202 : CollatzResearch.WordTrace tailWord_640202 prefixEnd_640202 292205637306497280382907 := by
  unfold tailWord_640202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837521306666241660470715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15566723484443311094588573 5837521306666241660470715)
  ·
    refine ⟨8756281959999362490706073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837521306666241660470715 8756281959999362490706073)
    ·
      refine ⟨6567211469999521868029555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8756281959999362490706073 6567211469999521868029555)
      ·
        refine ⟨9850817204999282802044333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567211469999521868029555 9850817204999282802044333)
        ·
          refine ⟨3694056451874731050766625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9850817204999282802044333 3694056451874731050766625)
          ·
            refine ⟨2770542338906048288074969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3694056451874731050766625 2770542338906048288074969)
            ·
              refine ⟨2077906754179536216056227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770542338906048288074969 2077906754179536216056227)
              ·
                refine ⟨3116860131269304324084341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077906754179536216056227 3116860131269304324084341)
                ·
                  refine ⟨292205637306497280382907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3116860131269304324084341 292205637306497280382907)
                  ·
                    rfl

theorem cell20_640202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_640202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640202 prefixEnd_640202 := by exact prefixLift 640202
  have htrace : WordTrace (prefixWord ++ tailWord_640202) baseStart_640202 baseEnd_640202 := by
    simpa [prefixWord, tailWord_640202, baseEnd_640202] using wordTrace_append hprefix tailTrace_640202
  have hstable : (prefixWord ++ tailWord_640202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640202).length < 2 ^ (prefixWord ++ tailWord_640202).sum := by decide
  have hdescent : baseEnd_640202 < baseStart_640202 := by decide
  rcases family_descends (prefixWord ++ tailWord_640202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640257 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_640257 : Nat := 118140960795 + 640257 * 2 ^ 59
def prefixEnd_640257 : Nat := 4983230072969 + 3 ^ 40 * 640257 * 2
def baseEnd_640257 : Nat := 292230740805161533549349

theorem tailTrace_640257 : CollatzResearch.WordTrace tailWord_640257 prefixEnd_640257 292230740805161533549349 := by
  unfold tailWord_640257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23352091241465711035135025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15568060827643807356756683 23352091241465711035135025)
  ·
    refine ⟨17514068431099283276351269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23352091241465711035135025 17514068431099283276351269)
    ·
      refine ⟨3283887830831115614315863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17514068431099283276351269 3283887830831115614315863)
      ·
        refine ⟨4925831746246673421473795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283887830831115614315863 4925831746246673421473795)
        ·
          refine ⟨7388747619370010132210693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925831746246673421473795 7388747619370010132210693)
          ·
            refine ⟨1385390178631876899789505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7388747619370010132210693 1385390178631876899789505)
            ·
              refine ⟨1039042633973907674842129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385390178631876899789505 1039042633973907674842129)
              ·
                refine ⟨779281975480430756131597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039042633973907674842129 779281975480430756131597)
                ·
                  refine ⟨292230740805161533549349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779281975480430756131597 292230740805161533549349)
                  ·
                    rfl

theorem cell20_640257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_640257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640257 prefixEnd_640257 := by exact prefixLift 640257
  have htrace : WordTrace (prefixWord ++ tailWord_640257) baseStart_640257 baseEnd_640257 := by
    simpa [prefixWord, tailWord_640257, baseEnd_640257] using wordTrace_append hprefix tailTrace_640257
  have hstable : (prefixWord ++ tailWord_640257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640257).length < 2 ^ (prefixWord ++ tailWord_640257).sum := by decide
  have hdescent : baseEnd_640257 < baseStart_640257 := by decide
  rcases family_descends (prefixWord ++ tailWord_640257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640260 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_640260 : Nat := 118140960795 + 640260 * 2 ^ 59
def prefixEnd_640260 : Nat := 4983230072969 + 3 ^ 40 * 640260 * 2
def baseEnd_640260 : Nat := 292232110086906856449337

theorem tailTrace_640260 : CollatzResearch.WordTrace tailWord_640260 prefixEnd_640260 292232110086906856449337 := by
  unfold tailWord_640260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11676100330227421273747117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15568133773636561698329489 11676100330227421273747117)
  ·
    refine ⟨4378537623835282977655169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11676100330227421273747117 4378537623835282977655169)
    ·
      refine ⟨3283903217876462233241377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4378537623835282977655169 3283903217876462233241377)
      ·
        refine ⟨2462927413407346674931033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3283903217876462233241377 2462927413407346674931033)
        ·
          refine ⟨1847195560055510006198275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462927413407346674931033 1847195560055510006198275)
          ·
            refine ⟨2770793340083265009297413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847195560055510006198275 2770793340083265009297413)
            ·
              refine ⟨519523751265612189243265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2770793340083265009297413 519523751265612189243265)
              ·
                refine ⟨389642813449209141932449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519523751265612189243265 389642813449209141932449)
                ·
                  refine ⟨292232110086906856449337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389642813449209141932449 292232110086906856449337)
                  ·
                    rfl

theorem cell20_640260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_640260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640260 prefixEnd_640260 := by exact prefixLift 640260
  have htrace : WordTrace (prefixWord ++ tailWord_640260) baseStart_640260 baseEnd_640260 := by
    simpa [prefixWord, tailWord_640260, baseEnd_640260] using wordTrace_append hprefix tailTrace_640260
  have hstable : (prefixWord ++ tailWord_640260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640260).length < 2 ^ (prefixWord ++ tailWord_640260).sum := by decide
  have hdescent : baseEnd_640260 < baseStart_640260 := by decide
  rcases family_descends (prefixWord ++ tailWord_640260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640288 : List Nat := [2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_640288 : Nat := 118140960795 + 640288 * 2 ^ 59
def prefixEnd_640288 : Nat := 4983230072969 + 3 ^ 40 * 640288 * 2
def baseEnd_640288 : Nat := 97414963349954401171963

theorem tailTrace_640288 : CollatzResearch.WordTrace tailWord_640288 prefixEnd_640288 97414963349954401171963 := by
  unfold tailWord_640288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11676610952176701664756759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15568814602902268886342345 11676610952176701664756759)
  ·
    refine ⟨17514916428265052497135139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11676610952176701664756759 17514916428265052497135139)
    ·
      refine ⟨26272374642397578745702709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17514916428265052497135139 26272374642397578745702709)
      ·
        refine ⟨2463035122724773007409629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26272374642397578745702709 2463035122724773007409629)
        ·
          refine ⟨923638171021789877778611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2463035122724773007409629 923638171021789877778611)
          ·
            refine ⟨1385457256532684816667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923638171021789877778611 1385457256532684816667917)
            ·
              refine ⟨519546471199756806250469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385457256532684816667917 519546471199756806250469)
              ·
                refine ⟨97414963349954401171963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519546471199756806250469 97414963349954401171963)
                ·
                  rfl

theorem cell20_640288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_640288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640288 prefixEnd_640288 := by exact prefixLift 640288
  have htrace : WordTrace (prefixWord ++ tailWord_640288) baseStart_640288 baseEnd_640288 := by
    simpa [prefixWord, tailWord_640288, baseEnd_640288] using wordTrace_append hprefix tailTrace_640288
  have hstable : (prefixWord ++ tailWord_640288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640288).length < 2 ^ (prefixWord ++ tailWord_640288).sum := by decide
  have hdescent : baseEnd_640288 < baseStart_640288 := by decide
  rcases family_descends (prefixWord ++ tailWord_640288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640298 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_640298 : Nat := 118140960795 + 640298 * 2 ^ 59
def prefixEnd_640298 : Nat := 4983230072969 + 3 ^ 40 * 640298 * 2
def baseEnd_640298 : Nat := 292249454322347613182515

theorem tailTrace_640298 : CollatzResearch.WordTrace tailWord_640298 prefixEnd_640298 292249454322347613182515 := by
  unfold tailWord_640298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838396658579293759344387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15569057756211450024918365 5838396658579293759344387)
  ·
    refine ⟨8757594987868940639016581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5838396658579293759344387 8757594987868940639016581)
    ·
      refine ⟨1642049060225426369815609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8757594987868940639016581 1642049060225426369815609)
      ·
        refine ⟨1231536795169069777361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642049060225426369815609 1231536795169069777361707)
        ·
          refine ⟨1847305192753604666042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231536795169069777361707 1847305192753604666042561)
          ·
            refine ⟨1385478894565203499531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847305192753604666042561 1385478894565203499531921)
            ·
              refine ⟨1039109170923902624648941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1385478894565203499531921 1039109170923902624648941)
              ·
                refine ⟨389665939096463484243353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1039109170923902624648941 389665939096463484243353)
                ·
                  refine ⟨292249454322347613182515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389665939096463484243353 292249454322347613182515)
                  ·
                    rfl

theorem cell20_640298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_640298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640298 prefixEnd_640298 := by exact prefixLift 640298
  have htrace : WordTrace (prefixWord ++ tailWord_640298) baseStart_640298 baseEnd_640298 := by
    simpa [prefixWord, tailWord_640298, baseEnd_640298] using wordTrace_append hprefix tailTrace_640298
  have hstable : (prefixWord ++ tailWord_640298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640298).length < 2 ^ (prefixWord ++ tailWord_640298).sum := by decide
  have hdescent : baseEnd_640298 < baseStart_640298 := by decide
  rcases family_descends (prefixWord ++ tailWord_640298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640316 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_640316 : Nat := 118140960795 + 640316 * 2 ^ 59
def prefixEnd_640316 : Nat := 4983230072969 + 3 ^ 40 * 640316 * 2
def baseEnd_640316 : Nat := 292257670012819550582441

theorem tailTrace_640316 : CollatzResearch.WordTrace tailWord_640316 prefixEnd_640316 292257670012819550582441 := by
  unfold tailWord_640316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677121574125982055766401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15569495432167976074355201 11677121574125982055766401)
  ·
    refine ⟨8757841180594486541824801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11677121574125982055766401 8757841180594486541824801)
    ·
      refine ⟨6568380885445864906368601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8757841180594486541824801 6568380885445864906368601)
      ·
        refine ⟨4926285664084398679776451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6568380885445864906368601 4926285664084398679776451)
        ·
          refine ⟨7389428496126598019664677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926285664084398679776451 7389428496126598019664677)
          ·
            refine ⟨1385517843023737128687127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7389428496126598019664677 1385517843023737128687127)
            ·
              refine ⟨2078276764535605693030691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385517843023737128687127 2078276764535605693030691)
              ·
                refine ⟨3117415146803408539546037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078276764535605693030691 3117415146803408539546037)
                ·
                  refine ⟨292257670012819550582441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117415146803408539546037 292257670012819550582441)
                  ·
                    rfl

theorem cell20_640316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_640316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640316 prefixEnd_640316 := by exact prefixLift 640316
  have htrace : WordTrace (prefixWord ++ tailWord_640316) baseStart_640316 baseEnd_640316 := by
    simpa [prefixWord, tailWord_640316, baseEnd_640316] using wordTrace_append hprefix tailTrace_640316
  have hstable : (prefixWord ++ tailWord_640316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640316).length < 2 ^ (prefixWord ++ tailWord_640316).sum := by decide
  have hdescent : baseEnd_640316 < baseStart_640316 := by decide
  rcases family_descends (prefixWord ++ tailWord_640316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640349 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 2]
def baseStart_640349 : Nat := 118140960795 + 640349 * 2 ^ 59
def prefixEnd_640349 : Nat := 4983230072969 + 3 ^ 40 * 640349 * 2
def baseEnd_640349 : Nat := 292272732112018102482307

theorem tailTrace_640349 : CollatzResearch.WordTrace tailWord_640349 prefixEnd_640349 292272732112018102482307 := by
  unfold tailWord_640349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355446757132410747484101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15570297838088273831656067 23355446757132410747484101)
  ·
    refine ⟨4379146266962327015153269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23355446757132410747484101 4379146266962327015153269)
    ·
      refine ⟨410544962527718157670619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4379146266962327015153269 410544962527718157670619)
      ·
        refine ⟨615817443791577236505929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410544962527718157670619 615817443791577236505929)
        ·
          refine ⟨461863082843682927379447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615817443791577236505929 461863082843682927379447)
          ·
            refine ⟨692794624265524391069171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461863082843682927379447 692794624265524391069171)
            ·
              refine ⟨1039191936398286586603757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692794624265524391069171 1039191936398286586603757)
              ·
                refine ⟨389696976149357469976409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1039191936398286586603757 389696976149357469976409)
                ·
                  refine ⟨292272732112018102482307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389696976149357469976409 292272732112018102482307)
                  ·
                    rfl

theorem cell20_640349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_640349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640349 prefixEnd_640349 := by exact prefixLift 640349
  have htrace : WordTrace (prefixWord ++ tailWord_640349) baseStart_640349 baseEnd_640349 := by
    simpa [prefixWord, tailWord_640349, baseEnd_640349] using wordTrace_append hprefix tailTrace_640349
  have hstable : (prefixWord ++ tailWord_640349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640349).length < 2 ^ (prefixWord ++ tailWord_640349).sum := by decide
  have hdescent : baseEnd_640349 < baseStart_640349 := by decide
  rcases family_descends (prefixWord ++ tailWord_640349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640354 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_640354 : Nat := 118140960795 + 640354 * 2 ^ 59
def prefixEnd_640354 : Nat := 4983230072969 + 3 ^ 40 * 640354 * 2
def baseEnd_640354 : Nat := 292275014248260307315619

theorem tailTrace_640354 : CollatzResearch.WordTrace tailWord_640354 prefixEnd_640354 292275014248260307315619 := by
  unfold tailWord_640354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838907280528574150354029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15570419414742864400944077 5838907280528574150354029)
  ·
    refine ⟨2189590230198215306382761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5838907280528574150354029 2189590230198215306382761)
    ·
      refine ⟨1642192672648661479787071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189590230198215306382761 1642192672648661479787071)
      ·
        refine ⟨2463289008972992219680607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642192672648661479787071 2463289008972992219680607)
        ·
          refine ⟨3694933513459488329520911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463289008972992219680607 3694933513459488329520911)
          ·
            refine ⟨5542400270189232494281367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694933513459488329520911 5542400270189232494281367)
            ·
              refine ⟨8313600405283848741422051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542400270189232494281367 8313600405283848741422051)
              ·
                refine ⟨12470400607925773112133077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313600405283848741422051 12470400607925773112133077)
                ·
                  refine ⟨292275014248260307315619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12470400607925773112133077 292275014248260307315619)
                  ·
                    rfl

theorem cell20_640354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_640354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640354 prefixEnd_640354 := by exact prefixLift 640354
  have htrace : WordTrace (prefixWord ++ tailWord_640354) baseStart_640354 baseEnd_640354 := by
    simpa [prefixWord, tailWord_640354, baseEnd_640354] using wordTrace_append hprefix tailTrace_640354
  have hstable : (prefixWord ++ tailWord_640354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640354).length < 2 ^ (prefixWord ++ tailWord_640354).sum := by decide
  have hdescent : baseEnd_640354 < baseStart_640354 := by decide
  rcases family_descends (prefixWord ++ tailWord_640354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640375 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_640375 : Nat := 118140960795 + 640375 * 2 ^ 59
def prefixEnd_640375 : Nat := 4983230072969 + 3 ^ 40 * 640375 * 2
def baseEnd_640375 : Nat := 292284599220477567615533

theorem tailTrace_640375 : CollatzResearch.WordTrace tailWord_640375 prefixEnd_640375 292284599220477567615533 := by
  unfold tailWord_640375
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356395055038217187930579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15570930036692144791953719 23356395055038217187930579)
  ·
    refine ⟨35034592582557325781895869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23356395055038217187930579 35034592582557325781895869)
    ·
      refine ⟨13137972218458997168210951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35034592582557325781895869 13137972218458997168210951)
      ·
        refine ⟨19706958327688495752316427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13137972218458997168210951 19706958327688495752316427)
        ·
          refine ⟨29560437491532743628474641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19706958327688495752316427 29560437491532743628474641)
          ·
            refine ⟨22170328118649557721355981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29560437491532743628474641 22170328118649557721355981)
            ·
              refine ⟨8313873044493584145508493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22170328118649557721355981 8313873044493584145508493)
              ·
                refine ⟨3117702391685094054565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8313873044493584145508493 3117702391685094054565685)
                ·
                  refine ⟨292284599220477567615533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117702391685094054565685 292284599220477567615533)
                  ·
                    rfl

theorem cell20_640375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_640375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640375 prefixEnd_640375 := by exact prefixLift 640375
  have htrace : WordTrace (prefixWord ++ tailWord_640375) baseStart_640375 baseEnd_640375 := by
    simpa [prefixWord, tailWord_640375, baseEnd_640375] using wordTrace_append hprefix tailTrace_640375
  have hstable : (prefixWord ++ tailWord_640375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640375).length < 2 ^ (prefixWord ++ tailWord_640375).sum := by decide
  have hdescent : baseEnd_640375 < baseStart_640375 := by decide
  rcases family_descends (prefixWord ++ tailWord_640375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640388 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_640388 : Nat := 118140960795 + 640388 * 2 ^ 59
def prefixEnd_640388 : Nat := 4983230072969 + 3 ^ 40 * 640388 * 2
def baseEnd_640388 : Nat := 292290532774707300182147

theorem tailTrace_640388 : CollatzResearch.WordTrace tailWord_640388 prefixEnd_640388 292290532774707300182147 := by
  unfold tailWord_640388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678434601995560204076909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15571246135994080272102545 11678434601995560204076909)
  ·
    refine ⟨4379412975748335076528841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11678434601995560204076909 4379412975748335076528841)
    ·
      refine ⟨3284559731811251307396631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4379412975748335076528841 3284559731811251307396631)
      ·
        refine ⟨4926839597716876961094947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3284559731811251307396631 4926839597716876961094947)
        ·
          refine ⟨7390259396575315441642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926839597716876961094947 7390259396575315441642421)
          ·
            refine ⟨692836818428935822653977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7390259396575315441642421 692836818428935822653977)
            ·
              refine ⟨519627613821701866990483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692836818428935822653977 519627613821701866990483)
              ·
                refine ⟨779441420732552800485725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519627613821701866990483 779441420732552800485725)
                ·
                  refine ⟨292290532774707300182147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779441420732552800485725 292290532774707300182147)
                  ·
                    rfl

theorem cell20_640388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_640388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640388 prefixEnd_640388 := by exact prefixLift 640388
  have htrace : WordTrace (prefixWord ++ tailWord_640388) baseStart_640388 baseEnd_640388 := by
    simpa [prefixWord, tailWord_640388, baseEnd_640388] using wordTrace_append hprefix tailTrace_640388
  have hstable : (prefixWord ++ tailWord_640388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640388).length < 2 ^ (prefixWord ++ tailWord_640388).sum := by decide
  have hdescent : baseEnd_640388 < baseStart_640388 := by decide
  rcases family_descends (prefixWord ++ tailWord_640388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640416 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_640416 : Nat := 118140960795 + 640416 * 2 ^ 59
def prefixEnd_640416 : Nat := 4983230072969 + 3 ^ 40 * 640416 * 2
def baseEnd_640416 : Nat := 292303312737663647248699

theorem tailTrace_640416 : CollatzResearch.WordTrace tailWord_640416 prefixEnd_640416 292303312737663647248699 := by
  unfold tailWord_640416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678945223944840595086551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15571926965259787460115401 11678945223944840595086551)
  ·
    refine ⟨17518417835917260892629827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11678945223944840595086551 17518417835917260892629827)
    ·
      refine ⟨26277626753875891338944741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518417835917260892629827 26277626753875891338944741)
      ·
        refine ⟨4927055016351729626052139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26277626753875891338944741 4927055016351729626052139)
        ·
          refine ⟨7390582524527594439078209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927055016351729626052139 7390582524527594439078209)
          ·
            refine ⟨5542936893395695829308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7390582524527594439078209 5542936893395695829308657)
            ·
              refine ⟨4157202670046771871981493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542936893395695829308657 4157202670046771871981493)
              ·
                refine ⟨389737750316884862998265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4157202670046771871981493 389737750316884862998265)
                ·
                  refine ⟨292303312737663647248699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389737750316884862998265 292303312737663647248699)
                  ·
                    rfl

theorem cell20_640416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_640416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640416 prefixEnd_640416 := by exact prefixLift 640416
  have htrace : WordTrace (prefixWord ++ tailWord_640416) baseStart_640416 baseEnd_640416 := by
    simpa [prefixWord, tailWord_640416, baseEnd_640416] using wordTrace_append hprefix tailTrace_640416
  have hstable : (prefixWord ++ tailWord_640416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640416).length < 2 ^ (prefixWord ++ tailWord_640416).sum := by decide
  have hdescent : baseEnd_640416 < baseStart_640416 := by decide
  rcases family_descends (prefixWord ++ tailWord_640416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640429 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 2]
def baseStart_640429 : Nat := 118140960795 + 640429 * 2 ^ 59
def prefixEnd_640429 : Nat := 4983230072969 + 3 ^ 40 * 640429 * 2
def baseEnd_640429 : Nat := 292309246291893379815313

theorem tailTrace_640429 : CollatzResearch.WordTrace tailWord_640429 prefixEnd_640429 292309246291893379815313 := by
  unfold tailWord_640429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358364596842584410396341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15572243064561722940264227 23358364596842584410396341)
  ·
    refine ⟨2189846680953992288474657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23358364596842584410396341 2189846680953992288474657)
    ·
      refine ⟨1642385010715494216355993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189846680953992288474657 1642385010715494216355993)
      ·
        refine ⟨1231788758036620662266995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642385010715494216355993 1231788758036620662266995)
        ·
          refine ⟨1847683137054930993400493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231788758036620662266995 1847683137054930993400493)
          ·
            refine ⟨692881176395599122525185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1847683137054930993400493 692881176395599122525185)
            ·
              refine ⟨519660882296699341893889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692881176395599122525185 519660882296699341893889)
              ·
                refine ⟨389745661722524506420417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519660882296699341893889 389745661722524506420417)
                ·
                  refine ⟨292309246291893379815313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389745661722524506420417 292309246291893379815313)
                  ·
                    rfl

theorem cell20_640429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_640429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640429 prefixEnd_640429 := by exact prefixLift 640429
  have htrace : WordTrace (prefixWord ++ tailWord_640429) baseStart_640429 baseEnd_640429 := by
    simpa [prefixWord, tailWord_640429, baseEnd_640429] using wordTrace_append hprefix tailTrace_640429
  have hstable : (prefixWord ++ tailWord_640429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640429).length < 2 ^ (prefixWord ++ tailWord_640429).sum := by decide
  have hdescent : baseEnd_640429 < baseStart_640429 := by decide
  rcases family_descends (prefixWord ++ tailWord_640429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640485 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_640485 : Nat := 118140960795 + 640485 * 2 ^ 59
def prefixEnd_640485 : Nat := 4983230072969 + 3 ^ 40 * 640485 * 2
def baseEnd_640485 : Nat := 292334806217806073948417

theorem tailTrace_640485 : CollatzResearch.WordTrace tailWord_640485 prefixEnd_640485 292334806217806073948417 := by
  unfold tailWord_640485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23360407084639705974434909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15573604723093137316289939 23360407084639705974434909)
  ·
    refine ⟨8760152656739889740413091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23360407084639705974434909 8760152656739889740413091)
    ·
      refine ⟨13140228985109834610619637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8760152656739889740413091 13140228985109834610619637)
      ·
        refine ⟨1231896467354046994745591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13140228985109834610619637 1231896467354046994745591)
        ·
          refine ⟨1847844701031070492118387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231896467354046994745591 1847844701031070492118387)
          ·
            refine ⟨2771767051546605738177581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847844701031070492118387 2771767051546605738177581)
            ·
              refine ⟨1039412644329977151816593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2771767051546605738177581 1039412644329977151816593)
              ·
                refine ⟨779559483247482863862445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039412644329977151816593 779559483247482863862445)
                ·
                  refine ⟨292334806217806073948417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779559483247482863862445 292334806217806073948417)
                  ·
                    rfl

theorem cell20_640485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_640485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640485 prefixEnd_640485 := by exact prefixLift 640485
  have htrace : WordTrace (prefixWord ++ tailWord_640485) baseStart_640485 baseEnd_640485 := by
    simpa [prefixWord, tailWord_640485, baseEnd_640485] using wordTrace_append hprefix tailTrace_640485
  have hstable : (prefixWord ++ tailWord_640485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640485).length < 2 ^ (prefixWord ++ tailWord_640485).sum := by decide
  have hdescent : baseEnd_640485 < baseStart_640485 := by decide
  rcases family_descends (prefixWord ++ tailWord_640485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640502 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_640502 : Nat := 118140960795 + 640502 * 2 ^ 59
def prefixEnd_640502 : Nat := 4983230072969 + 3 ^ 40 * 640502 * 2
def baseEnd_640502 : Nat := 292342565481029570381681

theorem tailTrace_640502 : CollatzResearch.WordTrace tailWord_640502 prefixEnd_640502 292342565481029570381681 := by
  unfold tailWord_640502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460064195348632367362735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15574018083718745251869173 1460064195348632367362735)
  ·
    refine ⟨2190096293022948551044103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460064195348632367362735 2190096293022948551044103)
    ·
      refine ⟨3285144439534422826566155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190096293022948551044103 3285144439534422826566155)
      ·
        refine ⟨4927716659301634239849233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285144439534422826566155 4927716659301634239849233)
        ·
          refine ⟨3695787494476225679886925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927716659301634239849233 3695787494476225679886925)
          ·
            refine ⟨1385920310428584629957597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3695787494476225679886925 1385920310428584629957597)
            ·
              refine ⟨519720116410719236234099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385920310428584629957597 519720116410719236234099)
              ·
                refine ⟨779580174616078854351149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519720116410719236234099 779580174616078854351149)
                ·
                  refine ⟨292342565481029570381681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779580174616078854351149 292342565481029570381681)
                  ·
                    rfl

theorem cell20_640502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_640502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640502 prefixEnd_640502 := by exact prefixLift 640502
  have htrace : WordTrace (prefixWord ++ tailWord_640502) baseStart_640502 baseEnd_640502 := by
    simpa [prefixWord, tailWord_640502, baseEnd_640502] using wordTrace_append hprefix tailTrace_640502
  have hstable : (prefixWord ++ tailWord_640502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640502).length < 2 ^ (prefixWord ++ tailWord_640502).sum := by decide
  have hdescent : baseEnd_640502 < baseStart_640502 := by decide
  rcases family_descends (prefixWord ++ tailWord_640502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640526 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_640526 : Nat := 118140960795 + 640526 * 2 ^ 59
def prefixEnd_640526 : Nat := 4983230072969 + 3 ^ 40 * 640526 * 2
def baseEnd_640526 : Nat := 292353519734992153581583

theorem tailTrace_640526 : CollatzResearch.WordTrace tailWord_640526 prefixEnd_640526 292353519734992153581583 := by
  unfold tailWord_640526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2920237809686396247084679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15574601651660779984451621 2920237809686396247084679)
  ·
    refine ⟨4380356714529594370627019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2920237809686396247084679 4380356714529594370627019)
    ·
      refine ⟨6570535071794391555940529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380356714529594370627019 6570535071794391555940529)
      ·
        refine ⟨4927901303845793666955397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6570535071794391555940529 4927901303845793666955397)
        ·
          refine ⟨923981494471086312554137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4927901303845793666955397 923981494471086312554137)
          ·
            refine ⟨692986120853314734415603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923981494471086312554137 692986120853314734415603)
            ·
              refine ⟨1039479181279972101623405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692986120853314734415603 1039479181279972101623405)
              ·
                refine ⟨389804692979989538108777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1039479181279972101623405 389804692979989538108777)
                ·
                  refine ⟨292353519734992153581583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389804692979989538108777 292353519734992153581583)
                  ·
                    rfl

theorem cell20_640526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_640526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640526 prefixEnd_640526 := by exact prefixLift 640526
  have htrace : WordTrace (prefixWord ++ tailWord_640526) baseStart_640526 baseEnd_640526 := by
    simpa [prefixWord, tailWord_640526, baseEnd_640526] using wordTrace_append hprefix tailTrace_640526
  have hstable : (prefixWord ++ tailWord_640526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640526).length < 2 ^ (prefixWord ++ tailWord_640526).sum := by decide
  have hdescent : baseEnd_640526 < baseStart_640526 := by decide
  rcases family_descends (prefixWord ++ tailWord_640526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640544 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_640544 : Nat := 118140960795 + 640544 * 2 ^ 59
def prefixEnd_640544 : Nat := 4983230072969 + 3 ^ 40 * 640544 * 2
def baseEnd_640544 : Nat := 292361735425464090981509

theorem tailTrace_640544 : CollatzResearch.WordTrace tailWord_640544 prefixEnd_640544 292361735425464090981509 := by
  unfold tailWord_640544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681279495712979525416343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15575039327617306033888457 11681279495712979525416343)
  ·
    refine ⟨17521919243569469288124515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11681279495712979525416343 17521919243569469288124515)
    ·
      refine ⟨26282878865354203932186773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17521919243569469288124515 26282878865354203932186773)
      ·
        refine ⟨1232009946813478309321255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26282878865354203932186773 1232009946813478309321255)
        ·
          refine ⟨1848014920220217463981883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232009946813478309321255 1848014920220217463981883)
          ·
            refine ⟨2772022380330326195972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848014920220217463981883 2772022380330326195972825)
            ·
              refine ⟨2079016785247744646979619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772022380330326195972825 2079016785247744646979619)
              ·
                refine ⟨3118525177871616970469429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079016785247744646979619 3118525177871616970469429)
                ·
                  refine ⟨292361735425464090981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118525177871616970469429 292361735425464090981509)
                  ·
                    rfl

theorem cell20_640544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_640544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640544 prefixEnd_640544 := by exact prefixLift 640544
  have htrace : WordTrace (prefixWord ++ tailWord_640544) baseStart_640544 baseEnd_640544 := by
    simpa [prefixWord, tailWord_640544, baseEnd_640544] using wordTrace_append hprefix tailTrace_640544
  have hstable : (prefixWord ++ tailWord_640544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640544).length < 2 ^ (prefixWord ++ tailWord_640544).sum := by decide
  have hdescent : baseEnd_640544 < baseStart_640544 := by decide
  rcases family_descends (prefixWord ++ tailWord_640544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640547 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 4]
def baseStart_640547 : Nat := 118140960795 + 640547 * 2 ^ 59
def prefixEnd_640547 : Nat := 4983230072969 + 3 ^ 40 * 640547 * 2
def baseEnd_640547 : Nat := 292363104707209413881497

theorem tailTrace_640547 : CollatzResearch.WordTrace tailWord_640547 prefixEnd_640547 292363104707209413881497 := by
  unfold tailWord_640547
  simp only [CollatzResearch.WordTrace]
  refine ⟨23362668410415090563191895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15575112273610060375461263 23362668410415090563191895)
  ·
    refine ⟨35044002615622635844787843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23362668410415090563191895 35044002615622635844787843)
    ·
      refine ⟨52566003923433953767181765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35044002615622635844787843 52566003923433953767181765)
      ·
        refine ⟨9856125735643866331346581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52566003923433953767181765 9856125735643866331346581)
        ·
          refine ⟨462005893858306234281871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9856125735643866331346581 462005893858306234281871)
          ·
            refine ⟨693008840787459351422807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462005893858306234281871 693008840787459351422807)
            ·
              refine ⟨1039513261181189027134211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693008840787459351422807 1039513261181189027134211)
              ·
                refine ⟨1559269891771783540701317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039513261181189027134211 1559269891771783540701317)
                ·
                  refine ⟨292363104707209413881497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1559269891771783540701317 292363104707209413881497)
                  ·
                    rfl

theorem cell20_640547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4].length) (baseStart_640547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640547 prefixEnd_640547 := by exact prefixLift 640547
  have htrace : WordTrace (prefixWord ++ tailWord_640547) baseStart_640547 baseEnd_640547 := by
    simpa [prefixWord, tailWord_640547, baseEnd_640547] using wordTrace_append hprefix tailTrace_640547
  have hstable : (prefixWord ++ tailWord_640547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640547).length < 2 ^ (prefixWord ++ tailWord_640547).sum := by decide
  have hdescent : baseEnd_640547 < baseStart_640547 := by decide
  rcases family_descends (prefixWord ++ tailWord_640547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640613 : List Nat := [1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_640613 : Nat := 118140960795 + 640613 * 2 ^ 59
def prefixEnd_640613 : Nat := 4983230072969 + 3 ^ 40 * 640613 * 2
def baseEnd_640613 : Nat := 97464409635202172560409

theorem tailTrace_640613 : CollatzResearch.WordTrace tailWord_640613 prefixEnd_640613 97464409635202172560409 := by
  unfold tailWord_640613
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365075628175983835094493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15576717085450655890062995 23365075628175983835094493)
  ·
    refine ⟨8761903360565993938160435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23365075628175983835094493 8761903360565993938160435)
    ·
      refine ⟨13142855040848990907240653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8761903360565993938160435 13142855040848990907240653)
      ·
        refine ⟨4928570640318371590215245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13142855040848990907240653 4928570640318371590215245)
        ·
          refine ⟨1848213990119389346330717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928570640318371590215245 1848213990119389346330717)
          ·
            refine ⟨693080246294771004874019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1848213990119389346330717 693080246294771004874019)
            ·
              refine ⟨1039620369442156507311029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693080246294771004874019 1039620369442156507311029)
              ·
                refine ⟨97464409635202172560409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1039620369442156507311029 97464409635202172560409)
                ·
                  rfl

theorem cell20_640613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_640613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640613 prefixEnd_640613 := by exact prefixLift 640613
  have htrace : WordTrace (prefixWord ++ tailWord_640613) baseStart_640613 baseEnd_640613 := by
    simpa [prefixWord, tailWord_640613, baseEnd_640613] using wordTrace_append hprefix tailTrace_640613
  have hstable : (prefixWord ++ tailWord_640613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640613).length < 2 ^ (prefixWord ++ tailWord_640613).sum := by decide
  have hdescent : baseEnd_640613 < baseStart_640613 := by decide
  rcases family_descends (prefixWord ++ tailWord_640613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640630 : List Nat := [5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_640630 : Nat := 118140960795 + 640630 * 2 ^ 59
def prefixEnd_640630 : Nat := 4983230072969 + 3 ^ 40 * 640630 * 2
def baseEnd_640630 : Nat := 97466996056276671371497

theorem tailTrace_640630 : CollatzResearch.WordTrace tailWord_640630 prefixEnd_640630 97466996056276671371497 := by
  unfold tailWord_640630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460355979319649733653959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15577130446076263825642229 1460355979319649733653959)
  ·
    refine ⟨2190533968979474600480939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460355979319649733653959 2190533968979474600480939)
    ·
      refine ⟨3285800953469211900721409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190533968979474600480939 3285800953469211900721409)
      ·
        refine ⟨2464350715101908925541057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285800953469211900721409 2464350715101908925541057)
        ·
          refine ⟨1848263036326431694155793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464350715101908925541057 1848263036326431694155793)
          ·
            refine ⟨1386197277244823770616845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848263036326431694155793 1386197277244823770616845)
            ·
              refine ⟨519823978966808913981317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386197277244823770616845 519823978966808913981317)
              ·
                refine ⟨97466996056276671371497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519823978966808913981317 97466996056276671371497)
                ·
                  rfl

theorem cell20_640630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_640630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640630 prefixEnd_640630 := by exact prefixLift 640630
  have htrace : WordTrace (prefixWord ++ tailWord_640630) baseStart_640630 baseEnd_640630 := by
    simpa [prefixWord, tailWord_640630, baseEnd_640630] using wordTrace_append hprefix tailTrace_640630
  have hstable : (prefixWord ++ tailWord_640630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640630).length < 2 ^ (prefixWord ++ tailWord_640630).sum := by decide
  have hdescent : baseEnd_640630 < baseStart_640630 := by decide
  rcases family_descends (prefixWord ++ tailWord_640630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640716 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_640716 : Nat := 118140960795 + 640716 * 2 ^ 59
def prefixEnd_640716 : Nat := 4983230072969 + 3 ^ 40 * 640716 * 2
def baseEnd_640716 : Nat := 292440240912195937247473

theorem tailTrace_640716 : CollatzResearch.WordTrace tailWord_640716 prefixEnd_640716 292440240912195937247473 := by
  unfold tailWord_640716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684416173401416213047001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15579221564535221617396001 11684416173401416213047001)
  ·
    refine ⟨8763312130051062159785251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11684416173401416213047001 8763312130051062159785251)
    ·
      refine ⟨13144968195076593239677877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8763312130051062159785251 13144968195076593239677877)
      ·
        refine ⟨1232340768288430616219801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13144968195076593239677877 1232340768288430616219801)
        ·
          refine ⟨924255576216322962164851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232340768288430616219801 924255576216322962164851)
          ·
            refine ⟨1386383364324484443247277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924255576216322962164851 1386383364324484443247277)
            ·
              refine ⟨519893761621681666217729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386383364324484443247277 519893761621681666217729)
              ·
                refine ⟨389920321216261249663297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519893761621681666217729 389920321216261249663297)
                ·
                  refine ⟨292440240912195937247473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389920321216261249663297 292440240912195937247473)
                  ·
                    rfl

theorem cell20_640716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_640716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640716 prefixEnd_640716 := by exact prefixLift 640716
  have htrace : WordTrace (prefixWord ++ tailWord_640716) baseStart_640716 baseEnd_640716 := by
    simpa [prefixWord, tailWord_640716, baseEnd_640716] using wordTrace_append hprefix tailTrace_640716
  have hstable : (prefixWord ++ tailWord_640716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640716).length < 2 ^ (prefixWord ++ tailWord_640716).sum := by decide
  have hdescent : baseEnd_640716 < baseStart_640716 := by decide
  rcases family_descends (prefixWord ++ tailWord_640716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640726 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_640726 : Nat := 118140960795 + 640726 * 2 ^ 59
def prefixEnd_640726 : Nat := 4983230072969 + 3 ^ 40 * 640726 * 2
def baseEnd_640726 : Nat := 292444805184680346914099

theorem tailTrace_640726 : CollatzResearch.WordTrace tailWord_640726 prefixEnd_640726 292444805184680346914099 := by
  unfold tailWord_640726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460574817297912758372377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15579464717844402755972021 1460574817297912758372377)
  ·
    refine ⟨1095431112973434568779283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1460574817297912758372377 1095431112973434568779283)
    ·
      refine ⟨1643146669460151853168925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095431112973434568779283 1643146669460151853168925)
      ·
        refine ⟨616180001047556944938347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1643146669460151853168925 616180001047556944938347)
        ·
          refine ⟨924270001571335417407521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616180001047556944938347 924270001571335417407521)
          ·
            refine ⟨693202501178501563055641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924270001571335417407521 693202501178501563055641)
            ·
              refine ⟨519901875883876172291731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693202501178501563055641 519901875883876172291731)
              ·
                refine ⟨779852813825814258437597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519901875883876172291731 779852813825814258437597)
                ·
                  refine ⟨292444805184680346914099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779852813825814258437597 292444805184680346914099)
                  ·
                    rfl

theorem cell20_640726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_640726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640726 prefixEnd_640726 := by exact prefixLift 640726
  have htrace : WordTrace (prefixWord ++ tailWord_640726) baseStart_640726 baseEnd_640726 := by
    simpa [prefixWord, tailWord_640726, baseEnd_640726] using wordTrace_append hprefix tailTrace_640726
  have hstable : (prefixWord ++ tailWord_640726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640726).length < 2 ^ (prefixWord ++ tailWord_640726).sum := by decide
  have hdescent : baseEnd_640726 < baseStart_640726 := by decide
  rcases family_descends (prefixWord ++ tailWord_640726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640772 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_640772 : Nat := 118140960795 + 640772 * 2 ^ 59
def prefixEnd_640772 : Nat := 4983230072969 + 3 ^ 40 * 640772 * 2
def baseEnd_640772 : Nat := 292465800838108631380577

theorem tailTrace_640772 : CollatzResearch.WordTrace tailWord_640772 prefixEnd_640772 292465800838108631380577 := by
  unfold tailWord_640772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11685437417299976995066285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15580583223066635993421713 11685437417299976995066285)
  ·
    refine ⟨4382039031487491373149857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11685437417299976995066285 4382039031487491373149857)
    ·
      refine ⟨3286529273615618529862393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4382039031487491373149857 3286529273615618529862393)
      ·
        refine ⟨2464896955211713897396795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286529273615618529862393 2464896955211713897396795)
        ·
          refine ⟨3697345432817570846095193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464896955211713897396795 3697345432817570846095193)
          ·
            refine ⟨2773009074613178134571395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3697345432817570846095193 2773009074613178134571395)
            ·
              refine ⟨4159513611919767201857093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773009074613178134571395 4159513611919767201857093)
              ·
                refine ⟨779908802234956350348205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4159513611919767201857093 779908802234956350348205)
                ·
                  refine ⟨292465800838108631380577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779908802234956350348205 292465800838108631380577)
                  ·
                    rfl

theorem cell20_640772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_640772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640772 prefixEnd_640772 := by exact prefixLift 640772
  have htrace : WordTrace (prefixWord ++ tailWord_640772) baseStart_640772 baseEnd_640772 := by
    simpa [prefixWord, tailWord_640772, baseEnd_640772] using wordTrace_append hprefix tailTrace_640772
  have hstable : (prefixWord ++ tailWord_640772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640772).length < 2 ^ (prefixWord ++ tailWord_640772).sum := by decide
  have hdescent : baseEnd_640772 < baseStart_640772 := by decide
  rcases family_descends (prefixWord ++ tailWord_640772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640774 : List Nat := [6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_640774 : Nat := 118140960795 + 640774 * 2 ^ 59
def prefixEnd_640774 : Nat := 4983230072969 + 3 ^ 40 * 640774 * 2
def baseEnd_640774 : Nat := 97488904564201837771301

theorem tailTrace_640774 : CollatzResearch.WordTrace tailWord_640774 prefixEnd_640774 97488904564201837771301 := by
  unfold tailWord_640774
  simp only [CollatzResearch.WordTrace]
  refine ⟨730342118143522135365793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15580631853728472221136917 730342118143522135365793)
  ·
    refine ⟨547756588607641601524345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 730342118143522135365793 547756588607641601524345)
    ·
      refine ⟨410817441455731201143259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547756588607641601524345 410817441455731201143259)
      ·
        refine ⟨616226162183596801714889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410817441455731201143259 616226162183596801714889)
        ·
          refine ⟨462169621637697601286167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616226162183596801714889 462169621637697601286167)
          ·
            refine ⟨693254432456546401929251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462169621637697601286167 693254432456546401929251)
            ·
              refine ⟨1039881648684819602893877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693254432456546401929251 1039881648684819602893877)
              ·
                refine ⟨97488904564201837771301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1039881648684819602893877 97488904564201837771301)
                ·
                  rfl

theorem cell20_640774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_640774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640774 prefixEnd_640774 := by exact prefixLift 640774
  have htrace : WordTrace (prefixWord ++ tailWord_640774) baseStart_640774 baseEnd_640774 := by
    simpa [prefixWord, tailWord_640774, baseEnd_640774] using wordTrace_append hprefix tailTrace_640774
  have hstable : (prefixWord ++ tailWord_640774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640774).length < 2 ^ (prefixWord ++ tailWord_640774).sum := by decide
  have hdescent : baseEnd_640774 < baseStart_640774 := by decide
  rcases family_descends (prefixWord ++ tailWord_640774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640775 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 2]
def baseStart_640775 : Nat := 118140960795 + 640775 * 2 ^ 59
def prefixEnd_640775 : Nat := 4983230072969 + 3 ^ 40 * 640775 * 2
def baseEnd_640775 : Nat := 292467170119853954280565

theorem tailTrace_640775 : CollatzResearch.WordTrace tailWord_640775 prefixEnd_640775 292467170119853954280565 := by
  unfold tailWord_640775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23370984253589085502491779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15580656169059390334994519 23370984253589085502491779)
  ·
    refine ⟨35056476380383628253737669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23370984253589085502491779 35056476380383628253737669)
    ·
      refine ⟨6573089321321930297575813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35056476380383628253737669 6573089321321930297575813)
      ·
        refine ⟨1232454247747861930795465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6573089321321930297575813 1232454247747861930795465)
        ·
          refine ⟨924340685810896448096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232454247747861930795465 924340685810896448096599)
          ·
            refine ⟨1386511028716344672144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924340685810896448096599 1386511028716344672144899)
            ·
              refine ⟨2079766543074517008217349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386511028716344672144899 2079766543074517008217349)
              ·
                refine ⟨389956226826471939040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2079766543074517008217349 389956226826471939040753)
                ·
                  refine ⟨292467170119853954280565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389956226826471939040753 292467170119853954280565)
                  ·
                    rfl

theorem cell20_640775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2].length) (baseStart_640775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640775 prefixEnd_640775 := by exact prefixLift 640775
  have htrace : WordTrace (prefixWord ++ tailWord_640775) baseStart_640775 baseEnd_640775 := by
    simpa [prefixWord, tailWord_640775, baseEnd_640775] using wordTrace_append hprefix tailTrace_640775
  have hstable : (prefixWord ++ tailWord_640775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640775).length < 2 ^ (prefixWord ++ tailWord_640775).sum := by decide
  have hdescent : baseEnd_640775 < baseStart_640775 := by decide
  rcases family_descends (prefixWord ++ tailWord_640775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640868 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_640868 : Nat := 118140960795 + 640868 * 2 ^ 59
def prefixEnd_640868 : Nat := 4983230072969 + 3 ^ 40 * 640868 * 2
def baseEnd_640868 : Nat := 292509617853958964180185

theorem tailTrace_640868 : CollatzResearch.WordTrace tailWord_640868 prefixEnd_640868 292509617853958964180185 := by
  unfold tailWord_640868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687188121126081192813629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15582917494834774923751505 11687188121126081192813629)
  ·
    refine ⟨4382695545422280447305111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11687188121126081192813629 4382695545422280447305111)
    ·
      refine ⟨6574043318133420670957667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382695545422280447305111 6574043318133420670957667)
      ·
        refine ⟨9861064977200131006436501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574043318133420670957667 9861064977200131006436501)
        ·
          refine ⟨462237420806256140926711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9861064977200131006436501 462237420806256140926711)
          ·
            refine ⟨693356131209384211390067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462237420806256140926711 693356131209384211390067)
            ·
              refine ⟨1040034196814076317085101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693356131209384211390067 1040034196814076317085101)
              ·
                refine ⟨390012823805278618906913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040034196814076317085101 390012823805278618906913)
                ·
                  refine ⟨292509617853958964180185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390012823805278618906913 292509617853958964180185)
                  ·
                    rfl

theorem cell20_640868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_640868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640868 prefixEnd_640868 := by exact prefixLift 640868
  have htrace : WordTrace (prefixWord ++ tailWord_640868) baseStart_640868 baseEnd_640868 := by
    simpa [prefixWord, tailWord_640868, baseEnd_640868] using wordTrace_append hprefix tailTrace_640868
  have hstable : (prefixWord ++ tailWord_640868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640868).length < 2 ^ (prefixWord ++ tailWord_640868).sum := by decide
  have hdescent : baseEnd_640868 < baseStart_640868 := by decide
  rcases family_descends (prefixWord ++ tailWord_640868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640921 : List Nat := [1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_640921 : Nat := 118140960795 + 640921 * 2 ^ 59
def prefixEnd_640921 : Nat := 4983230072969 + 3 ^ 40 * 640921 * 2
def baseEnd_640921 : Nat := 97511269499375445137767

theorem tailTrace_640921 : CollatzResearch.WordTrace tailWord_640921 prefixEnd_640921 97511269499375445137767 := by
  unfold tailWord_640921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376309311060152437306617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15584206207373434958204411 23376309311060152437306617)
  ·
    refine ⟨17532231983295114327979963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23376309311060152437306617 17532231983295114327979963)
    ·
      refine ⟨26298347974942671491969945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17532231983295114327979963 26298347974942671491969945)
      ·
        refine ⟨19723760981207003618977459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26298347974942671491969945 19723760981207003618977459)
        ·
          refine ⟨29585641471810505428466189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19723760981207003618977459 29585641471810505428466189)
          ·
            refine ⟨11094615551928939535674821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29585641471810505428466189 11094615551928939535674821)
            ·
              refine ⟨2080240415986676162939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11094615551928939535674821 2080240415986676162939029)
              ·
                refine ⟨97511269499375445137767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2080240415986676162939029 97511269499375445137767)
                ·
                  rfl

theorem cell20_640921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_640921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640921 prefixEnd_640921 := by exact prefixLift 640921
  have htrace : WordTrace (prefixWord ++ tailWord_640921) baseStart_640921 baseEnd_640921 := by
    simpa [prefixWord, tailWord_640921, baseEnd_640921] using wordTrace_append hprefix tailTrace_640921
  have hstable : (prefixWord ++ tailWord_640921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640921).length < 2 ^ (prefixWord ++ tailWord_640921).sum := by decide
  have hdescent : baseEnd_640921 < baseStart_640921 := by decide
  rcases family_descends (prefixWord ++ tailWord_640921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640931 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 2]
def baseStart_640931 : Nat := 118140960795 + 640931 * 2 ^ 59
def prefixEnd_640931 : Nat := 4983230072969 + 3 ^ 40 * 640931 * 2
def baseEnd_640931 : Nat := 292538372770610745079927

theorem tailTrace_640931 : CollatzResearch.WordTrace tailWord_640931 prefixEnd_640931 292538372770610745079927 := by
  unfold tailWord_640931
  simp only [CollatzResearch.WordTrace]
  refine ⟨23376674041023924145170647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15584449360682616096780431 23376674041023924145170647)
  ·
    refine ⟨35065011061535886217755971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23376674041023924145170647 35065011061535886217755971)
    ·
      refine ⟨52597516592303829326633957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35065011061535886217755971 52597516592303829326633957)
      ·
        refine ⟨9862034361056967998743867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52597516592303829326633957 9862034361056967998743867)
        ·
          refine ⟨14793051541585451998115801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9862034361056967998743867 14793051541585451998115801)
          ·
            refine ⟨11094788656189088998586851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14793051541585451998115801 11094788656189088998586851)
            ·
              refine ⟨16642182984283633497880277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11094788656189088998586851 16642182984283633497880277)
              ·
                refine ⟨390051163694147660106569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16642182984283633497880277 390051163694147660106569)
                ·
                  refine ⟨292538372770610745079927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390051163694147660106569 292538372770610745079927)
                  ·
                    rfl

theorem cell20_640931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 2].length) (baseStart_640931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640931 prefixEnd_640931 := by exact prefixLift 640931
  have htrace : WordTrace (prefixWord ++ tailWord_640931) baseStart_640931 baseEnd_640931 := by
    simpa [prefixWord, tailWord_640931, baseEnd_640931] using wordTrace_append hprefix tailTrace_640931
  have hstable : (prefixWord ++ tailWord_640931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640931).length < 2 ^ (prefixWord ++ tailWord_640931).sum := by decide
  have hdescent : baseEnd_640931 < baseStart_640931 := by decide
  rcases family_descends (prefixWord ++ tailWord_640931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640952 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_640952 : Nat := 118140960795 + 640952 * 2 ^ 59
def prefixEnd_640952 : Nat := 4983230072969 + 3 ^ 40 * 640952 * 2
def baseEnd_640952 : Nat := 292547957742828005379841

theorem tailTrace_640952 : CollatzResearch.WordTrace tailWord_640952 prefixEnd_640952 292547957742828005379841 := by
  unfold tailWord_640952
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688719986973922365842555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15584959982631896487790073 11688719986973922365842555)
  ·
    refine ⟨17533079980460883548763833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688719986973922365842555 17533079980460883548763833)
    ·
      refine ⟨13149809985345662661572875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17533079980460883548763833 13149809985345662661572875)
      ·
        refine ⟨19724714978018493992359313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149809985345662661572875 19724714978018493992359313)
        ·
          refine ⟨14793536233513870494269485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19724714978018493992359313 14793536233513870494269485)
          ·
            refine ⟨5547576087567701435351057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14793536233513870494269485 5547576087567701435351057)
            ·
              refine ⟨4160682065675776076513293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5547576087567701435351057 4160682065675776076513293)
              ·
                refine ⟨1560255774628416028692485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4160682065675776076513293 1560255774628416028692485)
                ·
                  refine ⟨292547957742828005379841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560255774628416028692485 292547957742828005379841)
                  ·
                    rfl

theorem cell20_640952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_640952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640952 prefixEnd_640952 := by exact prefixLift 640952
  have htrace : WordTrace (prefixWord ++ tailWord_640952) baseStart_640952 baseEnd_640952 := by
    simpa [prefixWord, tailWord_640952, baseEnd_640952] using wordTrace_append hprefix tailTrace_640952
  have hstable : (prefixWord ++ tailWord_640952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640952).length < 2 ^ (prefixWord ++ tailWord_640952).sum := by decide
  have hdescent : baseEnd_640952 < baseStart_640952 := by decide
  rcases family_descends (prefixWord ++ tailWord_640952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640982 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_640982 : Nat := 118140960795 + 640982 * 2 ^ 59
def prefixEnd_640982 : Nat := 4983230072969 + 3 ^ 40 * 640982 * 2
def baseEnd_640982 : Nat := 292561650560281234379719

theorem tailTrace_640982 : CollatzResearch.WordTrace tailWord_640982 prefixEnd_640982 292561650560281234379719 := by
  unfold tailWord_640982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461158385239947490954825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15585689442559439903518133 1461158385239947490954825)
  ·
    refine ⟨1095868788929960618216119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1461158385239947490954825 1095868788929960618216119)
    ·
      refine ⟨1643803183394940927324179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095868788929960618216119 1643803183394940927324179)
      ·
        refine ⟨2465704775092411390986269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643803183394940927324179 2465704775092411390986269)
        ·
          refine ⟨924639290659654271619851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2465704775092411390986269 924639290659654271619851)
          ·
            refine ⟨1386958935989481407429777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924639290659654271619851 1386958935989481407429777)
            ·
              refine ⟨1040219201992111055572333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386958935989481407429777 1040219201992111055572333)
              ·
                refine ⟨390082200747041645839625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040219201992111055572333 390082200747041645839625)
                ·
                  refine ⟨292561650560281234379719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390082200747041645839625 292561650560281234379719)
                  ·
                    rfl

theorem cell20_640982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_640982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_640982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_640982 prefixEnd_640982 := by exact prefixLift 640982
  have htrace : WordTrace (prefixWord ++ tailWord_640982) baseStart_640982 baseEnd_640982 := by
    simpa [prefixWord, tailWord_640982, baseEnd_640982] using wordTrace_append hprefix tailTrace_640982
  have hstable : (prefixWord ++ tailWord_640982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640982).length < 2 ^ (prefixWord ++ tailWord_640982).sum := by decide
  have hdescent : baseEnd_640982 < baseStart_640982 := by decide
  rcases family_descends (prefixWord ++ tailWord_640982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641007 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 2]
def baseStart_641007 : Nat := 118140960795 + 641007 * 2 ^ 59
def prefixEnd_641007 : Nat := 4983230072969 + 3 ^ 40 * 641007 * 2
def baseEnd_641007 : Nat := 292573061241492258546283

theorem tailTrace_641007 : CollatzResearch.WordTrace tailWord_641007 prefixEnd_641007 292573061241492258546283 := by
  unfold tailWord_641007
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379445988748589124937275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15586297325832392749958183 23379445988748589124937275)
  ·
    refine ⟨35069168983122883687405913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23379445988748589124937275 35069168983122883687405913)
    ·
      refine ⟨26301876737342162765554435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35069168983122883687405913 26301876737342162765554435)
      ·
        refine ⟨39452815106013244148331653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26301876737342162765554435 39452815106013244148331653)
        ·
          refine ⟨7397402832377483277812185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39452815106013244148331653 7397402832377483277812185)
          ·
            refine ⟨5548052124283112458359139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7397402832377483277812185 5548052124283112458359139)
            ·
              refine ⟨8322078186424668687538709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5548052124283112458359139 8322078186424668687538709)
              ·
                refine ⟨390097414988656344728377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8322078186424668687538709 390097414988656344728377)
                ·
                  refine ⟨292573061241492258546283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390097414988656344728377 292573061241492258546283)
                  ·
                    rfl

theorem cell20_641007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 2].length) (baseStart_641007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641007 prefixEnd_641007 := by exact prefixLift 641007
  have htrace : WordTrace (prefixWord ++ tailWord_641007) baseStart_641007 baseEnd_641007 := by
    simpa [prefixWord, tailWord_641007, baseEnd_641007] using wordTrace_append hprefix tailTrace_641007
  have hstable : (prefixWord ++ tailWord_641007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641007).length < 2 ^ (prefixWord ++ tailWord_641007).sum := by decide
  have hdescent : baseEnd_641007 < baseStart_641007 := by decide
  rcases family_descends (prefixWord ++ tailWord_641007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641021 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_641021 : Nat := 118140960795 + 641021 * 2 ^ 59
def prefixEnd_641021 : Nat := 4983230072969 + 3 ^ 40 * 641021 * 2
def baseEnd_641021 : Nat := 292579451222970432079559

theorem tailTrace_641021 : CollatzResearch.WordTrace tailWord_641021 prefixEnd_641021 292579451222970432079559 := by
  unfold tailWord_641021
  simp only [CollatzResearch.WordTrace]
  refine ⟨23379956610697869515946917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15586637740465246343964611 23379956610697869515946917)
  ·
    refine ⟨4383741864505850534240047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23379956610697869515946917 4383741864505850534240047)
    ·
      refine ⟨6575612796758775801360071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383741864505850534240047 6575612796758775801360071)
      ·
        refine ⟨9863419195138163702040107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6575612796758775801360071 9863419195138163702040107)
        ·
          refine ⟨14795128792707245553060161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9863419195138163702040107 14795128792707245553060161)
          ·
            refine ⟨11096346594530434164795121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14795128792707245553060161 11096346594530434164795121)
            ·
              refine ⟨8322259945897825623596341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11096346594530434164795121 8322259945897825623596341)
              ·
                refine ⟨780211869927921152212157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8322259945897825623596341 780211869927921152212157)
                ·
                  refine ⟨292579451222970432079559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780211869927921152212157 292579451222970432079559)
                  ·
                    rfl

theorem cell20_641021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_641021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641021 prefixEnd_641021 := by exact prefixLift 641021
  have htrace : WordTrace (prefixWord ++ tailWord_641021) baseStart_641021 baseEnd_641021 := by
    simpa [prefixWord, tailWord_641021, baseEnd_641021] using wordTrace_append hprefix tailTrace_641021
  have hstable : (prefixWord ++ tailWord_641021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641021).length < 2 ^ (prefixWord ++ tailWord_641021).sum := by decide
  have hdescent : baseEnd_641021 < baseStart_641021 := by decide
  rcases family_descends (prefixWord ++ tailWord_641021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641031 : List Nat := [1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_641031 : Nat := 118140960795 + 641031 * 2 ^ 59
def prefixEnd_641031 : Nat := 4983230072969 + 3 ^ 40 * 641031 * 2
def baseEnd_641031 : Nat := 97528005165151613915395

theorem tailTrace_641031 : CollatzResearch.WordTrace tailWord_641031 prefixEnd_641031 97528005165151613915395 := by
  unfold tailWord_641031
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380321340661641223810947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15586880893774427482540631 23380321340661641223810947)
  ·
    refine ⟨35070482010992461835716421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23380321340661641223810947 35070482010992461835716421)
    ·
      refine ⟨6575715377061086594196829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35070482010992461835716421 6575715377061086594196829)
      ·
        refine ⟨2465893266397907472823811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6575715377061086594196829 2465893266397907472823811)
        ·
          refine ⟨3698839899596861209235717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465893266397907472823811 3698839899596861209235717)
          ·
            refine ⟨693532481174411476731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3698839899596861209235717 693532481174411476731697)
            ·
              refine ⟨520149360880808607548773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693532481174411476731697 520149360880808607548773)
              ·
                refine ⟨97528005165151613915395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520149360880808607548773 97528005165151613915395)
                ·
                  rfl

theorem cell20_641031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_641031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641031 prefixEnd_641031 := by exact prefixLift 641031
  have htrace : WordTrace (prefixWord ++ tailWord_641031) baseStart_641031 baseEnd_641031 := by
    simpa [prefixWord, tailWord_641031, baseEnd_641031] using wordTrace_append hprefix tailTrace_641031
  have hstable : (prefixWord ++ tailWord_641031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641031).length < 2 ^ (prefixWord ++ tailWord_641031).sum := by decide
  have hdescent : baseEnd_641031 < baseStart_641031 := by decide
  rcases family_descends (prefixWord ++ tailWord_641031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641035 : List Nat := [1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_641035 : Nat := 118140960795 + 641035 * 2 ^ 59
def prefixEnd_641035 : Nat := 4983230072969 + 3 ^ 40 * 641035 * 2
def baseEnd_641035 : Nat := 97528613734816201870945

theorem tailTrace_641035 : CollatzResearch.WordTrace tailWord_641035 prefixEnd_641035 97528613734816201870945 := by
  unfold tailWord_641035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380467232647149906956559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15586978155098099937971039 23380467232647149906956559)
  ·
    refine ⟨35070700848970724860434839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23380467232647149906956559 35070700848970724860434839)
    ·
      refine ⟨52606051273456087290652259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35070700848970724860434839 52606051273456087290652259)
      ·
        refine ⟨78909076910184130935978389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52606051273456087290652259 78909076910184130935978389)
        ·
          refine ⟨3698862980164881137623987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78909076910184130935978389 3698862980164881137623987)
          ·
            refine ⟨5548294470247321706435981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698862980164881137623987 5548294470247321706435981)
            ·
              refine ⟨2080610426342745639913493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5548294470247321706435981 2080610426342745639913493)
              ·
                refine ⟨97528613734816201870945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2080610426342745639913493 97528613734816201870945)
                ·
                  rfl

theorem cell20_641035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_641035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641035 prefixEnd_641035 := by exact prefixLift 641035
  have htrace : WordTrace (prefixWord ++ tailWord_641035) baseStart_641035 baseEnd_641035 := by
    simpa [prefixWord, tailWord_641035, baseEnd_641035] using wordTrace_append hprefix tailTrace_641035
  have hstable : (prefixWord ++ tailWord_641035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641035).length < 2 ^ (prefixWord ++ tailWord_641035).sum := by decide
  have hdescent : baseEnd_641035 < baseStart_641035 := by decide
  rcases family_descends (prefixWord ++ tailWord_641035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641052 : List Nat := [2, 2, 3, 1, 3, 3, 6]
def baseStart_641052 : Nat := 118140960795 + 641052 * 2 ^ 59
def prefixEnd_641052 : Nat := 4983230072969 + 3 ^ 40 * 641052 * 2
def baseEnd_641052 : Nat := 32510400051963566894011

theorem tailTrace_641052 : CollatzResearch.WordTrace tailWord_641052 prefixEnd_641052 32510400051963566894011 := by
  unfold tailWord_641052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690543636792780905162705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15587391515723707873550273 11690543636792780905162705)
  ·
    refine ⟨8767907727594585678872029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11690543636792780905162705 8767907727594585678872029)
    ·
      refine ⟨3287965397847969629577011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8767907727594585678872029 3287965397847969629577011)
      ·
        refine ⟨4931948096771954444365517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287965397847969629577011 4931948096771954444365517)
        ·
          refine ⟨1849480536289482916637069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4931948096771954444365517 1849480536289482916637069)
          ·
            refine ⟨693555201108556093738901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1849480536289482916637069 693555201108556093738901)
            ·
              refine ⟨32510400051963566894011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 693555201108556093738901 32510400051963566894011)
              ·
                rfl

theorem cell20_641052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_641052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641052 prefixEnd_641052 := by exact prefixLift 641052
  have htrace : WordTrace (prefixWord ++ tailWord_641052) baseStart_641052 baseEnd_641052 := by
    simpa [prefixWord, tailWord_641052, baseEnd_641052] using wordTrace_append hprefix tailTrace_641052
  have hstable : (prefixWord ++ tailWord_641052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641052).length < 2 ^ (prefixWord ++ tailWord_641052).sum := by decide
  have hdescent : baseEnd_641052 < baseStart_641052 := by decide
  rcases family_descends (prefixWord ++ tailWord_641052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641059 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_641059 : Nat := 118140960795 + 641059 * 2 ^ 59
def prefixEnd_641059 : Nat := 4983230072969 + 3 ^ 40 * 641059 * 2
def baseEnd_641059 : Nat := 292596795458411188812737

theorem tailTrace_641059 : CollatzResearch.WordTrace tailWord_641059 prefixEnd_641059 292596795458411188812737 := by
  unfold tailWord_641059
  simp only [CollatzResearch.WordTrace]
  refine ⟨23381342584560202005830231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15587561723040134670553487 23381342584560202005830231)
  ·
    refine ⟨35072013876840303008745347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23381342584560202005830231 35072013876840303008745347)
    ·
      refine ⟨52608020815260454513118021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35072013876840303008745347 52608020815260454513118021)
      ·
        refine ⟨9864003902861335221209629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52608020815260454513118021 9864003902861335221209629)
        ·
          refine ⟨3699001463573000707953611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9864003902861335221209629 3699001463573000707953611)
          ·
            refine ⟨5548502195359501061930417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699001463573000707953611 5548502195359501061930417)
            ·
              refine ⟨4161376646519625796447813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5548502195359501061930417 4161376646519625796447813)
              ·
                refine ⟨780258121222429836833965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4161376646519625796447813 780258121222429836833965)
                ·
                  refine ⟨292596795458411188812737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780258121222429836833965 292596795458411188812737)
                  ·
                    rfl

theorem cell20_641059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_641059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641059 prefixEnd_641059 := by exact prefixLift 641059
  have htrace : WordTrace (prefixWord ++ tailWord_641059) baseStart_641059 baseEnd_641059 := by
    simpa [prefixWord, tailWord_641059, baseEnd_641059] using wordTrace_append hprefix tailTrace_641059
  have hstable : (prefixWord ++ tailWord_641059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641059).length < 2 ^ (prefixWord ++ tailWord_641059).sum := by decide
  have hdescent : baseEnd_641059 < baseStart_641059 := by decide
  rcases family_descends (prefixWord ++ tailWord_641059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641073 : List Nat := [1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_641073 : Nat := 118140960795 + 641073 * 2 ^ 59
def prefixEnd_641073 : Nat := 4983230072969 + 3 ^ 40 * 641073 * 2
def baseEnd_641073 : Nat := 97534395146629787448671

theorem tailTrace_641073 : CollatzResearch.WordTrace tailWord_641073 prefixEnd_641073 97534395146629787448671 := by
  unfold tailWord_641073
  simp only [CollatzResearch.WordTrace]
  refine ⟨23381853206509482396839873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15587902137672988264559915 23381853206509482396839873)
  ·
    refine ⟨17536389904882111797629905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23381853206509482396839873 17536389904882111797629905)
    ·
      refine ⟨13152292428661583848222429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17536389904882111797629905 13152292428661583848222429)
      ·
        refine ⟨4932109660748093943083411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13152292428661583848222429 4932109660748093943083411)
        ·
          refine ⟨7398164491122140914625117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932109660748093943083411 7398164491122140914625117)
          ·
            refine ⟨2774311684170802842984419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7398164491122140914625117 2774311684170802842984419)
            ·
              refine ⟨4161467526256204264476629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774311684170802842984419 4161467526256204264476629)
              ·
                refine ⟨97534395146629787448671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4161467526256204264476629 97534395146629787448671)
                ·
                  rfl

theorem cell20_641073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_641073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641073 prefixEnd_641073 := by exact prefixLift 641073
  have htrace : WordTrace (prefixWord ++ tailWord_641073) baseStart_641073 baseEnd_641073 := by
    simpa [prefixWord, tailWord_641073, baseEnd_641073] using wordTrace_append hprefix tailTrace_641073
  have hstable : (prefixWord ++ tailWord_641073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641073).length < 2 ^ (prefixWord ++ tailWord_641073).sum := by decide
  have hdescent : baseEnd_641073 < baseStart_641073 := by decide
  rcases family_descends (prefixWord ++ tailWord_641073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641110 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_641110 : Nat := 118140960795 + 641110 * 2 ^ 59
def prefixEnd_641110 : Nat := 4983230072969 + 3 ^ 40 * 641110 * 2
def baseEnd_641110 : Nat := 292620073248081678112529

theorem tailTrace_641110 : CollatzResearch.WordTrace tailWord_641110 prefixEnd_641110 292620073248081678112529 := by
  unfold tailWord_641110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461450169210964857246049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15588801804916958477291189 1461450169210964857246049)
  ·
    refine ⟨1096087626908223642934537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1461450169210964857246049 1096087626908223642934537)
    ·
      refine ⟨822065720181167732200903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1096087626908223642934537 822065720181167732200903)
      ·
        refine ⟨1233098580271751598301355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822065720181167732200903 1233098580271751598301355)
        ·
          refine ⟨1849647870407627397452033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233098580271751598301355 1849647870407627397452033)
          ·
            refine ⟨1387235902805720548089025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849647870407627397452033 1387235902805720548089025)
            ·
              refine ⟨1040426927104290411066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387235902805720548089025 1040426927104290411066769)
              ·
                refine ⟨780320195328217808300077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040426927104290411066769 780320195328217808300077)
                ·
                  refine ⟨292620073248081678112529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780320195328217808300077 292620073248081678112529)
                  ·
                    rfl

theorem cell20_641110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_641110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641110 prefixEnd_641110 := by exact prefixLift 641110
  have htrace : WordTrace (prefixWord ++ tailWord_641110) baseStart_641110 baseEnd_641110 := by
    simpa [prefixWord, tailWord_641110, baseEnd_641110] using wordTrace_append hprefix tailTrace_641110
  have hstable : (prefixWord ++ tailWord_641110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641110).length < 2 ^ (prefixWord ++ tailWord_641110).sum := by decide
  have hdescent : baseEnd_641110 < baseStart_641110 := by decide
  rcases family_descends (prefixWord ++ tailWord_641110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641117 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 2]
def baseStart_641117 : Nat := 118140960795 + 641117 * 2 ^ 59
def prefixEnd_641117 : Nat := 4983230072969 + 3 ^ 40 * 641117 * 2
def baseEnd_641117 : Nat := 292623268238820764879167

theorem tailTrace_641117 : CollatzResearch.WordTrace tailWord_641117 prefixEnd_641117 292623268238820764879167 := by
  unfold tailWord_641117
  simp only [CollatzResearch.WordTrace]
  refine ⟨23383458018350077911441605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15588972012233385274294403 23383458018350077911441605)
  ·
    refine ⟨4384398378440639608395301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23383458018350077911441605 4384398378440639608395301)
    ·
      refine ⟨822074695957619926574119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4384398378440639608395301 822074695957619926574119)
      ·
        refine ⟨1233112043936429889861179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822074695957619926574119 1233112043936429889861179)
        ·
          refine ⟨1849668065904644834791769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233112043936429889861179 1849668065904644834791769)
          ·
            refine ⟨1387251049428483626093827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849668065904644834791769 1387251049428483626093827)
            ·
              refine ⟨2080876574142725439140741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387251049428483626093827 2080876574142725439140741)
              ·
                refine ⟨390164357651761019838889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2080876574142725439140741 390164357651761019838889)
                ·
                  refine ⟨292623268238820764879167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390164357651761019838889 292623268238820764879167)
                  ·
                    rfl

theorem cell20_641117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_641117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641117 prefixEnd_641117 := by exact prefixLift 641117
  have htrace : WordTrace (prefixWord ++ tailWord_641117) baseStart_641117 baseEnd_641117 := by
    simpa [prefixWord, tailWord_641117, baseEnd_641117] using wordTrace_append hprefix tailTrace_641117
  have hstable : (prefixWord ++ tailWord_641117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641117).length < 2 ^ (prefixWord ++ tailWord_641117).sum := by decide
  have hdescent : baseEnd_641117 < baseStart_641117 := by decide
  rcases family_descends (prefixWord ++ tailWord_641117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641135 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_641135 : Nat := 118140960795 + 641135 * 2 ^ 59
def prefixEnd_641135 : Nat := 4983230072969 + 3 ^ 40 * 641135 * 2
def baseEnd_641135 : Nat := 292631483929292702279093

theorem tailTrace_641135 : CollatzResearch.WordTrace tailWord_641135 prefixEnd_641135 292631483929292702279093 := by
  unfold tailWord_641135
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384114532284866985596859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15589409688189911323731239 23384114532284866985596859)
  ·
    refine ⟨35076171798427300478395289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23384114532284866985596859 35076171798427300478395289)
    ·
      refine ⟨26307128848820475358796467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35076171798427300478395289 26307128848820475358796467)
      ·
        refine ⟨39460693273230713038194701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26307128848820475358796467 39460693273230713038194701)
        ·
          refine ⟨14797759977461517389323013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39460693273230713038194701 14797759977461517389323013)
          ·
            refine ⟨2774579995774034510498065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14797759977461517389323013 2774579995774034510498065)
            ·
              refine ⟨2080934996830525882873549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774579995774034510498065 2080934996830525882873549)
              ·
                refine ⟨780350623811447206077581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2080934996830525882873549 780350623811447206077581)
                ·
                  refine ⟨292631483929292702279093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780350623811447206077581 292631483929292702279093)
                  ·
                    rfl

theorem cell20_641135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_641135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641135 prefixEnd_641135 := by exact prefixLift 641135
  have htrace : WordTrace (prefixWord ++ tailWord_641135) baseStart_641135 baseEnd_641135 := by
    simpa [prefixWord, tailWord_641135, baseEnd_641135] using wordTrace_append hprefix tailTrace_641135
  have hstable : (prefixWord ++ tailWord_641135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641135).length < 2 ^ (prefixWord ++ tailWord_641135).sum := by decide
  have hdescent : baseEnd_641135 < baseStart_641135 := by decide
  rcases family_descends (prefixWord ++ tailWord_641135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641159 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 2]
def baseStart_641159 : Nat := 118140960795 + 641159 * 2 ^ 59
def prefixEnd_641159 : Nat := 4983230072969 + 3 ^ 40 * 641159 * 2
def baseEnd_641159 : Nat := 292642438183255285478995

theorem tailTrace_641159 : CollatzResearch.WordTrace tailWord_641159 prefixEnd_641159 292642438183255285478995 := by
  unfold tailWord_641159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384989884197919084470531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15589993256131946056313687 23384989884197919084470531)
  ·
    refine ⟨35077484826296878626705797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23384989884197919084470531 35077484826296878626705797)
    ·
      refine ⟨6577028404930664742507337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35077484826296878626705797 6577028404930664742507337)
      ·
        refine ⟨4932771303697998556880503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6577028404930664742507337 4932771303697998556880503)
        ·
          refine ⟨7399156955546997835320755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932771303697998556880503 7399156955546997835320755)
          ·
            refine ⟨11098735433320496752981133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399156955546997835320755 11098735433320496752981133)
            ·
              refine ⟨4162025787495186282367925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11098735433320496752981133 4162025787495186282367925)
              ·
                refine ⟨390189917577673713971993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4162025787495186282367925 390189917577673713971993)
                ·
                  refine ⟨292642438183255285478995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390189917577673713971993 292642438183255285478995)
                  ·
                    rfl

theorem cell20_641159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2].length) (baseStart_641159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641159 prefixEnd_641159 := by exact prefixLift 641159
  have htrace : WordTrace (prefixWord ++ tailWord_641159) baseStart_641159 baseEnd_641159 := by
    simpa [prefixWord, tailWord_641159, baseEnd_641159] using wordTrace_append hprefix tailTrace_641159
  have hstable : (prefixWord ++ tailWord_641159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641159).length < 2 ^ (prefixWord ++ tailWord_641159).sum := by decide
  have hdescent : baseEnd_641159 < baseStart_641159 := by decide
  rcases family_descends (prefixWord ++ tailWord_641159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641166 : List Nat := [4, 1, 1, 3, 3, 1, 7]
def baseStart_641166 : Nat := 118140960795 + 641166 * 2 ^ 59
def prefixEnd_641166 : Nat := 4983230072969 + 3 ^ 40 * 641166 * 2
def baseEnd_641166 : Nat := 32516181463777152471737

theorem tailTrace_641166 : CollatzResearch.WordTrace tailWord_641166 prefixEnd_641166 32516181463777152471737 := by
  unfold tailWord_641166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923155649396569909996919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15590163463448372853316901 2923155649396569909996919)
  ·
    refine ⟨4384733474094854864995379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923155649396569909996919 4384733474094854864995379)
    ·
      refine ⟨6577100211142282297493069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384733474094854864995379 6577100211142282297493069)
      ·
        refine ⟨2466412579178355861559901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6577100211142282297493069 2466412579178355861559901)
        ·
          refine ⟨924904717191883448084963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2466412579178355861559901 924904717191883448084963)
          ·
            refine ⟨1387357075787825172127445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924904717191883448084963 1387357075787825172127445)
            ·
              refine ⟨32516181463777152471737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1387357075787825172127445 32516181463777152471737)
              ·
                rfl

theorem cell20_641166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_641166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641166 prefixEnd_641166 := by exact prefixLift 641166
  have htrace : WordTrace (prefixWord ++ tailWord_641166) baseStart_641166 baseEnd_641166 := by
    simpa [prefixWord, tailWord_641166, baseEnd_641166] using wordTrace_append hprefix tailTrace_641166
  have hstable : (prefixWord ++ tailWord_641166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641166).length < 2 ^ (prefixWord ++ tailWord_641166).sum := by decide
  have hdescent : baseEnd_641166 < baseStart_641166 := by decide
  rcases family_descends (prefixWord ++ tailWord_641166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641197 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_641197 : Nat := 118140960795 + 641197 * 2 ^ 59
def prefixEnd_641197 : Nat := 4983230072969 + 3 ^ 40 * 641197 * 2
def baseEnd_641197 : Nat := 292659782418696042212173

theorem tailTrace_641197 : CollatzResearch.WordTrace tailWord_641197 prefixEnd_641197 292659782418696042212173 := by
  unfold tailWord_641197
  simp only [CollatzResearch.WordTrace]
  refine ⟨23386375858060251574353845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15590917238706834382902563 23386375858060251574353845)
  ·
    refine ⟨2192472736693148585095673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23386375858060251574353845 2192472736693148585095673)
    ·
      refine ⟨1644354552519861438821755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2192472736693148585095673 1644354552519861438821755)
      ·
        refine ⟨2466531828779792158232633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644354552519861438821755 2466531828779792158232633)
        ·
          refine ⟨1849898871584844118674475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466531828779792158232633 1849898871584844118674475)
          ·
            refine ⟨2774848307377266178011713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849898871584844118674475 2774848307377266178011713)
            ·
              refine ⟨2081136230532949633508785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2774848307377266178011713 2081136230532949633508785)
              ·
                refine ⟨1560852172899712225131589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081136230532949633508785 1560852172899712225131589)
                ·
                  refine ⟨292659782418696042212173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560852172899712225131589 292659782418696042212173)
                  ·
                    rfl

theorem cell20_641197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_641197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641197 prefixEnd_641197 := by exact prefixLift 641197
  have htrace : WordTrace (prefixWord ++ tailWord_641197) baseStart_641197 baseEnd_641197 := by
    simpa [prefixWord, tailWord_641197, baseEnd_641197] using wordTrace_append hprefix tailTrace_641197
  have hstable : (prefixWord ++ tailWord_641197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641197).length < 2 ^ (prefixWord ++ tailWord_641197).sum := by decide
  have hdescent : baseEnd_641197 < baseStart_641197 := by decide
  rcases family_descends (prefixWord ++ tailWord_641197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641245 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_641245 : Nat := 118140960795 + 641245 * 2 ^ 59
def prefixEnd_641245 : Nat := 4983230072969 + 3 ^ 40 * 641245 * 2
def baseEnd_641245 : Nat := 292681690926621208611977

theorem tailTrace_641245 : CollatzResearch.WordTrace tailWord_641245 prefixEnd_641245 292681690926621208611977 := by
  unfold tailWord_641245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388126561886355772101189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15592084374590903848067459 23388126561886355772101189)
  ·
    refine ⟨4385273730353691707268973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23388126561886355772101189 4385273730353691707268973)
    ·
      refine ⟨1644477648882634390225865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4385273730353691707268973 1644477648882634390225865)
      ·
        refine ⟨1233358236661975792669399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1644477648882634390225865 1233358236661975792669399)
        ·
          refine ⟨1850037354992963689004099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233358236661975792669399 1850037354992963689004099)
          ·
            refine ⟨2775056032489445533506149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850037354992963689004099 2775056032489445533506149)
            ·
              refine ⟨520323006091771037532403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2775056032489445533506149 520323006091771037532403)
              ·
                refine ⟨780484509137656556298605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520323006091771037532403 780484509137656556298605)
                ·
                  refine ⟨292681690926621208611977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780484509137656556298605 292681690926621208611977)
                  ·
                    rfl

theorem cell20_641245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_641245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641245 prefixEnd_641245 := by exact prefixLift 641245
  have htrace : WordTrace (prefixWord ++ tailWord_641245) baseStart_641245 baseEnd_641245 := by
    simpa [prefixWord, tailWord_641245, baseEnd_641245] using wordTrace_append hprefix tailTrace_641245
  have hstable : (prefixWord ++ tailWord_641245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641245).length < 2 ^ (prefixWord ++ tailWord_641245).sum := by decide
  have hdescent : baseEnd_641245 < baseStart_641245 := by decide
  rcases family_descends (prefixWord ++ tailWord_641245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641249 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_641249 : Nat := 118140960795 + 641249 * 2 ^ 59
def prefixEnd_641249 : Nat := 4983230072969 + 3 ^ 40 * 641249 * 2
def baseEnd_641249 : Nat := 292683516635614972478627

theorem tailTrace_641249 : CollatzResearch.WordTrace tailWord_641249 prefixEnd_641249 292683516635614972478627 := by
  unfold tailWord_641249
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388272453871864455246801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15592181635914576303497867 23388272453871864455246801)
  ·
    refine ⟨17541204340403898341435101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23388272453871864455246801 17541204340403898341435101)
    ·
      refine ⟨6577951627651461878038163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17541204340403898341435101 6577951627651461878038163)
      ·
        refine ⟨9866927441477192817057245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577951627651461878038163 9866927441477192817057245)
        ·
          refine ⟨3700097790553947306396467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9866927441477192817057245 3700097790553947306396467)
          ·
            refine ⟨5550146685830920959594701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700097790553947306396467 5550146685830920959594701)
            ·
              refine ⟨2081305007186595359848013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5550146685830920959594701 2081305007186595359848013)
              ·
                refine ⟨780489377694973259943005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081305007186595359848013 780489377694973259943005)
                ·
                  refine ⟨292683516635614972478627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780489377694973259943005 292683516635614972478627)
                  ·
                    rfl

theorem cell20_641249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_641249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641249 prefixEnd_641249 := by exact prefixLift 641249
  have htrace : WordTrace (prefixWord ++ tailWord_641249) baseStart_641249 baseEnd_641249 := by
    simpa [prefixWord, tailWord_641249, baseEnd_641249] using wordTrace_append hprefix tailTrace_641249
  have hstable : (prefixWord ++ tailWord_641249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641249).length < 2 ^ (prefixWord ++ tailWord_641249).sum := by decide
  have hdescent : baseEnd_641249 < baseStart_641249 := by decide
  rcases family_descends (prefixWord ++ tailWord_641249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641263 : List Nat := [1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_641263 : Nat := 118140960795 + 641263 * 2 ^ 59
def prefixEnd_641263 : Nat := 4983230072969 + 3 ^ 40 * 641263 * 2
def baseEnd_641263 : Nat := 97563302205697715337301

theorem tailTrace_641263 : CollatzResearch.WordTrace tailWord_641263 prefixEnd_641263 97563302205697715337301 := by
  unfold tailWord_641263
  simp only [CollatzResearch.WordTrace]
  refine ⟨23388783075821144846256443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15592522050547429897504295 23388783075821144846256443)
  ·
    refine ⟨35083174613731717269384665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23388783075821144846256443 35083174613731717269384665)
    ·
      refine ⟨26312380960298787952038499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35083174613731717269384665 26312380960298787952038499)
      ·
        refine ⟨39468571440448181928057749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26312380960298787952038499 39468571440448181928057749)
        ·
          refine ⟨1850089286271008527877707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39468571440448181928057749 1850089286271008527877707)
          ·
            refine ⟨2775133929406512791816561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850089286271008527877707 2775133929406512791816561)
            ·
              refine ⟨2081350447054884593862421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2775133929406512791816561 2081350447054884593862421)
              ·
                refine ⟨97563302205697715337301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2081350447054884593862421 97563302205697715337301)
                ·
                  rfl

theorem cell20_641263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_641263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641263 prefixEnd_641263 := by exact prefixLift 641263
  have htrace : WordTrace (prefixWord ++ tailWord_641263) baseStart_641263 baseEnd_641263 := by
    simpa [prefixWord, tailWord_641263, baseEnd_641263] using wordTrace_append hprefix tailTrace_641263
  have hstable : (prefixWord ++ tailWord_641263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641263).length < 2 ^ (prefixWord ++ tailWord_641263).sum := by decide
  have hdescent : baseEnd_641263 < baseStart_641263 := by decide
  rcases family_descends (prefixWord ++ tailWord_641263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641290 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_641290 : Nat := 118140960795 + 641290 * 2 ^ 59
def prefixEnd_641290 : Nat := 4983230072969 + 3 ^ 40 * 641290 * 2
def baseEnd_641290 : Nat := 292702230152801052111793

theorem tailTrace_641290 : CollatzResearch.WordTrace tailWord_641290 prefixEnd_641290 292702230152801052111793 := by
  unfold tailWord_641290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847441961680832114372331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15593178564482218971659549 5847441961680832114372331)
  ·
    refine ⟨8771162942521248171558497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5847441961680832114372331 8771162942521248171558497)
    ·
      refine ⟨6578372206890936128668873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8771162942521248171558497 6578372206890936128668873)
      ·
        refine ⟨4933779155168202096501655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6578372206890936128668873 4933779155168202096501655)
        ·
          refine ⟨7400668732752303144752483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933779155168202096501655 7400668732752303144752483)
          ·
            refine ⟨11101003099128454717128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400668732752303144752483 11101003099128454717128725)
            ·
              refine ⟨520359520271646314865409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11101003099128454717128725 520359520271646314865409)
              ·
                refine ⟨390269640203734736149057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520359520271646314865409 390269640203734736149057)
                ·
                  refine ⟨292702230152801052111793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390269640203734736149057 292702230152801052111793)
                  ·
                    rfl

theorem cell20_641290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_641290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641290 prefixEnd_641290 := by exact prefixLift 641290
  have htrace : WordTrace (prefixWord ++ tailWord_641290) baseStart_641290 baseEnd_641290 := by
    simpa [prefixWord, tailWord_641290, baseEnd_641290] using wordTrace_append hprefix tailTrace_641290
  have hstable : (prefixWord ++ tailWord_641290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641290).length < 2 ^ (prefixWord ++ tailWord_641290).sum := by decide
  have hdescent : baseEnd_641290 < baseStart_641290 := by decide
  rcases family_descends (prefixWord ++ tailWord_641290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641294 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_641294 : Nat := 118140960795 + 641294 * 2 ^ 59
def prefixEnd_641294 : Nat := 4983230072969 + 3 ^ 40 * 641294 * 2
def baseEnd_641294 : Nat := 292704055861794815978443

theorem tailTrace_641294 : CollatzResearch.WordTrace tailWord_641294 prefixEnd_641294 292704055861794815978443 := by
  unfold tailWord_641294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923739217338604642579367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15593275825805891427089957 2923739217338604642579367)
  ·
    refine ⟨4385608826007906963869051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923739217338604642579367 4385608826007906963869051)
    ·
      refine ⟨6578413239011860445803577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385608826007906963869051 6578413239011860445803577)
      ·
        refine ⟨4933809929258895334352683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6578413239011860445803577 4933809929258895334352683)
        ·
          refine ⟨7400714893888343001529025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933809929258895334352683 7400714893888343001529025)
          ·
            refine ⟨5550536170416257251146769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7400714893888343001529025 5550536170416257251146769)
            ·
              refine ⟨4162902127812192938360077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5550536170416257251146769 4162902127812192938360077)
              ·
                refine ⟨1561088297929572351885029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4162902127812192938360077 1561088297929572351885029)
                ·
                  refine ⟨292704055861794815978443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561088297929572351885029 292704055861794815978443)
                  ·
                    rfl

theorem cell20_641294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_641294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641294 prefixEnd_641294 := by exact prefixLift 641294
  have htrace : WordTrace (prefixWord ++ tailWord_641294) baseStart_641294 baseEnd_641294 := by
    simpa [prefixWord, tailWord_641294, baseEnd_641294] using wordTrace_append hprefix tailTrace_641294
  have hstable : (prefixWord ++ tailWord_641294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641294).length < 2 ^ (prefixWord ++ tailWord_641294).sum := by decide
  have hdescent : baseEnd_641294 < baseStart_641294 := by decide
  rcases family_descends (prefixWord ++ tailWord_641294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641301 : List Nat := [1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_641301 : Nat := 118140960795 + 641301 * 2 ^ 59
def prefixEnd_641301 : Nat := 4983230072969 + 3 ^ 40 * 641301 * 2
def baseEnd_641301 : Nat := 97569083617511300915027

theorem tailTrace_641301 : CollatzResearch.WordTrace tailWord_641301 prefixEnd_641301 97569083617511300915027 := by
  unfold tailWord_641301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390169049683477336139757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15593446033122318224093171 23390169049683477336139757)
  ·
    refine ⟨8771313393631304001052409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23390169049683477336139757 8771313393631304001052409)
    ·
      refine ⟨6578485045223478000789307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8771313393631304001052409 6578485045223478000789307)
      ·
        refine ⟨9867727567835217001183961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6578485045223478000789307 9867727567835217001183961)
        ·
          refine ⟨7400795675876412750887971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9867727567835217001183961 7400795675876412750887971)
          ·
            refine ⟨11101193513814619126331957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400795675876412750887971 11101193513814619126331957)
            ·
              refine ⟨1040736891920120543093621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11101193513814619126331957 1040736891920120543093621)
              ·
                refine ⟨97569083617511300915027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1040736891920120543093621 97569083617511300915027)
                ·
                  rfl

theorem cell20_641301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_641301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641301 prefixEnd_641301 := by exact prefixLift 641301
  have htrace : WordTrace (prefixWord ++ tailWord_641301) baseStart_641301 baseEnd_641301 := by
    simpa [prefixWord, tailWord_641301, baseEnd_641301] using wordTrace_append hprefix tailTrace_641301
  have hstable : (prefixWord ++ tailWord_641301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641301).length < 2 ^ (prefixWord ++ tailWord_641301).sum := by decide
  have hdescent : baseEnd_641301 < baseStart_641301 := by decide
  rcases family_descends (prefixWord ++ tailWord_641301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641308 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_641308 : Nat := 118140960795 + 641308 * 2 ^ 59
def prefixEnd_641308 : Nat := 4983230072969 + 3 ^ 40 * 641308 * 2
def baseEnd_641308 : Nat := 292710445843272989511719

theorem tailTrace_641308 : CollatzResearch.WordTrace tailWord_641308 prefixEnd_641308 292710445843272989511719 := by
  unfold tailWord_641308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11695212180329058765822289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15593616240438745021096385 11695212180329058765822289)
  ·
    refine ⟨8771409135246794074366717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11695212180329058765822289 8771409135246794074366717)
    ·
      refine ⟨3289278425717547777887519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8771409135246794074366717 3289278425717547777887519)
      ·
        refine ⟨4933917638576321666831279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289278425717547777887519 4933917638576321666831279)
        ·
          refine ⟨7400876457864482500246919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933917638576321666831279 7400876457864482500246919)
          ·
            refine ⟨11101314686796723750370379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400876457864482500246919 11101314686796723750370379)
            ·
              refine ⟨16651972030195085625555569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101314686796723750370379 16651972030195085625555569)
              ·
                refine ⟨12488979022646314219166677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16651972030195085625555569 12488979022646314219166677)
                ·
                  refine ⟨292710445843272989511719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12488979022646314219166677 292710445843272989511719)
                  ·
                    rfl

theorem cell20_641308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_641308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641308 prefixEnd_641308 := by exact prefixLift 641308
  have htrace : WordTrace (prefixWord ++ tailWord_641308) baseStart_641308 baseEnd_641308 := by
    simpa [prefixWord, tailWord_641308, baseEnd_641308] using wordTrace_append hprefix tailTrace_641308
  have hstable : (prefixWord ++ tailWord_641308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641308).length < 2 ^ (prefixWord ++ tailWord_641308).sum := by decide
  have hdescent : baseEnd_641308 < baseStart_641308 := by decide
  rcases family_descends (prefixWord ++ tailWord_641308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641342 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_641342 : Nat := 118140960795 + 641342 * 2 ^ 59
def prefixEnd_641342 : Nat := 4983230072969 + 3 ^ 40 * 641342 * 2
def baseEnd_641342 : Nat := 292725964369719982378247

theorem tailTrace_641342 : CollatzResearch.WordTrace tailWord_641342 prefixEnd_641342 292725964369719982378247 := by
  unfold tailWord_641342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923958055316867667297785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15594442961689960892254853 2923958055316867667297785)
  ·
    refine ⟨2192968541487650750473339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2923958055316867667297785 2192968541487650750473339)
    ·
      refine ⟨3289452812231476125710009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192968541487650750473339 3289452812231476125710009)
      ·
        refine ⟨2467089609173607094282507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3289452812231476125710009 2467089609173607094282507)
        ·
          refine ⟨3700634413760410641423761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467089609173607094282507 3700634413760410641423761)
          ·
            refine ⟨2775475810320307981067821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3700634413760410641423761 2775475810320307981067821)
            ·
              refine ⟨1040803428870115492900433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2775475810320307981067821 1040803428870115492900433)
              ·
                refine ⟨780602571652586619675325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040803428870115492900433 780602571652586619675325)
                ·
                  refine ⟨292725964369719982378247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 780602571652586619675325 292725964369719982378247)
                  ·
                    rfl

theorem cell20_641342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_641342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641342 prefixEnd_641342 := by exact prefixLift 641342
  have htrace : WordTrace (prefixWord ++ tailWord_641342) baseStart_641342 baseEnd_641342 := by
    simpa [prefixWord, tailWord_641342, baseEnd_641342] using wordTrace_append hprefix tailTrace_641342
  have hstable : (prefixWord ++ tailWord_641342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641342).length < 2 ^ (prefixWord ++ tailWord_641342).sum := by decide
  have hdescent : baseEnd_641342 < baseStart_641342 := by decide
  rcases family_descends (prefixWord ++ tailWord_641342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641415 : List Nat := [1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_641415 : Nat := 118140960795 + 641415 * 2 ^ 59
def prefixEnd_641415 : Nat := 4983230072969 + 3 ^ 40 * 641415 * 2
def baseEnd_641415 : Nat := 97586427852952057648205

theorem tailTrace_641415 : CollatzResearch.WordTrace tailWord_641415 prefixEnd_641415 97586427852952057648205 := by
  unfold tailWord_641415
  simp only [CollatzResearch.WordTrace]
  refine ⟨23394326971270474805789699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15596217980846983203859799 23394326971270474805789699)
  ·
    refine ⟨35091490456905712208684549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23394326971270474805789699 35091490456905712208684549)
    ·
      refine ⟨6579654460669821039128353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35091490456905712208684549 6579654460669821039128353)
      ·
        refine ⟨4934740845502365779346265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6579654460669821039128353 4934740845502365779346265)
        ·
          refine ⟨3701055634126774334509699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4934740845502365779346265 3701055634126774334509699)
          ·
            refine ⟨5551583451190161501764549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701055634126774334509699 5551583451190161501764549)
            ·
              refine ⟨1040921897098155281580853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5551583451190161501764549 1040921897098155281580853)
              ·
                refine ⟨97586427852952057648205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1040921897098155281580853 97586427852952057648205)
                ·
                  rfl

theorem cell20_641415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_641415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641415 prefixEnd_641415 := by exact prefixLift 641415
  have htrace : WordTrace (prefixWord ++ tailWord_641415) baseStart_641415 baseEnd_641415 := by
    simpa [prefixWord, tailWord_641415, baseEnd_641415] using wordTrace_append hprefix tailTrace_641415
  have hstable : (prefixWord ++ tailWord_641415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641415).length < 2 ^ (prefixWord ++ tailWord_641415).sum := by decide
  have hdescent : baseEnd_641415 < baseStart_641415 := by decide
  rcases family_descends (prefixWord ++ tailWord_641415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641429 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_641429 : Nat := 118140960795 + 641429 * 2 ^ 59
def prefixEnd_641429 : Nat := 4983230072969 + 3 ^ 40 * 641429 * 2
def baseEnd_641429 : Nat := 292765673540334346477891

theorem tailTrace_641429 : CollatzResearch.WordTrace tailWord_641429 prefixEnd_641429 292765673540334346477891 := by
  unfold tailWord_641429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23394837593219755196799341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15596558395479836797866227 23394837593219755196799341)
  ·
    refine ⟨8773064097457408198799753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23394837593219755196799341 8773064097457408198799753)
    ·
      refine ⟨6579798073093056149099815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8773064097457408198799753 6579798073093056149099815)
      ·
        refine ⟨9869697109639584223649723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6579798073093056149099815 9869697109639584223649723)
        ·
          refine ⟨14804545664459376335474585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869697109639584223649723 14804545664459376335474585)
          ·
            refine ⟨11103409248344532251605939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14804545664459376335474585 11103409248344532251605939)
            ·
              refine ⟨16655113872516798377408909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11103409248344532251605939 16655113872516798377408909)
              ·
                refine ⟨6245667702193799391528341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16655113872516798377408909 6245667702193799391528341)
                ·
                  refine ⟨292765673540334346477891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6245667702193799391528341 292765673540334346477891)
                  ·
                    rfl

theorem cell20_641429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_641429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641429 prefixEnd_641429 := by exact prefixLift 641429
  have htrace : WordTrace (prefixWord ++ tailWord_641429) baseStart_641429 baseEnd_641429 := by
    simpa [prefixWord, tailWord_641429, baseEnd_641429] using wordTrace_append hprefix tailTrace_641429
  have hstable : (prefixWord ++ tailWord_641429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641429).length < 2 ^ (prefixWord ++ tailWord_641429).sum := by decide
  have hdescent : baseEnd_641429 < baseStart_641429 := by decide
  rcases family_descends (prefixWord ++ tailWord_641429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641453 : List Nat := [1, 5, 2, 2, 10]
def baseStart_641453 : Nat := 118140960795 + 641453 * 2 ^ 59
def prefixEnd_641453 : Nat := 4983230072969 + 3 ^ 40 * 641453 * 2
def baseEnd_641453 : Nat := 3614526269065394193553

theorem tailTrace_641453 : CollatzResearch.WordTrace tailWord_641453 prefixEnd_641453 3614526269065394193553 := by
  unfold tailWord_641453
  simp only [CollatzResearch.WordTrace]
  refine ⟨23395712945132807295673013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15597141963421871530448675 23395712945132807295673013)
  ·
    refine ⟨2193348088606200683969345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23395712945132807295673013 2193348088606200683969345)
    ·
      refine ⟨1645011066454650512977009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2193348088606200683969345 1645011066454650512977009)
      ·
        refine ⟨1233758299840987884732757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1645011066454650512977009 1233758299840987884732757)
        ·
          refine ⟨3614526269065394193553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1233758299840987884732757 3614526269065394193553)
          ·
            rfl

theorem cell20_641453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 10].length) (baseStart_641453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641453 prefixEnd_641453 := by exact prefixLift 641453
  have htrace : WordTrace (prefixWord ++ tailWord_641453) baseStart_641453 baseEnd_641453 := by
    simpa [prefixWord, tailWord_641453, baseEnd_641453] using wordTrace_append hprefix tailTrace_641453
  have hstable : (prefixWord ++ tailWord_641453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641453).length < 2 ^ (prefixWord ++ tailWord_641453).sum := by decide
  have hdescent : baseEnd_641453 < baseStart_641453 := by decide
  rcases family_descends (prefixWord ++ tailWord_641453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641463 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 2]
def baseStart_641463 : Nat := 118140960795 + 641463 * 2 ^ 59
def prefixEnd_641463 : Nat := 4983230072969 + 3 ^ 40 * 641463 * 2
def baseEnd_641463 : Nat := 292781192066781339344419

theorem tailTrace_641463 : CollatzResearch.WordTrace tailWord_641463 prefixEnd_641463 292781192066781339344419 := by
  unfold tailWord_641463
  simp only [CollatzResearch.WordTrace]
  refine ⟨23396077675096579003537043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15597385116731052669024695 23396077675096579003537043)
  ·
    refine ⟨35094116512644868505305565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23396077675096579003537043 35094116512644868505305565)
    ·
      refine ⟨13160293692241825689489587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35094116512644868505305565 13160293692241825689489587)
      ·
        refine ⟨19740440538362738534234381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13160293692241825689489587 19740440538362738534234381)
        ·
          refine ⟨7402665201886026950337893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19740440538362738534234381 7402665201886026950337893)
          ·
            refine ⟨1387999725353630053188355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7402665201886026950337893 1387999725353630053188355)
            ·
              refine ⟨2081999588030445079782533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387999725353630053188355 2081999588030445079782533)
              ·
                refine ⟨390374922755708452459225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2081999588030445079782533 390374922755708452459225)
                ·
                  refine ⟨292781192066781339344419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390374922755708452459225 292781192066781339344419)
                  ·
                    rfl

theorem cell20_641463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 2].length) (baseStart_641463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641463 prefixEnd_641463 := by exact prefixLift 641463
  have htrace : WordTrace (prefixWord ++ tailWord_641463) baseStart_641463 baseEnd_641463 := by
    simpa [prefixWord, tailWord_641463, baseEnd_641463] using wordTrace_append hprefix tailTrace_641463
  have hstable : (prefixWord ++ tailWord_641463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641463).length < 2 ^ (prefixWord ++ tailWord_641463).sum := by decide
  have hdescent : baseEnd_641463 < baseStart_641463 := by decide
  rcases family_descends (prefixWord ++ tailWord_641463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641498 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_641498 : Nat := 118140960795 + 641498 * 2 ^ 59
def prefixEnd_641498 : Nat := 4983230072969 + 3 ^ 40 * 641498 * 2
def baseEnd_641498 : Nat := 292797167020476773177609

theorem tailTrace_641498 : CollatzResearch.WordTrace tailWord_641498 prefixEnd_641498 292797167020476773177609 := by
  unfold tailWord_641498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849338557492444995265287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15598236153313186654040765 5849338557492444995265287)
  ·
    refine ⟨8774007836238667492897931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849338557492444995265287 8774007836238667492897931)
    ·
      refine ⟨13161011754358001239346897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8774007836238667492897931 13161011754358001239346897)
      ·
        refine ⟨9870758815768500929510173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13161011754358001239346897 9870758815768500929510173)
        ·
          refine ⟨3701534555913187848566315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9870758815768500929510173 3701534555913187848566315)
          ·
            refine ⟨5552301833869781772849473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701534555913187848566315 5552301833869781772849473)
            ·
              refine ⟨4164226375402336329637105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5552301833869781772849473 4164226375402336329637105)
              ·
                refine ⟨3123169781551752247227829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164226375402336329637105 3123169781551752247227829)
                ·
                  refine ⟨292797167020476773177609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3123169781551752247227829 292797167020476773177609)
                  ·
                    rfl

theorem cell20_641498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_641498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641498 prefixEnd_641498 := by exact prefixLift 641498
  have htrace : WordTrace (prefixWord ++ tailWord_641498) baseStart_641498 baseEnd_641498 := by
    simpa [prefixWord, tailWord_641498, baseEnd_641498] using wordTrace_append hprefix tailTrace_641498
  have hstable : (prefixWord ++ tailWord_641498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641498).length < 2 ^ (prefixWord ++ tailWord_641498).sum := by decide
  have hdescent : baseEnd_641498 < baseStart_641498 := by decide
  rcases family_descends (prefixWord ++ tailWord_641498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641505 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_641505 : Nat := 118140960795 + 641505 * 2 ^ 59
def prefixEnd_641505 : Nat := 4983230072969 + 3 ^ 40 * 641505 * 2
def baseEnd_641505 : Nat := 292800362011215859944247

theorem tailTrace_641505 : CollatzResearch.WordTrace tailWord_641505 prefixEnd_641505 292800362011215859944247 := by
  unfold tailWord_641505
  simp only [CollatzResearch.WordTrace]
  refine ⟨23397609540944420176565969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15598406360629613451043979 23397609540944420176565969)
  ·
    refine ⟨17548207155708315132424477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23397609540944420176565969 17548207155708315132424477)
    ·
      refine ⟨6580577683390618174659179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17548207155708315132424477 6580577683390618174659179)
      ·
        refine ⟨9870866525085927261988769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580577683390618174659179 9870866525085927261988769)
        ·
          refine ⟨7403149893814445446491577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9870866525085927261988769 7403149893814445446491577)
          ·
            refine ⟨5552362420360834084868683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7403149893814445446491577 5552362420360834084868683)
            ·
              refine ⟨8328543630541251127303025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552362420360834084868683 8328543630541251127303025)
              ·
                refine ⟨6246407722905938345477269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8328543630541251127303025 6246407722905938345477269)
                ·
                  refine ⟨292800362011215859944247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6246407722905938345477269 292800362011215859944247)
                  ·
                    rfl

theorem cell20_641505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_641505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641505 prefixEnd_641505 := by exact prefixLift 641505
  have htrace : WordTrace (prefixWord ++ tailWord_641505) baseStart_641505 baseEnd_641505 := by
    simpa [prefixWord, tailWord_641505, baseEnd_641505] using wordTrace_append hprefix tailTrace_641505
  have hstable : (prefixWord ++ tailWord_641505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641505).length < 2 ^ (prefixWord ++ tailWord_641505).sum := by decide
  have hdescent : baseEnd_641505 < baseStart_641505 := by decide
  rcases family_descends (prefixWord ++ tailWord_641505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641542 : List Nat := [6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_641542 : Nat := 118140960795 + 641542 * 2 ^ 59
def prefixEnd_641542 : Nat := 4983230072969 + 3 ^ 40 * 641542 * 2
def baseEnd_641542 : Nat := 97605749939802725236921

theorem tailTrace_641542 : CollatzResearch.WordTrace tailWord_641542 prefixEnd_641542 97605749939802725236921 := by
  unfold tailWord_641542
  simp only [CollatzResearch.WordTrace]
  refine ⟨731217470056574234239465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15599306027873583663775253 731217470056574234239465)
  ·
    refine ⟨548413102542430675679599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 731217470056574234239465 548413102542430675679599)
    ·
      refine ⟨822619653813646013519399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548413102542430675679599 822619653813646013519399)
      ·
        refine ⟨1233929480720469020279099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822619653813646013519399 1233929480720469020279099)
        ·
          refine ⟨1850894221080703530418649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233929480720469020279099 1850894221080703530418649)
          ·
            refine ⟨1388170665810527647813987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850894221080703530418649 1388170665810527647813987)
            ·
              refine ⟨2082255998715791471720981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388170665810527647813987 2082255998715791471720981)
              ·
                refine ⟨97605749939802725236921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2082255998715791471720981 97605749939802725236921)
                ·
                  rfl

theorem cell20_641542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_641542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641542 prefixEnd_641542 := by exact prefixLift 641542
  have htrace : WordTrace (prefixWord ++ tailWord_641542) baseStart_641542 baseEnd_641542 := by
    simpa [prefixWord, tailWord_641542, baseEnd_641542] using wordTrace_append hprefix tailTrace_641542
  have hstable : (prefixWord ++ tailWord_641542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641542).length < 2 ^ (prefixWord ++ tailWord_641542).sum := by decide
  have hdescent : baseEnd_641542 < baseStart_641542 := by decide
  rcases family_descends (prefixWord ++ tailWord_641542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641628 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_641628 : Nat := 118140960795 + 641628 * 2 ^ 59
def prefixEnd_641628 : Nat := 4983230072969 + 3 ^ 40 * 641628 * 2
def baseEnd_641628 : Nat := 292856502562774098843745

theorem tailTrace_641628 : CollatzResearch.WordTrace tailWord_641628 prefixEnd_641628 292856502562774098843745 := by
  unfold tailWord_641628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11701047859749406091646769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15601397146332541455529025 11701047859749406091646769)
  ·
    refine ⟨8775785894812054568735077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11701047859749406091646769 8775785894812054568735077)
    ·
      refine ⟨1645459855277260231637827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8775785894812054568735077 1645459855277260231637827)
      ·
        refine ⟨2468189782915890347456741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645459855277260231637827 2468189782915890347456741)
        ·
          refine ⟨462785584296729440148139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2468189782915890347456741 462785584296729440148139)
          ·
            refine ⟨694178376445094160222209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462785584296729440148139 694178376445094160222209)
            ·
              refine ⟨520633782333820620166657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694178376445094160222209 520633782333820620166657)
              ·
                refine ⟨390475336750365465124993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520633782333820620166657 390475336750365465124993)
                ·
                  refine ⟨292856502562774098843745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390475336750365465124993 292856502562774098843745)
                  ·
                    rfl

theorem cell20_641628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_641628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641628 prefixEnd_641628 := by exact prefixLift 641628
  have htrace : WordTrace (prefixWord ++ tailWord_641628) baseStart_641628 baseEnd_641628 := by
    simpa [prefixWord, tailWord_641628, baseEnd_641628] using wordTrace_append hprefix tailTrace_641628
  have hstable : (prefixWord ++ tailWord_641628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641628).length < 2 ^ (prefixWord ++ tailWord_641628).sum := by decide
  have hdescent : baseEnd_641628 < baseStart_641628 := by decide
  rcases family_descends (prefixWord ++ tailWord_641628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641653 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_641653 : Nat := 118140960795 + 641653 * 2 ^ 59
def prefixEnd_641653 : Nat := 4983230072969 + 3 ^ 40 * 641653 * 2
def baseEnd_641653 : Nat := 292867913243985123010309

theorem tailTrace_641653 : CollatzResearch.WordTrace tailWord_641653 prefixEnd_641653 292867913243985123010309 := by
  unfold tailWord_641653
  simp only [CollatzResearch.WordTrace]
  refine ⟨23403007544408241452953613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15602005029605494301969075 23403007544408241452953613)
  ·
    refine ⟨8776127829153090544857605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23403007544408241452953613 8776127829153090544857605)
    ·
      refine ⟨1645523967966204477160801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8776127829153090544857605 1645523967966204477160801)
      ·
        refine ⟨1234142975974653357870601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1645523967966204477160801 1234142975974653357870601)
        ·
          refine ⟨925607231980990018402951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234142975974653357870601 925607231980990018402951)
          ·
            refine ⟨1388410847971485027604427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925607231980990018402951 1388410847971485027604427)
            ·
              refine ⟨2082616271957227541406641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388410847971485027604427 2082616271957227541406641)
              ·
                refine ⟨1561962203967920656054981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2082616271957227541406641 1561962203967920656054981)
                ·
                  refine ⟨292867913243985123010309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1561962203967920656054981 292867913243985123010309)
                  ·
                    rfl

theorem cell20_641653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_641653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641653 prefixEnd_641653 := by exact prefixLift 641653
  have htrace : WordTrace (prefixWord ++ tailWord_641653) baseStart_641653 baseEnd_641653 := by
    simpa [prefixWord, tailWord_641653, baseEnd_641653] using wordTrace_append hprefix tailTrace_641653
  have hstable : (prefixWord ++ tailWord_641653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641653).length < 2 ^ (prefixWord ++ tailWord_641653).sum := by decide
  have hdescent : baseEnd_641653 < baseStart_641653 := by decide
  rcases family_descends (prefixWord ++ tailWord_641653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641657 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_641657 : Nat := 118140960795 + 641657 * 2 ^ 59
def prefixEnd_641657 : Nat := 4983230072969 + 3 ^ 40 * 641657 * 2
def baseEnd_641657 : Nat := 292869738952978886876959

theorem tailTrace_641657 : CollatzResearch.WordTrace tailWord_641657 prefixEnd_641657 292869738952978886876959 := by
  unfold tailWord_641657
  simp only [CollatzResearch.WordTrace]
  refine ⟨23403153436393750136099225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15602102290929166757399483 23403153436393750136099225)
  ·
    refine ⟨17552365077295312602074419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23403153436393750136099225 17552365077295312602074419)
    ·
      refine ⟨26328547615942968903111629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17552365077295312602074419 26328547615942968903111629)
      ·
        refine ⟨9873205355978613338666861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26328547615942968903111629 9873205355978613338666861)
        ·
          refine ⟨3702452008491980002000073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9873205355978613338666861 3702452008491980002000073)
          ·
            refine ⟨2776839006368985001500055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3702452008491980002000073 2776839006368985001500055)
            ·
              refine ⟨4165258509553477502250083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776839006368985001500055 4165258509553477502250083)
              ·
                refine ⟨6247887764330216253375125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165258509553477502250083 6247887764330216253375125)
                ·
                  refine ⟨292869738952978886876959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6247887764330216253375125 292869738952978886876959)
                  ·
                    rfl

theorem cell20_641657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_641657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641657 prefixEnd_641657 := by exact prefixLift 641657
  have htrace : WordTrace (prefixWord ++ tailWord_641657) baseStart_641657 baseEnd_641657 := by
    simpa [prefixWord, tailWord_641657, baseEnd_641657] using wordTrace_append hprefix tailTrace_641657
  have hstable : (prefixWord ++ tailWord_641657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641657).length < 2 ^ (prefixWord ++ tailWord_641657).sum := by decide
  have hdescent : baseEnd_641657 < baseStart_641657 := by decide
  rcases family_descends (prefixWord ++ tailWord_641657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641684 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_641684 : Nat := 118140960795 + 641684 * 2 ^ 59
def prefixEnd_641684 : Nat := 4983230072969 + 3 ^ 40 * 641684 * 2
def baseEnd_641684 : Nat := 292882062488686792976849

theorem tailTrace_641684 : CollatzResearch.WordTrace tailWord_641684 prefixEnd_641684 292882062488686792976849 := by
  unfold tailWord_641684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702069103647966873666053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15602758804863955831554737 11702069103647966873666053)
  ·
    refine ⟨2194137956933993788812385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11702069103647966873666053 2194137956933993788812385)
    ·
      refine ⟨1645603467700495341609289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2194137956933993788812385 1645603467700495341609289)
      ·
        refine ⟨1234202600775371506206967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1645603467700495341609289 1234202600775371506206967)
        ·
          refine ⟨1851303901163057259310451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234202600775371506206967 1851303901163057259310451)
          ·
            refine ⟨2776955851744585888965677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851303901163057259310451 2776955851744585888965677)
            ·
              refine ⟨1041358444404219708362129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776955851744585888965677 1041358444404219708362129)
              ·
                refine ⟨781018833303164781271597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041358444404219708362129 781018833303164781271597)
                ·
                  refine ⟨292882062488686792976849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781018833303164781271597 292882062488686792976849)
                  ·
                    rfl

theorem cell20_641684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_641684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641684 prefixEnd_641684 := by exact prefixLift 641684
  have htrace : WordTrace (prefixWord ++ tailWord_641684) baseStart_641684 baseEnd_641684 := by
    simpa [prefixWord, tailWord_641684, baseEnd_641684] using wordTrace_append hprefix tailTrace_641684
  have hstable : (prefixWord ++ tailWord_641684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641684).length < 2 ^ (prefixWord ++ tailWord_641684).sum := by decide
  have hdescent : baseEnd_641684 < baseStart_641684 := by decide
  rcases family_descends (prefixWord ++ tailWord_641684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641688 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_641688 : Nat := 118140960795 + 641688 * 2 ^ 59
def prefixEnd_641688 : Nat := 4983230072969 + 3 ^ 40 * 641688 * 2
def baseEnd_641688 : Nat := 292883888197680556843499

theorem tailTrace_641688 : CollatzResearch.WordTrace tailWord_641688 prefixEnd_641688 292883888197680556843499 := by
  unfold tailWord_641688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702142049640721215238859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15602856066187628286985145 11702142049640721215238859)
  ·
    refine ⟨17553213074461081822858289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702142049640721215238859 17553213074461081822858289)
    ·
      refine ⟨13164909805845811367143717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17553213074461081822858289 13164909805845811367143717)
      ·
        refine ⟨2468420588596089631339447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13164909805845811367143717 2468420588596089631339447)
        ·
          refine ⟨3702630882894134447009171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468420588596089631339447 3702630882894134447009171)
          ·
            refine ⟨5553946324341201670513757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702630882894134447009171 5553946324341201670513757)
            ·
              refine ⟨2082729871627950626442659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5553946324341201670513757 2082729871627950626442659)
              ·
                refine ⟨3124094807441925939663989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082729871627950626442659 3124094807441925939663989)
                ·
                  refine ⟨292883888197680556843499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124094807441925939663989 292883888197680556843499)
                  ·
                    rfl

theorem cell20_641688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_641688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641688 prefixEnd_641688 := by exact prefixLift 641688
  have htrace : WordTrace (prefixWord ++ tailWord_641688) baseStart_641688 baseEnd_641688 := by
    simpa [prefixWord, tailWord_641688, baseEnd_641688] using wordTrace_append hprefix tailTrace_641688
  have hstable : (prefixWord ++ tailWord_641688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641688).length < 2 ^ (prefixWord ++ tailWord_641688).sum := by decide
  have hdescent : baseEnd_641688 < baseStart_641688 := by decide
  rcases family_descends (prefixWord ++ tailWord_641688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641719 : List Nat := [1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_641719 : Nat := 118140960795 + 641719 * 2 ^ 59
def prefixEnd_641719 : Nat := 4983230072969 + 3 ^ 40 * 641719 * 2
def baseEnd_641719 : Nat := 97632679147460742270013

theorem tailTrace_641719 : CollatzResearch.WordTrace tailWord_641719 prefixEnd_641719 97632679147460742270013 := by
  unfold tailWord_641719
  simp only [CollatzResearch.WordTrace]
  refine ⟨23405414762169134724856211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15603609841446089816570807 23405414762169134724856211)
  ·
    refine ⟨35108122143253702087284317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23405414762169134724856211 35108122143253702087284317)
    ·
      refine ⟨13165545803720138282731619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35108122143253702087284317 13165545803720138282731619)
      ·
        refine ⟨19748318705580207424097429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13165545803720138282731619 19748318705580207424097429)
        ·
          refine ⟨925702439324072223004567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19748318705580207424097429 925702439324072223004567)
          ·
            refine ⟨1388553658986108334506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925702439324072223004567 1388553658986108334506851)
            ·
              refine ⟨2082830488479162501760277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388553658986108334506851 2082830488479162501760277)
              ·
                refine ⟨97632679147460742270013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2082830488479162501760277 97632679147460742270013)
                ·
                  rfl

theorem cell20_641719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_641719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641719 prefixEnd_641719 := by exact prefixLift 641719
  have htrace : WordTrace (prefixWord ++ tailWord_641719) baseStart_641719 baseEnd_641719 := by
    simpa [prefixWord, tailWord_641719, baseEnd_641719] using wordTrace_append hprefix tailTrace_641719
  have hstable : (prefixWord ++ tailWord_641719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641719).length < 2 ^ (prefixWord ++ tailWord_641719).sum := by decide
  have hdescent : baseEnd_641719 < baseStart_641719 := by decide
  rcases family_descends (prefixWord ++ tailWord_641719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641726 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_641726 : Nat := 118140960795 + 641726 * 2 ^ 59
def prefixEnd_641726 : Nat := 4983230072969 + 3 ^ 40 * 641726 * 2
def baseEnd_641726 : Nat := 292901232433121313576677

theorem tailTrace_641726 : CollatzResearch.WordTrace tailWord_641726 prefixEnd_641726 292901232433121313576677 := by
  unfold tailWord_641726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925708759142971865045129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15603780048762516613574021 2925708759142971865045129)
  ·
    refine ⟨2194281569357228898783847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2925708759142971865045129 2194281569357228898783847)
    ·
      refine ⟨3291422354035843348175771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194281569357228898783847 3291422354035843348175771)
      ·
        refine ⟨4937133531053765022263657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3291422354035843348175771 4937133531053765022263657)
        ·
          refine ⟨3702850148290323766697743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937133531053765022263657 3702850148290323766697743)
          ·
            refine ⟨5554275222435485650046615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702850148290323766697743 5554275222435485650046615)
            ·
              refine ⟨8331412833653228475069923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554275222435485650046615 8331412833653228475069923)
              ·
                refine ⟨12497119250479842712604885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331412833653228475069923 12497119250479842712604885)
                ·
                  refine ⟨292901232433121313576677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12497119250479842712604885 292901232433121313576677)
                  ·
                    rfl

theorem cell20_641726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_641726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641726 prefixEnd_641726 := by exact prefixLift 641726
  have htrace : WordTrace (prefixWord ++ tailWord_641726) baseStart_641726 baseEnd_641726 := by
    simpa [prefixWord, tailWord_641726, baseEnd_641726] using wordTrace_append hprefix tailTrace_641726
  have hstable : (prefixWord ++ tailWord_641726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641726).length < 2 ^ (prefixWord ++ tailWord_641726).sum := by decide
  have hdescent : baseEnd_641726 < baseStart_641726 := by decide
  rcases family_descends (prefixWord ++ tailWord_641726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641746 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_641746 : Nat := 118140960795 + 641746 * 2 ^ 59
def prefixEnd_641746 : Nat := 4983230072969 + 3 ^ 40 * 641746 * 2
def baseEnd_641746 : Nat := 292910360978090132909929

theorem tailTrace_641746 : CollatzResearch.WordTrace tailWord_641746 prefixEnd_641746 292910360978090132909929 := by
  unfold tailWord_641746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851599883267829584022273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15604266355380878890726061 5851599883267829584022273)
  ·
    refine ⟨4388699912450872188016705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5851599883267829584022273 4388699912450872188016705)
    ·
      refine ⟨3291524934338154141012529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4388699912450872188016705 3291524934338154141012529)
      ·
        refine ⟨2468643700753615605759397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291524934338154141012529 2468643700753615605759397)
        ·
          refine ⟨462870693891302926079887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2468643700753615605759397 462870693891302926079887)
          ·
            refine ⟨694306040836954389119831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462870693891302926079887 694306040836954389119831)
            ·
              refine ⟨1041459061255431583679747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694306040836954389119831 1041459061255431583679747)
              ·
                refine ⟨1562188591883147375519621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041459061255431583679747 1562188591883147375519621)
                ·
                  refine ⟨292910360978090132909929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562188591883147375519621 292910360978090132909929)
                  ·
                    rfl

theorem cell20_641746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_641746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641746 prefixEnd_641746 := by exact prefixLift 641746
  have htrace : WordTrace (prefixWord ++ tailWord_641746) baseStart_641746 baseEnd_641746 := by
    simpa [prefixWord, tailWord_641746, baseEnd_641746] using wordTrace_append hprefix tailTrace_641746
  have hstable : (prefixWord ++ tailWord_641746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641746).length < 2 ^ (prefixWord ++ tailWord_641746).sum := by decide
  have hdescent : baseEnd_641746 < baseStart_641746 := by decide
  rcases family_descends (prefixWord ++ tailWord_641746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641785 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_641785 : Nat := 118140960795 + 641785 * 2 ^ 59
def prefixEnd_641785 : Nat := 4983230072969 + 3 ^ 40 * 641785 * 2
def baseEnd_641785 : Nat := 292928161640779330609769

theorem tailTrace_641785 : CollatzResearch.WordTrace tailWord_641785 prefixEnd_641785 292928161640779330609769 := by
  unfold tailWord_641785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23407821979930027996758809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15605214653286685331172539 23407821979930027996758809)
  ·
    refine ⟨17555866484947520997569107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23407821979930027996758809 17555866484947520997569107)
    ·
      refine ⟨26333799727421281496353661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17555866484947520997569107 26333799727421281496353661)
      ·
        refine ⟨9875174897782980561132623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26333799727421281496353661 9875174897782980561132623)
        ·
          refine ⟨14812762346674470841698935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875174897782980561132623 14812762346674470841698935)
          ·
            refine ⟨22219143520011706262548403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14812762346674470841698935 22219143520011706262548403)
            ·
              refine ⟨33328715280017559393822605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22219143520011706262548403 33328715280017559393822605)
              ·
                refine ⟨12498268230006584772683477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33328715280017559393822605 12498268230006584772683477)
                ·
                  refine ⟨292928161640779330609769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12498268230006584772683477 292928161640779330609769)
                  ·
                    rfl

theorem cell20_641785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_641785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641785 prefixEnd_641785 := by exact prefixLift 641785
  have htrace : WordTrace (prefixWord ++ tailWord_641785) baseStart_641785 baseEnd_641785 := by
    simpa [prefixWord, tailWord_641785, baseEnd_641785] using wordTrace_append hprefix tailTrace_641785
  have hstable : (prefixWord ++ tailWord_641785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641785).length < 2 ^ (prefixWord ++ tailWord_641785).sum := by decide
  have hdescent : baseEnd_641785 < baseStart_641785 := by decide
  rcases family_descends (prefixWord ++ tailWord_641785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641826 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_641826 : Nat := 118140960795 + 641826 * 2 ^ 59
def prefixEnd_641826 : Nat := 4983230072969 + 3 ^ 40 * 641826 * 2
def baseEnd_641826 : Nat := 292946875157965410242935

theorem tailTrace_641826 : CollatzResearch.WordTrace tailWord_641826 prefixEnd_641826 292946875157965410242935 := by
  unfold tailWord_641826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852329343195372999750333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15606211581854327999334221 5852329343195372999750333)
  ·
    refine ⟨2194623503698264874906375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5852329343195372999750333 2194623503698264874906375)
    ·
      refine ⟨3291935255547397312359563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194623503698264874906375 3291935255547397312359563)
      ·
        refine ⟨4937902883321095968539345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3291935255547397312359563 4937902883321095968539345)
        ·
          refine ⟨3703427162490821976404509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937902883321095968539345 3703427162490821976404509)
          ·
            refine ⟨1388785185934058241151691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3703427162490821976404509 1388785185934058241151691)
            ·
              refine ⟨2083177778901087361727537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388785185934058241151691 2083177778901087361727537)
              ·
                refine ⟨1562383334175815521295653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083177778901087361727537 1562383334175815521295653)
                ·
                  refine ⟨292946875157965410242935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562383334175815521295653 292946875157965410242935)
                  ·
                    rfl

theorem cell20_641826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_641826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641826 prefixEnd_641826 := by exact prefixLift 641826
  have htrace : WordTrace (prefixWord ++ tailWord_641826) baseStart_641826 baseEnd_641826 := by
    simpa [prefixWord, tailWord_641826, baseEnd_641826] using wordTrace_append hprefix tailTrace_641826
  have hstable : (prefixWord ++ tailWord_641826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641826).length < 2 ^ (prefixWord ++ tailWord_641826).sum := by decide
  have hdescent : baseEnd_641826 < baseStart_641826 := by decide
  rcases family_descends (prefixWord ++ tailWord_641826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641843 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 2]
def baseStart_641843 : Nat := 118140960795 + 641843 * 2 ^ 59
def prefixEnd_641843 : Nat := 4983230072969 + 3 ^ 40 * 641843 * 2
def baseEnd_641843 : Nat := 292954634421188906676199

theorem tailTrace_641843 : CollatzResearch.WordTrace tailWord_641843 prefixEnd_641843 292954634421188906676199 := by
  unfold tailWord_641843
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409937413719903902370183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15606624942479935934913455 23409937413719903902370183)
  ·
    refine ⟨35114906120579855853555275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23409937413719903902370183 35114906120579855853555275)
    ·
      refine ⟨52672359180869783780332913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35114906120579855853555275 52672359180869783780332913)
      ·
        refine ⟨39504269385652337835249685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52672359180869783780332913 39504269385652337835249685)
        ·
          refine ⟨1851762627452453336027329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39504269385652337835249685 1851762627452453336027329)
          ·
            refine ⟨1388821970589340002020497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851762627452453336027329 1388821970589340002020497)
            ·
              refine ⟨1041616477942005001515373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388821970589340002020497 1041616477942005001515373)
              ·
                refine ⟨390606179228251875568265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1041616477942005001515373 390606179228251875568265)
                ·
                  refine ⟨292954634421188906676199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390606179228251875568265 292954634421188906676199)
                  ·
                    rfl

theorem cell20_641843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2].length) (baseStart_641843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641843 prefixEnd_641843 := by exact prefixLift 641843
  have htrace : WordTrace (prefixWord ++ tailWord_641843) baseStart_641843 baseEnd_641843 := by
    simpa [prefixWord, tailWord_641843, baseEnd_641843] using wordTrace_append hprefix tailTrace_641843
  have hstable : (prefixWord ++ tailWord_641843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641843).length < 2 ^ (prefixWord ++ tailWord_641843).sum := by decide
  have hdescent : baseEnd_641843 < baseStart_641843 := by decide
  rcases family_descends (prefixWord ++ tailWord_641843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641853 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 3]
def baseStart_641853 : Nat := 118140960795 + 641853 * 2 ^ 59
def prefixEnd_641853 : Nat := 4983230072969 + 3 ^ 40 * 641853 * 2
def baseEnd_641853 : Nat := 292959198693673316342825

theorem tailTrace_641853 : CollatzResearch.WordTrace tailWord_641853 prefixEnd_641853 292959198693673316342825 := by
  unfold tailWord_641853
  simp only [CollatzResearch.WordTrace]
  refine ⟨23410302143683675610234213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15606868095789117073489475 23410302143683675610234213)
  ·
    refine ⟨4389431651940689176918915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23410302143683675610234213 4389431651940689176918915)
    ·
      refine ⟨6584147477911033765378373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389431651940689176918915 6584147477911033765378373)
      ·
        refine ⟨1234527652108318831008445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6584147477911033765378373 1234527652108318831008445)
        ·
          refine ⟨462947869540619561628167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1234527652108318831008445 462947869540619561628167)
          ·
            refine ⟨694421804310929342442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462947869540619561628167 694421804310929342442251)
            ·
              refine ⟨1041632706466394013663377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694421804310929342442251 1041632706466394013663377)
              ·
                refine ⟨781224529849795510247533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041632706466394013663377 781224529849795510247533)
                ·
                  refine ⟨292959198693673316342825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781224529849795510247533 292959198693673316342825)
                  ·
                    rfl

theorem cell20_641853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_641853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641853 prefixEnd_641853 := by exact prefixLift 641853
  have htrace : WordTrace (prefixWord ++ tailWord_641853) baseStart_641853 baseEnd_641853 := by
    simpa [prefixWord, tailWord_641853, baseEnd_641853] using wordTrace_append hprefix tailTrace_641853
  have hstable : (prefixWord ++ tailWord_641853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641853).length < 2 ^ (prefixWord ++ tailWord_641853).sum := by decide
  have hdescent : baseEnd_641853 < baseStart_641853 := by decide
  rcases family_descends (prefixWord ++ tailWord_641853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641860 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_641860 : Nat := 118140960795 + 641860 * 2 ^ 59
def prefixEnd_641860 : Nat := 4983230072969 + 3 ^ 40 * 641860 * 2
def baseEnd_641860 : Nat := 292962393684412403109463

theorem tailTrace_641860 : CollatzResearch.WordTrace tailWord_641860 prefixEnd_641860 292962393684412403109463 := by
  unfold tailWord_641860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705278727329157902869517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15607038303105543870492689 11705278727329157902869517)
  ·
    refine ⟨4389479522748434213576069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11705278727329157902869517 4389479522748434213576069)
    ·
      refine ⟨823027410515331415045513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4389479522748434213576069 823027410515331415045513)
      ·
        refine ⟨617270557886498561284135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823027410515331415045513 617270557886498561284135)
        ·
          refine ⟨925905836829747841926203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617270557886498561284135 925905836829747841926203)
          ·
            refine ⟨1388858755244621762889305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925905836829747841926203 1388858755244621762889305)
            ·
              refine ⟨1041644066433466322166979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388858755244621762889305 1041644066433466322166979)
              ·
                refine ⟨1562466099650199483250469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041644066433466322166979 1562466099650199483250469)
                ·
                  refine ⟨292962393684412403109463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562466099650199483250469 292962393684412403109463)
                  ·
                    rfl

theorem cell20_641860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_641860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641860 prefixEnd_641860 := by exact prefixLift 641860
  have htrace : WordTrace (prefixWord ++ tailWord_641860) baseStart_641860 baseEnd_641860 := by
    simpa [prefixWord, tailWord_641860, baseEnd_641860] using wordTrace_append hprefix tailTrace_641860
  have hstable : (prefixWord ++ tailWord_641860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641860).length < 2 ^ (prefixWord ++ tailWord_641860).sum := by decide
  have hdescent : baseEnd_641860 < baseStart_641860 := by decide
  rcases family_descends (prefixWord ++ tailWord_641860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641864 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_641864 : Nat := 118140960795 + 641864 * 2 ^ 59
def prefixEnd_641864 : Nat := 4983230072969 + 3 ^ 40 * 641864 * 2
def baseEnd_641864 : Nat := 292964219393406166976113

theorem tailTrace_641864 : CollatzResearch.WordTrace tailWord_641864 prefixEnd_641864 292964219393406166976113 := by
  unfold tailWord_641864
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705351673321912244442323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15607135564429216325923097 11705351673321912244442323)
  ·
    refine ⟨17558027509982868366663485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11705351673321912244442323 17558027509982868366663485)
    ·
      refine ⟨6584260316243575637498807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17558027509982868366663485 6584260316243575637498807)
      ·
        refine ⟨9876390474365363456248211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6584260316243575637498807 9876390474365363456248211)
        ·
          refine ⟨14814585711548045184372317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876390474365363456248211 14814585711548045184372317)
          ·
            refine ⟨5555469641830516944139619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14814585711548045184372317 5555469641830516944139619)
            ·
              refine ⟨8333204462745775416209429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555469641830516944139619 8333204462745775416209429)
              ·
                refine ⟨390618959191208222634817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8333204462745775416209429 390618959191208222634817)
                ·
                  refine ⟨292964219393406166976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390618959191208222634817 292964219393406166976113)
                  ·
                    rfl

theorem cell20_641864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_641864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641864 prefixEnd_641864 := by exact prefixLift 641864
  have htrace : WordTrace (prefixWord ++ tailWord_641864) baseStart_641864 baseEnd_641864 := by
    simpa [prefixWord, tailWord_641864, baseEnd_641864] using wordTrace_append hprefix tailTrace_641864
  have hstable : (prefixWord ++ tailWord_641864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641864).length < 2 ^ (prefixWord ++ tailWord_641864).sum := by decide
  have hdescent : baseEnd_641864 < baseStart_641864 := by decide
  rcases family_descends (prefixWord ++ tailWord_641864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641899 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_641899 : Nat := 118140960795 + 641899 * 2 ^ 59
def prefixEnd_641899 : Nat := 4983230072969 + 3 ^ 40 * 641899 * 2
def baseEnd_641899 : Nat := 292980194347101600809303

theorem tailTrace_641899 : CollatzResearch.WordTrace tailWord_641899 prefixEnd_641899 292980194347101600809303 := by
  unfold tailWord_641899
  simp only [CollatzResearch.WordTrace]
  refine ⟨23411979901517025466408751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15607986601011350310939167 23411979901517025466408751)
  ·
    refine ⟨35117969852275538199613127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23411979901517025466408751 35117969852275538199613127)
    ·
      refine ⟨52676954778413307299419691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35117969852275538199613127 52676954778413307299419691)
      ·
        refine ⟨79015432167619960949129537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52676954778413307299419691 79015432167619960949129537)
        ·
          refine ⟨59261574125714970711847153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79015432167619960949129537 59261574125714970711847153)
          ·
            refine ⟨44446180594286228033885365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59261574125714970711847153 44446180594286228033885365)
            ·
              refine ⟨4166829430714333878176753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44446180594286228033885365 4166829430714333878176753)
              ·
                refine ⟨3125122073035750408632565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166829430714333878176753 3125122073035750408632565)
                ·
                  refine ⟨292980194347101600809303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3125122073035750408632565 292980194347101600809303)
                  ·
                    rfl

theorem cell20_641899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_641899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641899 prefixEnd_641899 := by exact prefixLift 641899
  have htrace : WordTrace (prefixWord ++ tailWord_641899) baseStart_641899 baseEnd_641899 := by
    simpa [prefixWord, tailWord_641899, baseEnd_641899] using wordTrace_append hprefix tailTrace_641899
  have hstable : (prefixWord ++ tailWord_641899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641899).length < 2 ^ (prefixWord ++ tailWord_641899).sum := by decide
  have hdescent : baseEnd_641899 < baseStart_641899 := by decide
  rcases family_descends (prefixWord ++ tailWord_641899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641909 : List Nat := [1, 3, 4, 1, 1, 4, 6]
def baseStart_641909 : Nat := 118140960795 + 641909 * 2 ^ 59
def prefixEnd_641909 : Nat := 4983230072969 + 3 ^ 40 * 641909 * 2
def baseEnd_641909 : Nat := 32553862068842890052881

theorem tailTrace_641909 : CollatzResearch.WordTrace tailWord_641909 prefixEnd_641909 32553862068842890052881 := by
  unfold tailWord_641909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23412344631480797174272781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15608229754320531449515187 23412344631480797174272781)
  ·
    refine ⟨8779629236805298940352293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23412344631480797174272781 8779629236805298940352293)
    ·
      refine ⟨1646180481900993551316055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8779629236805298940352293 1646180481900993551316055)
      ·
        refine ⟨2469270722851490326974083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646180481900993551316055 2469270722851490326974083)
        ·
          refine ⟨3703906084277235490461125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469270722851490326974083 3703906084277235490461125)
          ·
            refine ⟨694482390801981654461461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3703906084277235490461125 694482390801981654461461)
            ·
              refine ⟨32553862068842890052881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 694482390801981654461461 32553862068842890052881)
              ·
                rfl

theorem cell20_641909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_641909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641909 prefixEnd_641909 := by exact prefixLift 641909
  have htrace : WordTrace (prefixWord ++ tailWord_641909) baseStart_641909 baseEnd_641909 := by
    simpa [prefixWord, tailWord_641909, baseEnd_641909] using wordTrace_append hprefix tailTrace_641909
  have hstable : (prefixWord ++ tailWord_641909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641909).length < 2 ^ (prefixWord ++ tailWord_641909).sum := by decide
  have hdescent : baseEnd_641909 < baseStart_641909 := by decide
  rcases family_descends (prefixWord ++ tailWord_641909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641975 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_641975 : Nat := 118140960795 + 641975 * 2 ^ 59
def prefixEnd_641975 : Nat := 4983230072969 + 3 ^ 40 * 641975 * 2
def baseEnd_641975 : Nat := 293014882817983114275659

theorem tailTrace_641975 : CollatzResearch.WordTrace tailWord_641975 prefixEnd_641975 293014882817983114275659 := by
  unfold tailWord_641975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23414751849241690446175379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15609834566161126964116919 23414751849241690446175379)
  ·
    refine ⟨35122127773862535669263069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23414751849241690446175379 35122127773862535669263069)
    ·
      refine ⟨13170797915198450875973651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35122127773862535669263069 13170797915198450875973651)
      ·
        refine ⟨19756196872797676313960477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170797915198450875973651 19756196872797676313960477)
        ·
          refine ⟨7408573827299128617735179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19756196872797676313960477 7408573827299128617735179)
          ·
            refine ⟨11112860740948692926602769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408573827299128617735179 11112860740948692926602769)
            ·
              refine ⟨8334645555711519694952077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11112860740948692926602769 8334645555711519694952077)
              ·
                refine ⟨3125492083391819885607029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8334645555711519694952077 3125492083391819885607029)
                ·
                  refine ⟨293014882817983114275659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3125492083391819885607029 293014882817983114275659)
                  ·
                    rfl

theorem cell20_641975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_641975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641975 prefixEnd_641975 := by exact prefixLift 641975
  have htrace : WordTrace (prefixWord ++ tailWord_641975) baseStart_641975 baseEnd_641975 := by
    simpa [prefixWord, tailWord_641975, baseEnd_641975] using wordTrace_append hprefix tailTrace_641975
  have hstable : (prefixWord ++ tailWord_641975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641975).length < 2 ^ (prefixWord ++ tailWord_641975).sum := by decide
  have hdescent : baseEnd_641975 < baseStart_641975 := by decide
  rcases family_descends (prefixWord ++ tailWord_641975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641978 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_641978 : Nat := 118140960795 + 641978 * 2 ^ 59
def prefixEnd_641978 : Nat := 4983230072969 + 3 ^ 40 * 641978 * 2
def baseEnd_641978 : Nat := 293016252099728437175647

theorem tailTrace_641978 : CollatzResearch.WordTrace tailWord_641978 prefixEnd_641978 293016252099728437175647 := by
  unfold tailWord_641978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853715317057705489633647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15609907512153881305689725 5853715317057705489633647)
  ·
    refine ⟨8780572975586558234450471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5853715317057705489633647 8780572975586558234450471)
    ·
      refine ⟨13170859463379837351675707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8780572975586558234450471 13170859463379837351675707)
      ·
        refine ⟨19756289195069756027513561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170859463379837351675707 19756289195069756027513561)
        ·
          refine ⟨14817216896302317020635171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19756289195069756027513561 14817216896302317020635171)
          ·
            refine ⟨22225825344453475530952757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14817216896302317020635171 22225825344453475530952757)
            ·
              refine ⟨2083671126042513331026821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22225825344453475530952757 2083671126042513331026821)
              ·
                refine ⟨390688336132971249567529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2083671126042513331026821 390688336132971249567529)
                ·
                  refine ⟨293016252099728437175647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390688336132971249567529 293016252099728437175647)
                  ·
                    rfl

theorem cell20_641978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_641978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641978 prefixEnd_641978 := by exact prefixLift 641978
  have htrace : WordTrace (prefixWord ++ tailWord_641978) baseStart_641978 baseEnd_641978 := by
    simpa [prefixWord, tailWord_641978, baseEnd_641978] using wordTrace_append hprefix tailTrace_641978
  have hstable : (prefixWord ++ tailWord_641978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641978).length < 2 ^ (prefixWord ++ tailWord_641978).sum := by decide
  have hdescent : baseEnd_641978 < baseStart_641978 := by decide
  rcases family_descends (prefixWord ++ tailWord_641978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641999 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_641999 : Nat := 118140960795 + 641999 * 2 ^ 59
def prefixEnd_641999 : Nat := 4983230072969 + 3 ^ 40 * 641999 * 2
def baseEnd_641999 : Nat := 293025837071945697475561

theorem tailTrace_641999 : CollatzResearch.WordTrace tailWord_641999 prefixEnd_641999 293025837071945697475561 := by
  unfold tailWord_641999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415627201154742545049051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15610418134103161696699367 23415627201154742545049051)
  ·
    refine ⟨35123440801732113817573577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23415627201154742545049051 35123440801732113817573577)
    ·
      refine ⟨26342580601299085363180183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35123440801732113817573577 26342580601299085363180183)
      ·
        refine ⟨39513870901948628044770275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26342580601299085363180183 39513870901948628044770275)
        ·
          refine ⟨59270806352922942067155413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39513870901948628044770275 59270806352922942067155413)
          ·
            refine ⟨1389159523896631454698955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59270806352922942067155413 1389159523896631454698955)
            ·
              refine ⟨2083739285844947182048433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389159523896631454698955 2083739285844947182048433)
              ·
                refine ⟨1562804464383710386536325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083739285844947182048433 1562804464383710386536325)
                ·
                  refine ⟨293025837071945697475561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562804464383710386536325 293025837071945697475561)
                  ·
                    rfl

theorem cell20_641999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_641999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_641999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_641999 prefixEnd_641999 := by exact prefixLift 641999
  have htrace : WordTrace (prefixWord ++ tailWord_641999) baseStart_641999 baseEnd_641999 := by
    simpa [prefixWord, tailWord_641999, baseEnd_641999] using wordTrace_append hprefix tailTrace_641999
  have hstable : (prefixWord ++ tailWord_641999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641999).length < 2 ^ (prefixWord ++ tailWord_641999).sum := by decide
  have hdescent : baseEnd_641999 < baseStart_641999 := by decide
  rcases family_descends (prefixWord ++ tailWord_641999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642002 : List Nat := [3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_642002 : Nat := 118140960795 + 642002 * 2 ^ 59
def prefixEnd_642002 : Nat := 4983230072969 + 3 ^ 40 * 642002 * 2
def baseEnd_642002 : Nat := 97675735451230340125183

theorem tailTrace_642002 : CollatzResearch.WordTrace tailWord_642002 prefixEnd_642002 97675735451230340125183 := by
  unfold tailWord_642002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853934155035968514352065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15610491080095916038272173 5853934155035968514352065)
  ·
    refine ⟨4390450616276976385764049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5853934155035968514352065 4390450616276976385764049)
    ·
      refine ⟨3292837962207732289323037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390450616276976385764049 3292837962207732289323037)
      ·
        refine ⟨1234814235827899608496139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3292837962207732289323037 1234814235827899608496139)
        ·
          refine ⟨1852221353741849412744209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234814235827899608496139 1852221353741849412744209)
          ·
            refine ⟨1389166015306387059558157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852221353741849412744209 1389166015306387059558157)
            ·
              refine ⟨520937255739895147334309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1389166015306387059558157 520937255739895147334309)
              ·
                refine ⟨97675735451230340125183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520937255739895147334309 97675735451230340125183)
                ·
                  rfl

theorem cell20_642002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_642002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642002 prefixEnd_642002 := by exact prefixLift 642002
  have htrace : WordTrace (prefixWord ++ tailWord_642002) baseStart_642002 baseEnd_642002 := by
    simpa [prefixWord, tailWord_642002, baseEnd_642002] using wordTrace_append hprefix tailTrace_642002
  have hstable : (prefixWord ++ tailWord_642002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642002).length < 2 ^ (prefixWord ++ tailWord_642002).sum := by decide
  have hdescent : baseEnd_642002 < baseStart_642002 := by decide
  rcases family_descends (prefixWord ++ tailWord_642002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642071 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 2]
def baseStart_642071 : Nat := 118140960795 + 642071 * 2 ^ 59
def prefixEnd_642071 : Nat := 4983230072969 + 3 ^ 40 * 642071 * 2
def baseEnd_642071 : Nat := 293058699833833447075267

theorem tailTrace_642071 : CollatzResearch.WordTrace tailWord_642071 prefixEnd_642071 293058699833833447075267 := by
  unfold tailWord_642071
  simp only [CollatzResearch.WordTrace]
  refine ⟨23418253256893898841670067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15612168837929265894446711 23418253256893898841670067)
  ·
    refine ⟨35127379885340848262505101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23418253256893898841670067 35127379885340848262505101)
    ·
      refine ⟨13172767457002818098439413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35127379885340848262505101 13172767457002818098439413)
      ·
        refine ⟨1234946949094014196728695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13172767457002818098439413 1234946949094014196728695)
        ·
          refine ⟨1852420423641021295093043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234946949094014196728695 1852420423641021295093043)
          ·
            refine ⟨2778630635461531942639565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852420423641021295093043 2778630635461531942639565)
            ·
              refine ⟨1041986488298074478489837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2778630635461531942639565 1041986488298074478489837)
              ·
                refine ⟨390744933111777929433689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1041986488298074478489837 390744933111777929433689)
                ·
                  refine ⟨293058699833833447075267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390744933111777929433689 293058699833833447075267)
                  ·
                    rfl

theorem cell20_642071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2].length) (baseStart_642071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642071 prefixEnd_642071 := by exact prefixLift 642071
  have htrace : WordTrace (prefixWord ++ tailWord_642071) baseStart_642071 baseEnd_642071 := by
    simpa [prefixWord, tailWord_642071, baseEnd_642071] using wordTrace_append hprefix tailTrace_642071
  have hstable : (prefixWord ++ tailWord_642071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642071).length < 2 ^ (prefixWord ++ tailWord_642071).sum := by decide
  have hdescent : baseEnd_642071 < baseStart_642071 := by decide
  rcases family_descends (prefixWord ++ tailWord_642071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642082 : List Nat := [3, 3, 1, 1, 1, 3, 8]
def baseStart_642082 : Nat := 118140960795 + 642082 * 2 ^ 59
def prefixEnd_642082 : Nat := 4983230072969 + 3 ^ 40 * 642082 * 2
def baseEnd_642082 : Nat := 32562635614840699745395

theorem tailTrace_642082 : CollatzResearch.WordTrace tailWord_642082 prefixEnd_642082 32562635614840699745395 := by
  unfold tailWord_642082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854663614963511930080125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15612436306569365146880333 5854663614963511930080125)
  ·
    refine ⟨2195498855611316973780047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5854663614963511930080125 2195498855611316973780047)
    ·
      refine ⟨3293248283416975460670071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195498855611316973780047 3293248283416975460670071)
      ·
        refine ⟨4939872425125463191005107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293248283416975460670071 4939872425125463191005107)
        ·
          refine ⟨7409808637688194786507661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939872425125463191005107 7409808637688194786507661)
          ·
            refine ⟨2778678239133073044940373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7409808637688194786507661 2778678239133073044940373)
            ·
              refine ⟨32562635614840699745395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2778678239133073044940373 32562635614840699745395)
              ·
                rfl

theorem cell20_642082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_642082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642082 prefixEnd_642082 := by exact prefixLift 642082
  have htrace : WordTrace (prefixWord ++ tailWord_642082) baseStart_642082 baseEnd_642082 := by
    simpa [prefixWord, tailWord_642082, baseEnd_642082] using wordTrace_append hprefix tailTrace_642082
  have hstable : (prefixWord ++ tailWord_642082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642082).length < 2 ^ (prefixWord ++ tailWord_642082).sum := by decide
  have hdescent : baseEnd_642082 < baseStart_642082 := by decide
  rcases family_descends (prefixWord ++ tailWord_642082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642102 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_642102 : Nat := 118140960795 + 642102 * 2 ^ 59
def prefixEnd_642102 : Nat := 4983230072969 + 3 ^ 40 * 642102 * 2
def baseEnd_642102 : Nat := 293072849078535117041807

theorem tailTrace_642102 : CollatzResearch.WordTrace tailWord_642102 prefixEnd_642102 293072849078535117041807 := by
  unfold tailWord_642102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463711494986349446003035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15612922613187727424032373 1463711494986349446003035)
  ·
    refine ⟨2195567242479524169004553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1463711494986349446003035 2195567242479524169004553)
    ·
      refine ⟨1646675431859643126753415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195567242479524169004553 1646675431859643126753415)
      ·
        refine ⟨2470013147789464690130123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646675431859643126753415 2470013147789464690130123)
        ·
          refine ⟨3705019721684197035195185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470013147789464690130123 3705019721684197035195185)
          ·
            refine ⟨2778764791263147776396389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3705019721684197035195185 2778764791263147776396389)
            ·
              refine ⟨521018398361840208074323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2778764791263147776396389 521018398361840208074323)
              ·
                refine ⟨781527597542760312111485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521018398361840208074323 781527597542760312111485)
                ·
                  refine ⟨293072849078535117041807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781527597542760312111485 293072849078535117041807)
                  ·
                    rfl

theorem cell20_642102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_642102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642102 prefixEnd_642102 := by exact prefixLift 642102
  have htrace : WordTrace (prefixWord ++ tailWord_642102) baseStart_642102 baseEnd_642102 := by
    simpa [prefixWord, tailWord_642102, baseEnd_642102] using wordTrace_append hprefix tailTrace_642102
  have hstable : (prefixWord ++ tailWord_642102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642102).length < 2 ^ (prefixWord ++ tailWord_642102).sum := by decide
  have hdescent : baseEnd_642102 < baseStart_642102 := by decide
  rcases family_descends (prefixWord ++ tailWord_642102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642144 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_642144 : Nat := 118140960795 + 642144 * 2 ^ 59
def prefixEnd_642144 : Nat := 4983230072969 + 3 ^ 40 * 642144 * 2
def baseEnd_642144 : Nat := 293092019022969637641635

theorem tailTrace_642144 : CollatzResearch.WordTrace tailWord_642144 prefixEnd_642144 293092019022969637641635 := by
  unfold tailWord_642144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710457892814716154538743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15613943857086288206051657 11710457892814716154538743)
  ·
    refine ⟨17565686839222074231808115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710457892814716154538743 17565686839222074231808115)
    ·
      refine ⟨26348530258833111347712173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17565686839222074231808115 26348530258833111347712173)
      ·
        refine ⟨9880698847062416755392065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26348530258833111347712173 9880698847062416755392065)
        ·
          refine ⟨7410524135296812566544049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880698847062416755392065 7410524135296812566544049)
          ·
            refine ⟨5557893101472609424908037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410524135296812566544049 5557893101472609424908037)
            ·
              refine ⟨1042104956526114267170257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5557893101472609424908037 1042104956526114267170257)
              ·
                refine ⟨781578717394585700377693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042104956526114267170257 781578717394585700377693)
                ·
                  refine ⟨293092019022969637641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781578717394585700377693 293092019022969637641635)
                  ·
                    rfl

theorem cell20_642144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_642144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642144 prefixEnd_642144 := by exact prefixLift 642144
  have htrace : WordTrace (prefixWord ++ tailWord_642144) baseStart_642144 baseEnd_642144 := by
    simpa [prefixWord, tailWord_642144, baseEnd_642144] using wordTrace_append hprefix tailTrace_642144
  have hstable : (prefixWord ++ tailWord_642144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642144).length < 2 ^ (prefixWord ++ tailWord_642144).sum := by decide
  have hdescent : baseEnd_642144 < baseStart_642144 := by decide
  rcases family_descends (prefixWord ++ tailWord_642144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642199 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_642199 : Nat := 118140960795 + 642199 * 2 ^ 59
def prefixEnd_642199 : Nat := 4983230072969 + 3 ^ 40 * 642199 * 2
def baseEnd_642199 : Nat := 293117122521633890808077

theorem tailTrace_642199 : CollatzResearch.WordTrace tailWord_642199 prefixEnd_642199 293117122521633890808077 := by
  unfold tailWord_642199
  simp only [CollatzResearch.WordTrace]
  refine ⟨23422921800430176702329651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15615281200286784468219767 23422921800430176702329651)
  ·
    refine ⟨35134382700645265053494477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23422921800430176702329651 35134382700645265053494477)
    ·
      refine ⟨13175393512741974395060429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35134382700645265053494477 13175393512741974395060429)
      ·
        refine ⟨4940772567278240398147661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13175393512741974395060429 4940772567278240398147661)
        ·
          refine ⟨1852789712729340149305373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4940772567278240398147661 1852789712729340149305373)
          ·
            refine ⟨694796142273502555989515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1852789712729340149305373 694796142273502555989515)
            ·
              refine ⟨1042194213410253833984273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694796142273502555989515 1042194213410253833984273)
              ·
                refine ⟨781645660057690375488205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042194213410253833984273 781645660057690375488205)
                ·
                  refine ⟨293117122521633890808077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781645660057690375488205 293117122521633890808077)
                  ·
                    rfl

theorem cell20_642199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_642199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642199 prefixEnd_642199 := by exact prefixLift 642199
  have htrace : WordTrace (prefixWord ++ tailWord_642199) baseStart_642199 baseEnd_642199 := by
    simpa [prefixWord, tailWord_642199, baseEnd_642199] using wordTrace_append hprefix tailTrace_642199
  have hstable : (prefixWord ++ tailWord_642199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642199).length < 2 ^ (prefixWord ++ tailWord_642199).sum := by decide
  have hdescent : baseEnd_642199 < baseStart_642199 := by decide
  rcases family_descends (prefixWord ++ tailWord_642199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642206 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_642206 : Nat := 118140960795 + 642206 * 2 ^ 59
def prefixEnd_642206 : Nat := 4983230072969 + 3 ^ 40 * 642206 * 2
def baseEnd_642206 : Nat := 293120317512372977574715

theorem tailTrace_642206 : CollatzResearch.WordTrace tailWord_642206 prefixEnd_642206 293120317512372977574715 := by
  unfold tailWord_642206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927897138925602112229309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15615451407603211265222981 2927897138925602112229309)
  ·
    refine ⟨1097961427097100792085991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2927897138925602112229309 1097961427097100792085991)
    ·
      refine ⟨1646942140645651188128987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097961427097100792085991 1646942140645651188128987)
      ·
        refine ⟨2470413210968476782193481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646942140645651188128987 2470413210968476782193481)
        ·
          refine ⟨1852809908226357586645111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2470413210968476782193481 1852809908226357586645111)
          ·
            refine ⟨2779214862339536379967667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852809908226357586645111 2779214862339536379967667)
            ·
              refine ⟨4168822293509304569951501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779214862339536379967667 4168822293509304569951501)
              ·
                refine ⟨1563308360065989213731813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4168822293509304569951501 1563308360065989213731813)
                ·
                  refine ⟨293120317512372977574715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563308360065989213731813 293120317512372977574715)
                  ·
                    rfl

theorem cell20_642206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_642206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642206 prefixEnd_642206 := by exact prefixLift 642206
  have htrace : WordTrace (prefixWord ++ tailWord_642206) baseStart_642206 baseEnd_642206 := by
    simpa [prefixWord, tailWord_642206, baseEnd_642206] using wordTrace_append hprefix tailTrace_642206
  have hstable : (prefixWord ++ tailWord_642206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642206).length < 2 ^ (prefixWord ++ tailWord_642206).sum := by decide
  have hdescent : baseEnd_642206 < baseStart_642206 := by decide
  rcases family_descends (prefixWord ++ tailWord_642206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642240 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_642240 : Nat := 118140960795 + 642240 * 2 ^ 59
def prefixEnd_642240 : Nat := 4983230072969 + 3 ^ 40 * 642240 * 2
def baseEnd_642240 : Nat := 293135836038819970441243

theorem tailTrace_642240 : CollatzResearch.WordTrace tailWord_642240 prefixEnd_642240 293135836038819970441243 := by
  unfold tailWord_642240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712208596640820352286087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15616278128854427136381449 11712208596640820352286087)
  ·
    refine ⟨17568312894961230528429131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11712208596640820352286087 17568312894961230528429131)
    ·
      refine ⟨26352469342441845792643697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17568312894961230528429131 26352469342441845792643697)
      ·
        refine ⟨19764352006831384344482773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26352469342441845792643697 19764352006831384344482773)
        ·
          refine ⟨463227000160110570573815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19764352006831384344482773 463227000160110570573815)
          ·
            refine ⟨694840500240165855860723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463227000160110570573815 694840500240165855860723)
            ·
              refine ⟨1042260750360248783791085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694840500240165855860723 1042260750360248783791085)
              ·
                refine ⟨390847781385093293921657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042260750360248783791085 390847781385093293921657)
                ·
                  refine ⟨293135836038819970441243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390847781385093293921657 293135836038819970441243)
                  ·
                    rfl

theorem cell20_642240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_642240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642240 prefixEnd_642240 := by exact prefixLift 642240
  have htrace : WordTrace (prefixWord ++ tailWord_642240) baseStart_642240 baseEnd_642240 := by
    simpa [prefixWord, tailWord_642240, baseEnd_642240] using wordTrace_append hprefix tailTrace_642240
  have hstable : (prefixWord ++ tailWord_642240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642240).length < 2 ^ (prefixWord ++ tailWord_642240).sum := by decide
  have hdescent : baseEnd_642240 < baseStart_642240 := by decide
  rcases family_descends (prefixWord ++ tailWord_642240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642248 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_642248 : Nat := 118140960795 + 642248 * 2 ^ 59
def prefixEnd_642248 : Nat := 4983230072969 + 3 ^ 40 * 642248 * 2
def baseEnd_642248 : Nat := 293139487456807498174543

theorem tailTrace_642248 : CollatzResearch.WordTrace tailWord_642248 prefixEnd_642248 293139487456807498174543 := by
  unfold tailWord_642248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712354488626329035431699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15616472651501772047242265 11712354488626329035431699)
  ·
    refine ⟨17568531732939493553147549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11712354488626329035431699 17568531732939493553147549)
    ·
      refine ⟨6588199399852310082430331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17568531732939493553147549 6588199399852310082430331)
      ·
        refine ⟨9882299099778465123645497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6588199399852310082430331 9882299099778465123645497)
        ·
          refine ⟨7411724324833848842734123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9882299099778465123645497 7411724324833848842734123)
          ·
            refine ⟨11117586487250773264101185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411724324833848842734123 11117586487250773264101185)
            ·
              refine ⟨8338189865438079948075889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11117586487250773264101185 8338189865438079948075889)
              ·
                refine ⟨6253642399078559961056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8338189865438079948075889 6253642399078559961056917)
                ·
                  refine ⟨293139487456807498174543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6253642399078559961056917 293139487456807498174543)
                  ·
                    rfl

theorem cell20_642248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_642248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642248 prefixEnd_642248 := by exact prefixLift 642248
  have htrace : WordTrace (prefixWord ++ tailWord_642248) baseStart_642248 baseEnd_642248 := by
    simpa [prefixWord, tailWord_642248, baseEnd_642248] using wordTrace_append hprefix tailTrace_642248
  have hstable : (prefixWord ++ tailWord_642248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642248).length < 2 ^ (prefixWord ++ tailWord_642248).sum := by decide
  have hdescent : baseEnd_642248 < baseStart_642248 := by decide
  rcases family_descends (prefixWord ++ tailWord_642248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642258 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_642258 : Nat := 118140960795 + 642258 * 2 ^ 59
def prefixEnd_642258 : Nat := 4983230072969 + 3 ^ 40 * 642258 * 2
def baseEnd_642258 : Nat := 293144051729291907841169

theorem tailTrace_642258 : CollatzResearch.WordTrace tailWord_642258 prefixEnd_642258 293144051729291907841169 := by
  unfold tailWord_642258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856268426804107444681857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15616715804810953185818285 5856268426804107444681857)
  ·
    refine ⟨4392201320103080583511393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5856268426804107444681857 4392201320103080583511393)
    ·
      refine ⟨3294150990077310437633545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4392201320103080583511393 3294150990077310437633545)
      ·
        refine ⟨2470613242557982828225159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3294150990077310437633545 2470613242557982828225159)
        ·
          refine ⟨3705919863836974242337739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470613242557982828225159 3705919863836974242337739)
          ·
            refine ⟨5558879795755461363506609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705919863836974242337739 5558879795755461363506609)
            ·
              refine ⟨4169159846816596022629957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558879795755461363506609 4169159846816596022629957)
              ·
                refine ⟨781717471278111754243117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4169159846816596022629957 781717471278111754243117)
                ·
                  refine ⟨293144051729291907841169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781717471278111754243117 293144051729291907841169)
                  ·
                    rfl

theorem cell20_642258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_642258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642258 prefixEnd_642258 := by exact prefixLift 642258
  have htrace : WordTrace (prefixWord ++ tailWord_642258) baseStart_642258 baseEnd_642258 := by
    simpa [prefixWord, tailWord_642258, baseEnd_642258] using wordTrace_append hprefix tailTrace_642258
  have hstable : (prefixWord ++ tailWord_642258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642258).length < 2 ^ (prefixWord ++ tailWord_642258).sum := by decide
  have hdescent : baseEnd_642258 < baseStart_642258 := by decide
  rcases family_descends (prefixWord ++ tailWord_642258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642272 : List Nat := [2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_642272 : Nat := 118140960795 + 642272 * 2 ^ 59
def prefixEnd_642272 : Nat := 4983230072969 + 3 ^ 40 * 642272 * 2
def baseEnd_642272 : Nat := 97716813903590027124815

theorem tailTrace_642272 : CollatzResearch.WordTrace tailWord_642272 prefixEnd_642272 97716813903590027124815 := by
  unfold tailWord_642272
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712792164582855084868535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15617056219443806779824713 11712792164582855084868535)
  ·
    refine ⟨17569188246874282627302803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11712792164582855084868535 17569188246874282627302803)
    ·
      refine ⟨26353782370311423940954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17569188246874282627302803 26353782370311423940954205)
      ·
        refine ⟨9882668388866783977857827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26353782370311423940954205 9882668388866783977857827)
        ·
          refine ⟨14824002583300175966786741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882668388866783977857827 14824002583300175966786741)
          ·
            refine ⟨1389750242184391496886257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14824002583300175966786741 1389750242184391496886257)
            ·
              refine ⟨1042312681638293622664693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389750242184391496886257 1042312681638293622664693)
              ·
                refine ⟨97716813903590027124815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042312681638293622664693 97716813903590027124815)
                ·
                  rfl

theorem cell20_642272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_642272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642272 prefixEnd_642272 := by exact prefixLift 642272
  have htrace : WordTrace (prefixWord ++ tailWord_642272) baseStart_642272 baseEnd_642272 := by
    simpa [prefixWord, tailWord_642272, baseEnd_642272] using wordTrace_append hprefix tailTrace_642272
  have hstable : (prefixWord ++ tailWord_642272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642272).length < 2 ^ (prefixWord ++ tailWord_642272).sum := by decide
  have hdescent : baseEnd_642272 < baseStart_642272 := by decide
  rcases family_descends (prefixWord ++ tailWord_642272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642341 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_642341 : Nat := 118140960795 + 642341 * 2 ^ 59
def prefixEnd_642341 : Nat := 4983230072969 + 3 ^ 40 * 642341 * 2
def baseEnd_642341 : Nat := 293181935190912508074163

theorem tailTrace_642341 : CollatzResearch.WordTrace tailWord_642341 prefixEnd_642341 293181935190912508074163 := by
  unfold tailWord_642341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428100965915734953998877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15618733977277156635999251 23428100965915734953998877)
  ·
    refine ⟨8785537862218400607749579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23428100965915734953998877 8785537862218400607749579)
    ·
      refine ⟨13178306793327600911624369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785537862218400607749579 13178306793327600911624369)
      ·
        refine ⟨9883730094995700683718277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13178306793327600911624369 9883730094995700683718277)
        ·
          refine ⟨1853199392811693878197177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9883730094995700683718277 1853199392811693878197177)
          ·
            refine ⟨1389899544608770408647883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853199392811693878197177 1389899544608770408647883)
            ·
              refine ⟨2084849316913155612971825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389899544608770408647883 2084849316913155612971825)
              ·
                refine ⟨1563636987684866709728869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084849316913155612971825 1563636987684866709728869)
                ·
                  refine ⟨293181935190912508074163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563636987684866709728869 293181935190912508074163)
                  ·
                    rfl

theorem cell20_642341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_642341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642341 prefixEnd_642341 := by exact prefixLift 642341
  have htrace : WordTrace (prefixWord ++ tailWord_642341) baseStart_642341 baseEnd_642341 := by
    simpa [prefixWord, tailWord_642341, baseEnd_642341] using wordTrace_append hprefix tailTrace_642341
  have hstable : (prefixWord ++ tailWord_642341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642341).length < 2 ^ (prefixWord ++ tailWord_642341).sum := by decide
  have hdescent : baseEnd_642341 < baseStart_642341 := by decide
  rcases family_descends (prefixWord ++ tailWord_642341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642362 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_642362 : Nat := 118140960795 + 642362 * 2 ^ 59
def prefixEnd_642362 : Nat := 4983230072969 + 3 ^ 40 * 642362 * 2
def baseEnd_642362 : Nat := 293191520163129768374077

theorem tailTrace_642362 : CollatzResearch.WordTrace tailWord_642362 prefixEnd_642362 293191520163129768374077 := by
  unfold tailWord_642362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857216724709913885128335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15619244599226437027008893 5857216724709913885128335)
  ·
    refine ⟨8785825087064870827692503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5857216724709913885128335 8785825087064870827692503)
    ·
      refine ⟨13178737630597306241538755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785825087064870827692503 13178737630597306241538755)
      ·
        refine ⟨19768106445895959362308133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13178737630597306241538755 19768106445895959362308133)
        ·
          refine ⟨3706519958605492380432775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19768106445895959362308133 3706519958605492380432775)
          ·
            refine ⟨5559779937908238570649163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706519958605492380432775 5559779937908238570649163)
            ·
              refine ⟨8339669906862357855973745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559779937908238570649163 8339669906862357855973745)
              ·
                refine ⟨6254752430146768391980309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8339669906862357855973745 6254752430146768391980309)
                ·
                  refine ⟨293191520163129768374077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6254752430146768391980309 293191520163129768374077)
                  ·
                    rfl

theorem cell20_642362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_642362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642362 prefixEnd_642362 := by exact prefixLift 642362
  have htrace : WordTrace (prefixWord ++ tailWord_642362) baseStart_642362 baseEnd_642362 := by
    simpa [prefixWord, tailWord_642362, baseEnd_642362] using wordTrace_append hprefix tailTrace_642362
  have hstable : (prefixWord ++ tailWord_642362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642362).length < 2 ^ (prefixWord ++ tailWord_642362).sum := by decide
  have hdescent : baseEnd_642362 < baseStart_642362 := by decide
  rcases family_descends (prefixWord ++ tailWord_642362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642365 : List Nat := [1, 4, 1, 5, 1, 1, 7]
def baseStart_642365 : Nat := 118140960795 + 642365 * 2 ^ 59
def prefixEnd_642365 : Nat := 4983230072969 + 3 ^ 40 * 642365 * 2
def baseEnd_642365 : Nat := 32576987716097232363785

theorem tailTrace_642365 : CollatzResearch.WordTrace tailWord_642365 prefixEnd_642365 32576987716097232363785 := by
  unfold tailWord_642365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428976317828787052872549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15619317545219191368581699 23428976317828787052872549)
  ·
    refine ⟨4392933059592897572413603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23428976317828787052872549 4392933059592897572413603)
    ·
      refine ⟨6589399589389346358620405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392933059592897572413603 6589399589389346358620405)
      ·
        refine ⟨617756211505251221120663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6589399589389346358620405 617756211505251221120663)
        ·
          refine ⟨926634317257876831680995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617756211505251221120663 926634317257876831680995)
          ·
            refine ⟨1389951475886815247521493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926634317257876831680995 1389951475886815247521493)
            ·
              refine ⟨32576987716097232363785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1389951475886815247521493 32576987716097232363785)
              ·
                rfl

theorem cell20_642365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_642365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642365 prefixEnd_642365 := by exact prefixLift 642365
  have htrace : WordTrace (prefixWord ++ tailWord_642365) baseStart_642365 baseEnd_642365 := by
    simpa [prefixWord, tailWord_642365, baseEnd_642365] using wordTrace_append hprefix tailTrace_642365
  have hstable : (prefixWord ++ tailWord_642365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642365).length < 2 ^ (prefixWord ++ tailWord_642365).sum := by decide
  have hdescent : baseEnd_642365 < baseStart_642365 := by decide
  rcases family_descends (prefixWord ++ tailWord_642365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642389 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_642389 : Nat := 118140960795 + 642389 * 2 ^ 59
def prefixEnd_642389 : Nat := 4983230072969 + 3 ^ 40 * 642389 * 2
def baseEnd_642389 : Nat := 293203843698837674473967

theorem tailTrace_642389 : CollatzResearch.WordTrace tailWord_642389 prefixEnd_642389 293203843698837674473967 := by
  unfold tailWord_642389
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429851669741839151746221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15619901113161226101164147 23429851669741839151746221)
  ·
    refine ⟨8786194376153189681904833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23429851669741839151746221 8786194376153189681904833)
    ·
      refine ⟨6589645782114892261428625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8786194376153189681904833 6589645782114892261428625)
      ·
        refine ⟨4942234336586169196071469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6589645782114892261428625 4942234336586169196071469)
        ·
          refine ⟨1853337876219813448526801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4942234336586169196071469 1853337876219813448526801)
          ·
            refine ⟨1390003407164860086395101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853337876219813448526801 1390003407164860086395101)
            ·
              refine ⟨521251277686822532398163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1390003407164860086395101 521251277686822532398163)
              ·
                refine ⟨781876916530233798597245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521251277686822532398163 781876916530233798597245)
                ·
                  refine ⟨293203843698837674473967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781876916530233798597245 293203843698837674473967)
                  ·
                    rfl

theorem cell20_642389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_642389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642389 prefixEnd_642389 := by exact prefixLift 642389
  have htrace : WordTrace (prefixWord ++ tailWord_642389) baseStart_642389 baseEnd_642389 := by
    simpa [prefixWord, tailWord_642389, baseEnd_642389] using wordTrace_append hprefix tailTrace_642389
  have hstable : (prefixWord ++ tailWord_642389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642389).length < 2 ^ (prefixWord ++ tailWord_642389).sum := by decide
  have hdescent : baseEnd_642389 < baseStart_642389 := by decide
  rcases family_descends (prefixWord ++ tailWord_642389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642393 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_642393 : Nat := 118140960795 + 642393 * 2 ^ 59
def prefixEnd_642393 : Nat := 4983230072969 + 3 ^ 40 * 642393 * 2
def baseEnd_642393 : Nat := 293205669407831438340617

theorem tailTrace_642393 : CollatzResearch.WordTrace tailWord_642393 prefixEnd_642393 293205669407831438340617 := by
  unfold tailWord_642393
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429997561727347834891833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15619998374484898556594555 23429997561727347834891833)
  ·
    refine ⟨17572498171295510876168875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23429997561727347834891833 17572498171295510876168875)
    ·
      refine ⟨26358747256943266314253313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17572498171295510876168875 26358747256943266314253313)
      ·
        refine ⟨19769060442707449735689985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26358747256943266314253313 19769060442707449735689985)
        ·
          refine ⟨14826795332030587301767489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19769060442707449735689985 14826795332030587301767489)
          ·
            refine ⟨11120096499022940476325617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14826795332030587301767489 11120096499022940476325617)
            ·
              refine ⟨8340072374267205357244213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11120096499022940476325617 8340072374267205357244213)
              ·
                refine ⟨781881785087550502241645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8340072374267205357244213 781881785087550502241645)
                ·
                  refine ⟨293205669407831438340617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781881785087550502241645 293205669407831438340617)
                  ·
                    rfl

theorem cell20_642393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_642393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642393 prefixEnd_642393 := by exact prefixLift 642393
  have htrace : WordTrace (prefixWord ++ tailWord_642393) baseStart_642393 baseEnd_642393 := by
    simpa [prefixWord, tailWord_642393, baseEnd_642393] using wordTrace_append hprefix tailTrace_642393
  have hstable : (prefixWord ++ tailWord_642393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642393).length < 2 ^ (prefixWord ++ tailWord_642393).sum := by decide
  have hdescent : baseEnd_642393 < baseStart_642393 := by decide
  rcases family_descends (prefixWord ++ tailWord_642393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642403 : List Nat := [1, 1, 1, 5, 2, 4, 2, 4]
def baseStart_642403 : Nat := 118140960795 + 642403 * 2 ^ 59
def prefixEnd_642403 : Nat := 4983230072969 + 3 ^ 40 * 642403 * 2
def baseEnd_642403 : Nat := 97736744560105282669081

theorem tailTrace_642403 : CollatzResearch.WordTrace tailWord_642403 prefixEnd_642403 97736744560105282669081 := by
  unfold tailWord_642403
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430362291691119542755863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15620241527794079695170575 23430362291691119542755863)
  ·
    refine ⟨35145543437536679314133795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23430362291691119542755863 35145543437536679314133795)
    ·
      refine ⟨52718315156305018971200693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35145543437536679314133795 52718315156305018971200693)
      ·
        refine ⟨4942342045903595528550065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52718315156305018971200693 4942342045903595528550065)
        ·
          refine ⟨3706756534427696646412549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4942342045903595528550065 3706756534427696646412549)
          ·
            refine ⟨695016850205193121202353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3706756534427696646412549 695016850205193121202353)
            ·
              refine ⟨521262637653894840901765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695016850205193121202353 521262637653894840901765)
              ·
                refine ⟨97736744560105282669081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521262637653894840901765 97736744560105282669081)
                ·
                  rfl

theorem cell20_642403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_642403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642403 prefixEnd_642403 := by exact prefixLift 642403
  have htrace : WordTrace (prefixWord ++ tailWord_642403) baseStart_642403 baseEnd_642403 := by
    simpa [prefixWord, tailWord_642403, baseEnd_642403] using wordTrace_append hprefix tailTrace_642403
  have hstable : (prefixWord ++ tailWord_642403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642403).length < 2 ^ (prefixWord ++ tailWord_642403).sum := by decide
  have hdescent : baseEnd_642403 < baseStart_642403 := by decide
  rcases family_descends (prefixWord ++ tailWord_642403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642413 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 2]
def baseStart_642413 : Nat := 118140960795 + 642413 * 2 ^ 59
def prefixEnd_642413 : Nat := 4983230072969 + 3 ^ 40 * 642413 * 2
def baseEnd_642413 : Nat := 293214797952800257673869

theorem tailTrace_642413 : CollatzResearch.WordTrace tailWord_642413 prefixEnd_642413 293214797952800257673869 := by
  unfold tailWord_642413
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430727021654891250619893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15620484681103260833746595 23430727021654891250619893)
  ·
    refine ⟨2196630658280146054745615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23430727021654891250619893 2196630658280146054745615)
    ·
      refine ⟨3294945987420219082118423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196630658280146054745615 3294945987420219082118423)
      ·
        refine ⟨4942418981130328623177635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294945987420219082118423 4942418981130328623177635)
        ·
          refine ⟨7413628471695492934766453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942418981130328623177635 7413628471695492934766453)
          ·
            refine ⟨695027669221452462634355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7413628471695492934766453 695027669221452462634355)
            ·
              refine ⟨1042541503832178693951533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695027669221452462634355 1042541503832178693951533)
              ·
                refine ⟨390953063937067010231825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042541503832178693951533 390953063937067010231825)
                ·
                  refine ⟨293214797952800257673869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390953063937067010231825 293214797952800257673869)
                  ·
                    rfl

theorem cell20_642413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_642413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642413 prefixEnd_642413 := by exact prefixLift 642413
  have htrace : WordTrace (prefixWord ++ tailWord_642413) baseStart_642413 baseEnd_642413 := by
    simpa [prefixWord, tailWord_642413, baseEnd_642413] using wordTrace_append hprefix tailTrace_642413
  have hstable : (prefixWord ++ tailWord_642413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642413).length < 2 ^ (prefixWord ++ tailWord_642413).sum := by decide
  have hdescent : baseEnd_642413 < baseStart_642413 := by decide
  rcases family_descends (prefixWord ++ tailWord_642413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642430 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_642430 : Nat := 118140960795 + 642430 * 2 ^ 59
def prefixEnd_642430 : Nat := 4983230072969 + 3 ^ 40 * 642430 * 2
def baseEnd_642430 : Nat := 293222557216023754107133

theorem tailTrace_642430 : CollatzResearch.WordTrace tailWord_642430 prefixEnd_642430 293222557216023754107133 := by
  unfold tailWord_642430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928918382824162894248593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15620898041728868769325829 2928918382824162894248593)
  ·
    refine ⟨2196688787118122170686445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2928918382824162894248593 2196688787118122170686445)
    ·
      refine ⟨823758295169295814007417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2196688787118122170686445 823758295169295814007417)
      ·
        refine ⟨617818721376971860505563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823758295169295814007417 617818721376971860505563)
        ·
          refine ⟨926728082065457790758345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617818721376971860505563 926728082065457790758345)
          ·
            refine ⟨695046061549093343068759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926728082065457790758345 695046061549093343068759)
            ·
              refine ⟨1042569092323640014603139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695046061549093343068759 1042569092323640014603139)
              ·
                refine ⟨1563853638485460021904709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042569092323640014603139 1563853638485460021904709)
                ·
                  refine ⟨293222557216023754107133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563853638485460021904709 293222557216023754107133)
                  ·
                    rfl

theorem cell20_642430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_642430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642430 prefixEnd_642430 := by exact prefixLift 642430
  have htrace : WordTrace (prefixWord ++ tailWord_642430) baseStart_642430 baseEnd_642430 := by
    simpa [prefixWord, tailWord_642430, baseEnd_642430] using wordTrace_append hprefix tailTrace_642430
  have hstable : (prefixWord ++ tailWord_642430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642430).length < 2 ^ (prefixWord ++ tailWord_642430).sum := by decide
  have hdescent : baseEnd_642430 < baseStart_642430 := by decide
  rcases family_descends (prefixWord ++ tailWord_642430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642507 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_642507 : Nat := 118140960795 + 642507 * 2 ^ 59
def prefixEnd_642507 : Nat := 4983230072969 + 3 ^ 40 * 642507 * 2
def baseEnd_642507 : Nat := 293257702114153708540151

theorem tailTrace_642507 : CollatzResearch.WordTrace tailWord_642507 prefixEnd_642507 293257702114153708540151 := by
  unfold tailWord_642507
  simp only [CollatzResearch.WordTrace]
  refine ⟨23434155483314345304541775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15622770322209563536361183 23434155483314345304541775)
  ·
    refine ⟨35151233224971517956812663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23434155483314345304541775 35151233224971517956812663)
    ·
      refine ⟨52726849837457276935218995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35151233224971517956812663 52726849837457276935218995)
      ·
        refine ⟨79090274756185915402828493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52726849837457276935218995 79090274756185915402828493)
        ·
          refine ⟨29658853033569718276060685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79090274756185915402828493 29658853033569718276060685)
          ·
            refine ⟨11122069887588644353522757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29658853033569718276060685 11122069887588644353522757)
            ·
              refine ⟨2085388103922870816285517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11122069887588644353522757 2085388103922870816285517)
              ·
                refine ⟨782020538971076556107069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085388103922870816285517 782020538971076556107069)
                ·
                  refine ⟨293257702114153708540151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782020538971076556107069 293257702114153708540151)
                  ·
                    rfl

theorem cell20_642507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_642507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642507 prefixEnd_642507 := by exact prefixLift 642507
  have htrace : WordTrace (prefixWord ++ tailWord_642507) baseStart_642507 baseEnd_642507 := by
    simpa [prefixWord, tailWord_642507, baseEnd_642507] using wordTrace_append hprefix tailTrace_642507
  have hstable : (prefixWord ++ tailWord_642507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642507).length < 2 ^ (prefixWord ++ tailWord_642507).sum := by decide
  have hdescent : baseEnd_642507 < baseStart_642507 := by decide
  rcases family_descends (prefixWord ++ tailWord_642507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642538 : List Nat := [3, 1, 3, 1, 4, 1, 7]
def baseStart_642538 : Nat := 118140960795 + 642538 * 2 ^ 59
def prefixEnd_642538 : Nat := 4983230072969 + 3 ^ 40 * 642538 * 2
def baseEnd_642538 : Nat := 32585761262095042056299

theorem tailTrace_642538 : CollatzResearch.WordTrace tailWord_642538 prefixEnd_642538 32585761262095042056299 := by
  unfold tailWord_642538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858821536550509399730067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15623524097468025065946845 5858821536550509399730067)
  ·
    refine ⟨8788232304825764099595101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5858821536550509399730067 8788232304825764099595101)
    ·
      refine ⟨3295587114309661537348163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8788232304825764099595101 3295587114309661537348163)
      ·
        refine ⟨4943380671464492306022245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295587114309661537348163 4943380671464492306022245)
        ·
          refine ⟨926883875899592307379171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4943380671464492306022245 926883875899592307379171)
          ·
            refine ⟨1390325813849388461068757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926883875899592307379171 1390325813849388461068757)
            ·
              refine ⟨32585761262095042056299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1390325813849388461068757 32585761262095042056299)
              ·
                rfl

theorem cell20_642538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 7].length) (baseStart_642538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642538 prefixEnd_642538 := by exact prefixLift 642538
  have htrace : WordTrace (prefixWord ++ tailWord_642538) baseStart_642538 baseEnd_642538 := by
    simpa [prefixWord, tailWord_642538, baseEnd_642538] using wordTrace_append hprefix tailTrace_642538
  have hstable : (prefixWord ++ tailWord_642538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642538).length < 2 ^ (prefixWord ++ tailWord_642538).sum := by decide
  have hdescent : baseEnd_642538 < baseStart_642538 := by decide
  rcases family_descends (prefixWord ++ tailWord_642538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642545 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_642545 : Nat := 118140960795 + 642545 * 2 ^ 59
def prefixEnd_642545 : Nat := 4983230072969 + 3 ^ 40 * 642545 * 2
def baseEnd_642545 : Nat := 293275046349594465273329

theorem tailTrace_642545 : CollatzResearch.WordTrace tailWord_642545 prefixEnd_642545 293275046349594465273329 := by
  unfold tailWord_642545
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435541457176677794425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15623694304784451862950059 23435541457176677794425089)
  ·
    refine ⟨17576656092882508345818817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23435541457176677794425089 17576656092882508345818817)
    ·
      refine ⟨13182492069661881259364113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17576656092882508345818817 13182492069661881259364113)
      ·
        refine ⟨9886869052246410944523085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13182492069661881259364113 9886869052246410944523085)
        ·
          refine ⟨3707575894592404104196157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9886869052246410944523085 3707575894592404104196157)
          ·
            refine ⟨1390340960472151539073559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3707575894592404104196157 1390340960472151539073559)
            ·
              refine ⟨2085511440708227308610339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390340960472151539073559 2085511440708227308610339)
              ·
                refine ⟨3128267161062340962915509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085511440708227308610339 3128267161062340962915509)
                ·
                  refine ⟨293275046349594465273329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128267161062340962915509 293275046349594465273329)
                  ·
                    rfl

theorem cell20_642545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_642545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642545 prefixEnd_642545 := by exact prefixLift 642545
  have htrace : WordTrace (prefixWord ++ tailWord_642545) baseStart_642545 baseEnd_642545 := by
    simpa [prefixWord, tailWord_642545, baseEnd_642545] using wordTrace_append hprefix tailTrace_642545
  have hstable : (prefixWord ++ tailWord_642545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642545).length < 2 ^ (prefixWord ++ tailWord_642545).sum := by decide
  have hdescent : baseEnd_642545 < baseStart_642545 := by decide
  rcases family_descends (prefixWord ++ tailWord_642545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642552 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_642552 : Nat := 118140960795 + 642552 * 2 ^ 59
def prefixEnd_642552 : Nat := 4983230072969 + 3 ^ 40 * 642552 * 2
def baseEnd_642552 : Nat := 293278241340333552039967

theorem tailTrace_642552 : CollatzResearch.WordTrace tailWord_642552 prefixEnd_642552 293278241340333552039967 := by
  unfold tailWord_642552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11717898384075658994964955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15623864512100878659953273 11717898384075658994964955)
  ·
    refine ⟨17576847576113488492447433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11717898384075658994964955 17576847576113488492447433)
    ·
      refine ⟨13182635682085116369335575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17576847576113488492447433 13182635682085116369335575)
      ·
        refine ⟨19773953523127674554003363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13182635682085116369335575 19773953523127674554003363)
        ·
          refine ⟨29660930284691511831005045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19773953523127674554003363 29660930284691511831005045)
          ·
            refine ⟨2780712214189829234156723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29660930284691511831005045 2780712214189829234156723)
            ·
              refine ⟨4171068321284743851235085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780712214189829234156723 4171068321284743851235085)
              ·
                refine ⟨1564150620481778944213157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4171068321284743851235085 1564150620481778944213157)
                ·
                  refine ⟨293278241340333552039967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564150620481778944213157 293278241340333552039967)
                  ·
                    rfl

theorem cell20_642552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_642552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642552 prefixEnd_642552 := by exact prefixLift 642552
  have htrace : WordTrace (prefixWord ++ tailWord_642552) baseStart_642552 baseEnd_642552 := by
    simpa [prefixWord, tailWord_642552, baseEnd_642552] using wordTrace_append hprefix tailTrace_642552
  have hstable : (prefixWord ++ tailWord_642552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642552).length < 2 ^ (prefixWord ++ tailWord_642552).sum := by decide
  have hdescent : baseEnd_642552 < baseStart_642552 := by decide
  rcases family_descends (prefixWord ++ tailWord_642552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642572 : List Nat := [2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_642572 : Nat := 118140960795 + 642572 * 2 ^ 59
def prefixEnd_642572 : Nat := 4983230072969 + 3 ^ 40 * 642572 * 2
def baseEnd_642572 : Nat := 97762456628434123791073

theorem tailTrace_642572 : CollatzResearch.WordTrace tailWord_642572 prefixEnd_642572 97762456628434123791073 := by
  unfold tailWord_642572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718263114039430702828985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15624350818719240937105313 11718263114039430702828985)
  ·
    refine ⟨8788697335529573027121739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11718263114039430702828985 8788697335529573027121739)
    ·
      refine ⟨13183046003294359540682609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8788697335529573027121739 13183046003294359540682609)
      ·
        refine ⟨9887284502470769655511957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13183046003294359540682609 9887284502470769655511957)
        ·
          refine ⟨463466461053317327602123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9887284502470769655511957 463466461053317327602123)
          ·
            refine ⟨695199691579975991403185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463466461053317327602123 695199691579975991403185)
            ·
              refine ⟨521399768684981993552389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695199691579975991403185 521399768684981993552389)
              ·
                refine ⟨97762456628434123791073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521399768684981993552389 97762456628434123791073)
                ·
                  rfl

theorem cell20_642572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_642572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642572 prefixEnd_642572 := by exact prefixLift 642572
  have htrace : WordTrace (prefixWord ++ tailWord_642572) baseStart_642572 baseEnd_642572 := by
    simpa [prefixWord, tailWord_642572, baseEnd_642572] using wordTrace_append hprefix tailTrace_642572
  have hstable : (prefixWord ++ tailWord_642572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642572).length < 2 ^ (prefixWord ++ tailWord_642572).sum := by decide
  have hdescent : baseEnd_642572 < baseStart_642572 := by decide
  rcases family_descends (prefixWord ++ tailWord_642572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642617 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_642617 : Nat := 118140960795 + 642617 * 2 ^ 59
def prefixEnd_642617 : Nat := 4983230072969 + 3 ^ 40 * 642617 * 2
def baseEnd_642617 : Nat := 293307909111482214873035

theorem tailTrace_642617 : CollatzResearch.WordTrace tailWord_642617 prefixEnd_642617 293307909111482214873035 := by
  unfold tailWord_642617
  simp only [CollatzResearch.WordTrace]
  refine ⟨23438167512915834091046105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15625445008610556060697403 23438167512915834091046105)
  ·
    refine ⟨17578625634686875568284579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23438167512915834091046105 17578625634686875568284579)
    ·
      refine ⟨26367938452030313352426869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17578625634686875568284579 26367938452030313352426869)
      ·
        refine ⟨2471994229877841876790019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26367938452030313352426869 2471994229877841876790019)
        ·
          refine ⟨3707991344816762815185029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471994229877841876790019 3707991344816762815185029)
          ·
            refine ⟨695248377153143027847193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3707991344816762815185029 695248377153143027847193)
            ·
              refine ⟨521436282864857270885395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695248377153143027847193 521436282864857270885395)
              ·
                refine ⟨782154424297285906328093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521436282864857270885395 782154424297285906328093)
                ·
                  refine ⟨293307909111482214873035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782154424297285906328093 293307909111482214873035)
                  ·
                    rfl

theorem cell20_642617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_642617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642617 prefixEnd_642617 := by exact prefixLift 642617
  have htrace : WordTrace (prefixWord ++ tailWord_642617) baseStart_642617 baseEnd_642617 := by
    simpa [prefixWord, tailWord_642617, baseEnd_642617] using wordTrace_append hprefix tailTrace_642617
  have hstable : (prefixWord ++ tailWord_642617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642617).length < 2 ^ (prefixWord ++ tailWord_642617).sum := by decide
  have hdescent : baseEnd_642617 < baseStart_642617 := by decide
  rcases family_descends (prefixWord ++ tailWord_642617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642645 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 2]
def baseStart_642645 : Nat := 118140960795 + 642645 * 2 ^ 59
def prefixEnd_642645 : Nat := 4983230072969 + 3 ^ 40 * 642645 * 2
def baseEnd_642645 : Nat := 293320689074438561939587

theorem tailTrace_642645 : CollatzResearch.WordTrace tailWord_642645 prefixEnd_642645 293320689074438561939587 := by
  unfold tailWord_642645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23439188756814394873065389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15626125837876263248710259 23439188756814394873065389)
  ·
    refine ⟨8789695783805398077399521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23439188756814394873065389 8789695783805398077399521)
    ·
      refine ⟨6592271837854048558049641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8789695783805398077399521 6592271837854048558049641)
      ·
        refine ⟨4944203878390536418537231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6592271837854048558049641 4944203878390536418537231)
        ·
          refine ⟨7416305817585804627805847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944203878390536418537231 7416305817585804627805847)
          ·
            refine ⟨11124458726378706941708771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416305817585804627805847 11124458726378706941708771)
            ·
              refine ⟨16686688089568060412563157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11124458726378706941708771 16686688089568060412563157)
              ·
                refine ⟨391094252099251415919449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16686688089568060412563157 391094252099251415919449)
                ·
                  refine ⟨293320689074438561939587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391094252099251415919449 293320689074438561939587)
                  ·
                    rfl

theorem cell20_642645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_642645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642645 prefixEnd_642645 := by exact prefixLift 642645
  have htrace : WordTrace (prefixWord ++ tailWord_642645) baseStart_642645 baseEnd_642645 := by
    simpa [prefixWord, tailWord_642645, baseEnd_642645] using wordTrace_append hprefix tailTrace_642645
  have hstable : (prefixWord ++ tailWord_642645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642645).length < 2 ^ (prefixWord ++ tailWord_642645).sum := by decide
  have hdescent : baseEnd_642645 < baseStart_642645 := by decide
  rcases family_descends (prefixWord ++ tailWord_642645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642659 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_642659 : Nat := 118140960795 + 642659 * 2 ^ 59
def prefixEnd_642659 : Nat := 4983230072969 + 3 ^ 40 * 642659 * 2
def baseEnd_642659 : Nat := 293327079055916735472863

theorem tailTrace_642659 : CollatzResearch.WordTrace tailWord_642659 prefixEnd_642659 293327079055916735472863 := by
  unfold tailWord_642659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23439699378763675264075031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15626466252509116842716687 23439699378763675264075031)
  ·
    refine ⟨35159549068145512896112547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23439699378763675264075031 35159549068145512896112547)
    ·
      refine ⟨52739323602218269344168821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35159549068145512896112547 52739323602218269344168821)
      ·
        refine ⟨4944311587707962751015827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52739323602218269344168821 4944311587707962751015827)
        ·
          refine ⟨7416467381561944126523741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944311587707962751015827 7416467381561944126523741)
          ·
            refine ⟨2781175268085729047446403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7416467381561944126523741 2781175268085729047446403)
            ·
              refine ⟨4171762902128593571169605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781175268085729047446403 4171762902128593571169605)
              ·
                refine ⟨782205544149111294594301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4171762902128593571169605 782205544149111294594301)
                ·
                  refine ⟨293327079055916735472863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782205544149111294594301 293327079055916735472863)
                  ·
                    rfl

theorem cell20_642659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_642659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642659 prefixEnd_642659 := by exact prefixLift 642659
  have htrace : WordTrace (prefixWord ++ tailWord_642659) baseStart_642659 baseEnd_642659 := by
    simpa [prefixWord, tailWord_642659, baseEnd_642659] using wordTrace_append hprefix tailTrace_642659
  have hstable : (prefixWord ++ tailWord_642659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642659).length < 2 ^ (prefixWord ++ tailWord_642659).sum := by decide
  have hdescent : baseEnd_642659 < baseStart_642659 := by decide
  rcases family_descends (prefixWord ++ tailWord_642659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642669 : List Nat := [1, 5, 1, 1, 4, 2, 1, 5]
def baseStart_642669 : Nat := 118140960795 + 642669 * 2 ^ 59
def prefixEnd_642669 : Nat := 4983230072969 + 3 ^ 40 * 642669 * 2
def baseEnd_642669 : Nat := 97777214442800381713163

theorem tailTrace_642669 : CollatzResearch.WordTrace tailWord_642669 prefixEnd_642669 97777214442800381713163 := by
  unfold tailWord_642669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440064108727446971939061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15626709405818297981292707 23440064108727446971939061)
  ·
    refine ⟨2197506010193198153619287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23440064108727446971939061 2197506010193198153619287)
    ·
      refine ⟨3296259015289797230428931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197506010193198153619287 3296259015289797230428931)
      ·
        refine ⟨4944388522934695845643397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296259015289797230428931 4944388522934695845643397)
        ·
          refine ⟨927072848050255471058137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4944388522934695845643397 927072848050255471058137)
          ·
            refine ⟨695304636037691603293603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927072848050255471058137 695304636037691603293603)
            ·
              refine ⟨1042956954056537404940405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695304636037691603293603 1042956954056537404940405)
              ·
                refine ⟨97777214442800381713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042956954056537404940405 97777214442800381713163)
                ·
                  rfl

theorem cell20_642669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_642669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642669 prefixEnd_642669 := by exact prefixLift 642669
  have htrace : WordTrace (prefixWord ++ tailWord_642669) baseStart_642669 baseEnd_642669 := by
    simpa [prefixWord, tailWord_642669, baseEnd_642669] using wordTrace_append hprefix tailTrace_642669
  have hstable : (prefixWord ++ tailWord_642669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642669).length < 2 ^ (prefixWord ++ tailWord_642669).sum := by decide
  have hdescent : baseEnd_642669 < baseStart_642669 := by decide
  rcases family_descends (prefixWord ++ tailWord_642669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642711 : List Nat := [1, 1, 3, 3, 2, 3, 7]
def baseStart_642711 : Nat := 118140960795 + 642711 * 2 ^ 59
def prefixEnd_642711 : Nat := 4983230072969 + 3 ^ 40 * 642711 * 2
def baseEnd_642711 : Nat := 32594534808092851748813

theorem tailTrace_642711 : CollatzResearch.WordTrace tailWord_642711 prefixEnd_642711 32594534808092851748813 := by
  unfold tailWord_642711
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441595974575288144967987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15627730649716858763311991 23441595974575288144967987)
  ·
    refine ⟨35162393961862932217451981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23441595974575288144967987 35162393961862932217451981)
    ·
      refine ⟨13185897735698599581544493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35162393961862932217451981 13185897735698599581544493)
      ·
        refine ⟨4944711650886974843079185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13185897735698599581544493 4944711650886974843079185)
        ·
          refine ⟨3708533738165231132309389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4944711650886974843079185 3708533738165231132309389)
          ·
            refine ⟨1390700151811961674616021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3708533738165231132309389 1390700151811961674616021)
            ·
              refine ⟨32594534808092851748813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1390700151811961674616021 32594534808092851748813)
              ·
                rfl

theorem cell20_642711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_642711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642711 prefixEnd_642711 := by exact prefixLift 642711
  have htrace : WordTrace (prefixWord ++ tailWord_642711) baseStart_642711 baseEnd_642711 := by
    simpa [prefixWord, tailWord_642711, baseEnd_642711] using wordTrace_append hprefix tailTrace_642711
  have hstable : (prefixWord ++ tailWord_642711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642711).length < 2 ^ (prefixWord ++ tailWord_642711).sum := by decide
  have hdescent : baseEnd_642711 < baseStart_642711 := by decide
  rcases family_descends (prefixWord ++ tailWord_642711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642721 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_642721 : Nat := 118140960795 + 642721 * 2 ^ 59
def prefixEnd_642721 : Nat := 4983230072969 + 3 ^ 40 * 642721 * 2
def baseEnd_642721 : Nat := 293355377545320075405943

theorem tailTrace_642721 : CollatzResearch.WordTrace tailWord_642721 prefixEnd_642721 293355377545320075405943 := by
  unfold tailWord_642721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441960704539059852832017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15627973803026039901888011 23441960704539059852832017)
  ·
    refine ⟨17581470528404294889624013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23441960704539059852832017 17581470528404294889624013)
    ·
      refine ⟨6593051448151610583609005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17581470528404294889624013 6593051448151610583609005)
      ·
        refine ⟨2472394293056853968853377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6593051448151610583609005 2472394293056853968853377)
        ·
          refine ⟨1854295719792640476640033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472394293056853968853377 1854295719792640476640033)
          ·
            refine ⟨1390721789844480357480025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1854295719792640476640033 1390721789844480357480025)
            ·
              refine ⟨1043041342383360268110019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390721789844480357480025 1043041342383360268110019)
              ·
                refine ⟨1564562013575040402165029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043041342383360268110019 1564562013575040402165029)
                ·
                  refine ⟨293355377545320075405943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564562013575040402165029 293355377545320075405943)
                  ·
                    rfl

theorem cell20_642721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_642721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642721 prefixEnd_642721 := by exact prefixLift 642721
  have htrace : WordTrace (prefixWord ++ tailWord_642721) baseStart_642721 baseEnd_642721 := by
    simpa [prefixWord, tailWord_642721, baseEnd_642721] using wordTrace_append hprefix tailTrace_642721
  have hstable : (prefixWord ++ tailWord_642721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642721).length < 2 ^ (prefixWord ++ tailWord_642721).sum := by decide
  have hdescent : baseEnd_642721 < baseStart_642721 := by decide
  rcases family_descends (prefixWord ++ tailWord_642721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642749 : List Nat := [1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_642749 : Nat := 118140960795 + 642749 * 2 ^ 59
def prefixEnd_642749 : Nat := 4983230072969 + 3 ^ 40 * 642749 * 2
def baseEnd_642749 : Nat := 97789385836092140824165

theorem tailTrace_642749 : CollatzResearch.WordTrace tailWord_642749 prefixEnd_642749 97789385836092140824165 := by
  unfold tailWord_642749
  simp only [CollatzResearch.WordTrace]
  refine ⟨23442981948437620634851301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15628654632291747089900867 23442981948437620634851301)
  ·
    refine ⟨4395559115332053869034619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23442981948437620634851301 4395559115332053869034619)
    ·
      refine ⟨6593338672998080803551929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395559115332053869034619 6593338672998080803551929)
      ·
        refine ⟨4945004004748560602663947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6593338672998080803551929 4945004004748560602663947)
        ·
          refine ⟨7417506007122840903995921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945004004748560602663947 7417506007122840903995921)
          ·
            refine ⟨5563129505342130677996941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7417506007122840903995921 5563129505342130677996941)
            ·
              refine ⟨2086173564503299004248853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5563129505342130677996941 2086173564503299004248853)
              ·
                refine ⟨97789385836092140824165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2086173564503299004248853 97789385836092140824165)
                ·
                  rfl

theorem cell20_642749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_642749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642749 prefixEnd_642749 := by exact prefixLift 642749
  have htrace : WordTrace (prefixWord ++ tailWord_642749) baseStart_642749 baseEnd_642749 := by
    simpa [prefixWord, tailWord_642749, baseEnd_642749] using wordTrace_append hprefix tailTrace_642749
  have hstable : (prefixWord ++ tailWord_642749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642749).length < 2 ^ (prefixWord ++ tailWord_642749).sum := by decide
  have hdescent : baseEnd_642749 < baseStart_642749 := by decide
  rcases family_descends (prefixWord ++ tailWord_642749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642763 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_642763 : Nat := 118140960795 + 642763 * 2 ^ 59
def prefixEnd_642763 : Nat := 4983230072969 + 3 ^ 40 * 642763 * 2
def baseEnd_642763 : Nat := 293374547489754596005771

theorem tailTrace_642763 : CollatzResearch.WordTrace tailWord_642763 prefixEnd_642763 293374547489754596005771 := by
  unfold tailWord_642763
  simp only [CollatzResearch.WordTrace]
  refine ⟨23443492570386901025860943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15628995046924600683907295 23443492570386901025860943)
  ·
    refine ⟨35165238855580351538791415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23443492570386901025860943 35165238855580351538791415)
    ·
      refine ⟨52747858283370527308187123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35165238855580351538791415 52747858283370527308187123)
      ·
        refine ⟨79121787425055790962280685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52747858283370527308187123 79121787425055790962280685)
        ·
          refine ⟨29670670284395921610855257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79121787425055790962280685 29670670284395921610855257)
          ·
            refine ⟨22253002713296941208141443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29670670284395921610855257 22253002713296941208141443)
            ·
              refine ⟨33379504069945411812212165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22253002713296941208141443 33379504069945411812212165)
              ·
                refine ⟨6258657013114764714789781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33379504069945411812212165 6258657013114764714789781)
                ·
                  refine ⟨293374547489754596005771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6258657013114764714789781 293374547489754596005771)
                  ·
                    rfl

theorem cell20_642763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_642763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642763 prefixEnd_642763 := by exact prefixLift 642763
  have htrace : WordTrace (prefixWord ++ tailWord_642763) baseStart_642763 baseEnd_642763 := by
    simpa [prefixWord, tailWord_642763, baseEnd_642763] using wordTrace_append hprefix tailTrace_642763
  have hstable : (prefixWord ++ tailWord_642763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642763).length < 2 ^ (prefixWord ++ tailWord_642763).sum := by decide
  have hdescent : baseEnd_642763 < baseStart_642763 := by decide
  rcases family_descends (prefixWord ++ tailWord_642763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642776 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_642776 : Nat := 118140960795 + 642776 * 2 ^ 59
def prefixEnd_642776 : Nat := 4983230072969 + 3 ^ 40 * 642776 * 2
def baseEnd_642776 : Nat := 293380481043984328572385

theorem tailTrace_642776 : CollatzResearch.WordTrace tailWord_642776 prefixEnd_642776 293380481043984328572385 := by
  unfold tailWord_642776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721983359669902123042091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15629311146226536164056121 11721983359669902123042091)
  ·
    refine ⟨17582975039504853184563137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11721983359669902123042091 17582975039504853184563137)
    ·
      refine ⟨13187231279628639888422353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17582975039504853184563137 13187231279628639888422353)
      ·
        refine ⟨9890423459721479916316765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187231279628639888422353 9890423459721479916316765)
        ·
          refine ⟨3708908797395554968618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9890423459721479916316765 3708908797395554968618787)
          ·
            refine ⟨5563363196093332452928181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708908797395554968618787 5563363196093332452928181)
            ·
              refine ⟨521565299633749917462017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5563363196093332452928181 521565299633749917462017)
              ·
                refine ⟨391173974725312438096513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521565299633749917462017 391173974725312438096513)
                ·
                  refine ⟨293380481043984328572385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391173974725312438096513 293380481043984328572385)
                  ·
                    rfl

theorem cell20_642776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_642776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642776 prefixEnd_642776 := by exact prefixLift 642776
  have htrace : WordTrace (prefixWord ++ tailWord_642776) baseStart_642776 baseEnd_642776 := by
    simpa [prefixWord, tailWord_642776, baseEnd_642776] using wordTrace_append hprefix tailTrace_642776
  have hstable : (prefixWord ++ tailWord_642776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642776).length < 2 ^ (prefixWord ++ tailWord_642776).sum := by decide
  have hdescent : baseEnd_642776 < baseStart_642776 := by decide
  rcases family_descends (prefixWord ++ tailWord_642776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642842 : List Nat := [3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_642842 : Nat := 118140960795 + 642842 * 2 ^ 59
def prefixEnd_642842 : Nat := 4983230072969 + 3 ^ 40 * 642842 * 2
def baseEnd_642842 : Nat := 97803535080793810790705

theorem tailTrace_642842 : CollatzResearch.WordTrace tailWord_642842 prefixEnd_642842 97803535080793810790705 := by
  unfold tailWord_642842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861593484275174379496695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15630915958067131678657853 5861593484275174379496695)
  ·
    refine ⟨8792390226412761569245043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861593484275174379496695 8792390226412761569245043)
    ·
      refine ⟨13188585339619142353867565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8792390226412761569245043 13188585339619142353867565)
      ·
        refine ⟨4945719502357178382700337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13188585339619142353867565 4945719502357178382700337)
        ·
          refine ⟨3709289626767883787025253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4945719502357178382700337 3709289626767883787025253)
          ·
            refine ⟨695491805018978210067235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3709289626767883787025253 695491805018978210067235)
            ·
              refine ⟨1043237707528467315100853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695491805018978210067235 1043237707528467315100853)
              ·
                refine ⟨97803535080793810790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1043237707528467315100853 97803535080793810790705)
                ·
                  rfl

theorem cell20_642842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_642842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642842 prefixEnd_642842 := by exact prefixLift 642842
  have htrace : WordTrace (prefixWord ++ tailWord_642842) baseStart_642842 baseEnd_642842 := by
    simpa [prefixWord, tailWord_642842, baseEnd_642842] using wordTrace_append hprefix tailTrace_642842
  have hstable : (prefixWord ++ tailWord_642842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642842).length < 2 ^ (prefixWord ++ tailWord_642842).sum := by decide
  have hdescent : baseEnd_642842 < baseStart_642842 := by decide
  rcases family_descends (prefixWord ++ tailWord_642842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642849 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_642849 : Nat := 118140960795 + 642849 * 2 ^ 59
def prefixEnd_642849 : Nat := 4983230072969 + 3 ^ 40 * 642849 * 2
def baseEnd_642849 : Nat := 293413800233120519138753

theorem tailTrace_642849 : CollatzResearch.WordTrace tailWord_642849 prefixEnd_642849 293413800233120519138753 := by
  unfold tailWord_642849
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446629248075337713491601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15631086165383558475661067 23446629248075337713491601)
  ·
    refine ⟨17584971936056503285118701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23446629248075337713491601 17584971936056503285118701)
    ·
      refine ⟨6594364476021188731919513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17584971936056503285118701 6594364476021188731919513)
      ·
        refine ⟨4945773357015891548939635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594364476021188731919513 4945773357015891548939635)
        ·
          refine ⟨7418660035523837323409453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945773357015891548939635 7418660035523837323409453)
          ·
            refine ⟨2781997513321438996278545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7418660035523837323409453 2781997513321438996278545)
            ·
              refine ⟨2086498134991079247208909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781997513321438996278545 2086498134991079247208909)
              ·
                refine ⟨782436800621654717703341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2086498134991079247208909 782436800621654717703341)
                ·
                  refine ⟨293413800233120519138753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782436800621654717703341 293413800233120519138753)
                  ·
                    rfl

theorem cell20_642849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_642849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642849 prefixEnd_642849 := by exact prefixLift 642849
  have htrace : WordTrace (prefixWord ++ tailWord_642849) baseStart_642849 baseEnd_642849 := by
    simpa [prefixWord, tailWord_642849, baseEnd_642849] using wordTrace_append hprefix tailTrace_642849
  have hstable : (prefixWord ++ tailWord_642849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642849).length < 2 ^ (prefixWord ++ tailWord_642849).sum := by decide
  have hdescent : baseEnd_642849 < baseStart_642849 := by decide
  rcases family_descends (prefixWord ++ tailWord_642849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642856 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_642856 : Nat := 118140960795 + 642856 * 2 ^ 59
def prefixEnd_642856 : Nat := 4983230072969 + 3 ^ 40 * 642856 * 2
def baseEnd_642856 : Nat := 293416995223859605905391

theorem tailTrace_642856 : CollatzResearch.WordTrace tailWord_642856 prefixEnd_642856 293416995223859605905391 := by
  unfold tailWord_642856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723442279524988954498211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15631256372699985272664281 11723442279524988954498211)
  ·
    refine ⟨17585163419287483431747317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11723442279524988954498211 17585163419287483431747317)
    ·
      refine ⟨1648609070558201571726311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17585163419287483431747317 1648609070558201571726311)
      ·
        refine ⟨2472913605837302357589467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648609070558201571726311 2472913605837302357589467)
        ·
          refine ⟨3709370408755953536384201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472913605837302357589467 3709370408755953536384201)
          ·
            refine ⟨2782027806566965152288151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3709370408755953536384201 2782027806566965152288151)
            ·
              refine ⟨4173041709850447728432227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782027806566965152288151 4173041709850447728432227)
              ·
                refine ⟨6259562564775671592648341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173041709850447728432227 6259562564775671592648341)
                ·
                  refine ⟨293416995223859605905391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6259562564775671592648341 293416995223859605905391)
                  ·
                    rfl

theorem cell20_642856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_642856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642856 prefixEnd_642856 := by exact prefixLift 642856
  have htrace : WordTrace (prefixWord ++ tailWord_642856) baseStart_642856 baseEnd_642856 := by
    simpa [prefixWord, tailWord_642856, baseEnd_642856] using wordTrace_append hprefix tailTrace_642856
  have hstable : (prefixWord ++ tailWord_642856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642856).length < 2 ^ (prefixWord ++ tailWord_642856).sum := by decide
  have hdescent : baseEnd_642856 < baseStart_642856 := by decide
  rcases family_descends (prefixWord ++ tailWord_642856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642887 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_642887 : Nat := 118140960795 + 642887 * 2 ^ 59
def prefixEnd_642887 : Nat := 4983230072969 + 3 ^ 40 * 642887 * 2
def baseEnd_642887 : Nat := 293431144468561275871931

theorem tailTrace_642887 : CollatzResearch.WordTrace tailWord_642887 prefixEnd_642887 293431144468561275871931 := by
  unfold tailWord_642887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23448015221937670203374915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15632010147958446802249943 23448015221937670203374915)
  ·
    refine ⟨35172022832906505305062373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23448015221937670203374915 35172022832906505305062373)
    ·
      refine ⟨6594754281169969744699195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35172022832906505305062373 6594754281169969744699195)
      ·
        refine ⟨9892131421754954617048793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594754281169969744699195 9892131421754954617048793)
        ·
          refine ⟨7419098566316215962786595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892131421754954617048793 7419098566316215962786595)
          ·
            refine ⟨11128647849474323944179893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419098566316215962786595 11128647849474323944179893)
            ·
              refine ⟨1043310735888217869766865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11128647849474323944179893 1043310735888217869766865)
              ·
                refine ⟨782483051916163402325149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043310735888217869766865 782483051916163402325149)
                ·
                  refine ⟨293431144468561275871931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782483051916163402325149 293431144468561275871931)
                  ·
                    rfl

theorem cell20_642887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_642887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642887 prefixEnd_642887 := by exact prefixLift 642887
  have htrace : WordTrace (prefixWord ++ tailWord_642887) baseStart_642887 baseEnd_642887 := by
    simpa [prefixWord, tailWord_642887, baseEnd_642887] using wordTrace_append hprefix tailTrace_642887
  have hstable : (prefixWord ++ tailWord_642887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642887).length < 2 ^ (prefixWord ++ tailWord_642887).sum := by decide
  have hdescent : baseEnd_642887 < baseStart_642887 := by decide
  rcases family_descends (prefixWord ++ tailWord_642887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642942 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_642942 : Nat := 118140960795 + 642942 * 2 ^ 59
def prefixEnd_642942 : Nat := 4983230072969 + 3 ^ 40 * 642942 * 2
def baseEnd_642942 : Nat := 293456247967225529038373

theorem tailTrace_642942 : CollatzResearch.WordTrace tailWord_642942 prefixEnd_642942 293456247967225529038373 := by
  unfold tailWord_642942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931252654592301824578385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15633347491158943064418053 2931252654592301824578385)
  ·
    refine ⟨2198439490944226368433789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2931252654592301824578385 2198439490944226368433789)
    ·
      refine ⟨824414809104084888162671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2198439490944226368433789 824414809104084888162671)
      ·
        refine ⟨1236622213656127332244007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824414809104084888162671 1236622213656127332244007)
        ·
          refine ⟨1854933320484190998366011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236622213656127332244007 1854933320484190998366011)
          ·
            refine ⟨2782399980726286497549017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854933320484190998366011 2782399980726286497549017)
            ·
              refine ⟨2086799985544714873161763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782399980726286497549017 2086799985544714873161763)
              ·
                refine ⟨3130199978317072309742645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086799985544714873161763 3130199978317072309742645)
                ·
                  refine ⟨293456247967225529038373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130199978317072309742645 293456247967225529038373)
                  ·
                    rfl

theorem cell20_642942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_642942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642942 prefixEnd_642942 := by exact prefixLift 642942
  have htrace : WordTrace (prefixWord ++ tailWord_642942) baseStart_642942 baseEnd_642942 := by
    simpa [prefixWord, tailWord_642942, baseEnd_642942] using wordTrace_append hprefix tailTrace_642942
  have hstable : (prefixWord ++ tailWord_642942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642942).length < 2 ^ (prefixWord ++ tailWord_642942).sum := by decide
  have hdescent : baseEnd_642942 < baseStart_642942 := by decide
  rcases family_descends (prefixWord ++ tailWord_642942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642945 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 4]
def baseStart_642945 : Nat := 118140960795 + 642945 * 2 ^ 59
def prefixEnd_642945 : Nat := 4983230072969 + 3 ^ 40 * 642945 * 2
def baseEnd_642945 : Nat := 293457617248970851938361

theorem tailTrace_642945 : CollatzResearch.WordTrace tailWord_642945 prefixEnd_642945 293457617248970851938361 := by
  unfold tailWord_642945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450130655727546108986289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15633420437151697405990859 23450130655727546108986289)
  ·
    refine ⟨17587597991795659581739717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23450130655727546108986289 17587597991795659581739717)
    ·
      refine ⟨3297674623461686171576197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17587597991795659581739717 3297674623461686171576197)
      ·
        refine ⟨618313991899066157170537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3297674623461686171576197 618313991899066157170537)
        ·
          refine ⟨463735493924299617877903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618313991899066157170537 463735493924299617877903)
          ·
            refine ⟨695603240886449426816855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463735493924299617877903 695603240886449426816855)
            ·
              refine ⟨1043404861329674140225283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695603240886449426816855 1043404861329674140225283)
              ·
                refine ⟨1565107291994511210337925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043404861329674140225283 1565107291994511210337925)
                ·
                  refine ⟨293457617248970851938361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565107291994511210337925 293457617248970851938361)
                  ·
                    rfl

theorem cell20_642945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_642945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642945 prefixEnd_642945 := by exact prefixLift 642945
  have htrace : WordTrace (prefixWord ++ tailWord_642945) baseStart_642945 baseEnd_642945 := by
    simpa [prefixWord, tailWord_642945, baseEnd_642945] using wordTrace_append hprefix tailTrace_642945
  have hstable : (prefixWord ++ tailWord_642945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642945).length < 2 ^ (prefixWord ++ tailWord_642945).sum := by decide
  have hdescent : baseEnd_642945 < baseStart_642945 := by decide
  rcases family_descends (prefixWord ++ tailWord_642945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642960 : List Nat := [2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_642960 : Nat := 118140960795 + 642960 * 2 ^ 59
def prefixEnd_642960 : Nat := 4983230072969 + 3 ^ 40 * 642960 * 2
def baseEnd_642960 : Nat := 97821487885899155479433

theorem tailTrace_642960 : CollatzResearch.WordTrace tailWord_642960 prefixEnd_642960 97821487885899155479433 := by
  unfold tailWord_642960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725338875336601835391167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15633785167115469113854889 11725338875336601835391167)
  ·
    refine ⟨17588008313004902753086751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11725338875336601835391167 17588008313004902753086751)
    ·
      refine ⟨26382012469507354129630127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17588008313004902753086751 26382012469507354129630127)
      ·
        refine ⟨39573018704261031194445191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26382012469507354129630127 39573018704261031194445191)
        ·
          refine ⟨59359528056391546791667787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39573018704261031194445191 59359528056391546791667787)
          ·
            refine ⟨89039292084587320187501681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59359528056391546791667787 89039292084587320187501681)
            ·
              refine ⟨66779469063440490140626261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89039292084587320187501681 66779469063440490140626261)
              ·
                refine ⟨97821487885899155479433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66779469063440490140626261 97821487885899155479433)
                ·
                  rfl

theorem cell20_642960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_642960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642960 prefixEnd_642960 := by exact prefixLift 642960
  have htrace : WordTrace (prefixWord ++ tailWord_642960) baseStart_642960 baseEnd_642960 := by
    simpa [prefixWord, tailWord_642960, baseEnd_642960] using wordTrace_append hprefix tailTrace_642960
  have hstable : (prefixWord ++ tailWord_642960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642960).length < 2 ^ (prefixWord ++ tailWord_642960).sum := by decide
  have hdescent : baseEnd_642960 < baseStart_642960 := by decide
  rcases family_descends (prefixWord ++ tailWord_642960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642990 : List Nat := [4, 1, 5, 1, 2, 7]
def baseStart_642990 : Nat := 118140960795 + 642990 * 2 ^ 59
def prefixEnd_642990 : Nat := 4983230072969 + 3 ^ 40 * 642990 * 2
def baseEnd_642990 : Nat := 10869561350931507238451

theorem tailTrace_642990 : CollatzResearch.WordTrace tailWord_642990 prefixEnd_642990 10869561350931507238451 := by
  unfold tailWord_642990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931471492570564849296803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15634514627043012529582949 2931471492570564849296803)
  ·
    refine ⟨4397207238855847273945205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931471492570564849296803 4397207238855847273945205)
    ·
      refine ⟨412238178642735681932363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4397207238855847273945205 412238178642735681932363)
      ·
        refine ⟨618357267964103522898545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412238178642735681932363 618357267964103522898545)
        ·
          refine ⟨463767950973077642173909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618357267964103522898545 463767950973077642173909)
          ·
            refine ⟨10869561350931507238451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 463767950973077642173909 10869561350931507238451)
            ·
              rfl

theorem cell20_642990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 7].length) (baseStart_642990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_642990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_642990 prefixEnd_642990 := by exact prefixLift 642990
  have htrace : WordTrace (prefixWord ++ tailWord_642990) baseStart_642990 baseEnd_642990 := by
    simpa [prefixWord, tailWord_642990, baseEnd_642990] using wordTrace_append hprefix tailTrace_642990
  have hstable : (prefixWord ++ tailWord_642990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642990).length < 2 ^ (prefixWord ++ tailWord_642990).sum := by decide
  have hdescent : baseEnd_642990 < baseStart_642990 := by decide
  rcases family_descends (prefixWord ++ tailWord_642990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643001 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_643001 : Nat := 118140960795 + 643001 * 2 ^ 59
def prefixEnd_643001 : Nat := 4983230072969 + 3 ^ 40 * 643001 * 2
def baseEnd_643001 : Nat := 293483177174883546071465

theorem tailTrace_643001 : CollatzResearch.WordTrace tailWord_643001 prefixEnd_643001 293483177174883546071465 := by
  unfold tailWord_643001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452173143524667673024857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634782095683111782016571 23452173143524667673024857)
  ·
    refine ⟨17589129857643500754768643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23452173143524667673024857 17589129857643500754768643)
    ·
      refine ⟨26383694786465251132152965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17589129857643500754768643 26383694786465251132152965)
      ·
        refine ⟨4946942772462234587278681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26383694786465251132152965 4946942772462234587278681)
        ·
          refine ⟨3710207079346675940459011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4946942772462234587278681 3710207079346675940459011)
          ·
            refine ⟨5565310619020013910688517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710207079346675940459011 5565310619020013910688517)
            ·
              refine ⟨1043495741066252608254097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5565310619020013910688517 1043495741066252608254097)
              ·
                refine ⟨782621805799689456190573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043495741066252608254097 782621805799689456190573)
                ·
                  refine ⟨293483177174883546071465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782621805799689456190573 293483177174883546071465)
                  ·
                    rfl

theorem cell20_643001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_643001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643001 prefixEnd_643001 := by exact prefixLift 643001
  have htrace : WordTrace (prefixWord ++ tailWord_643001) baseStart_643001 baseEnd_643001 := by
    simpa [prefixWord, tailWord_643001, baseEnd_643001] using wordTrace_append hprefix tailTrace_643001
  have hstable : (prefixWord ++ tailWord_643001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643001).length < 2 ^ (prefixWord ++ tailWord_643001).sum := by decide
  have hdescent : baseEnd_643001 < baseStart_643001 := by decide
  rcases family_descends (prefixWord ++ tailWord_643001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643067 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_643067 : Nat := 118140960795 + 643067 * 2 ^ 59
def prefixEnd_643067 : Nat := 4983230072969 + 3 ^ 40 * 643067 * 2
def baseEnd_643067 : Nat := 293513301373280649871195

theorem tailTrace_643067 : CollatzResearch.WordTrace tailWord_643067 prefixEnd_643067 293513301373280649871195 := by
  unfold tailWord_643067
  simp only [CollatzResearch.WordTrace]
  refine ⟨23454580361285560944927455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15636386907523707296618303 23454580361285560944927455)
  ·
    refine ⟨35181870541928341417391183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23454580361285560944927455 35181870541928341417391183)
    ·
      refine ⟨52772805812892512126086775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35181870541928341417391183 52772805812892512126086775)
      ·
        refine ⟨79159208719338768189130163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52772805812892512126086775 79159208719338768189130163)
        ·
          refine ⟨118738813079008152283695245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79159208719338768189130163 118738813079008152283695245)
          ·
            refine ⟨44527054904628057106385717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118738813079008152283695245 44527054904628057106385717)
            ·
              refine ⟨4174411397308880353723661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44527054904628057106385717 4174411397308880353723661)
              ·
                refine ⟨1565404273990830132646373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4174411397308880353723661 1565404273990830132646373)
                ·
                  refine ⟨293513301373280649871195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565404273990830132646373 293513301373280649871195)
                  ·
                    rfl

theorem cell20_643067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_643067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643067 prefixEnd_643067 := by exact prefixLift 643067
  have htrace : WordTrace (prefixWord ++ tailWord_643067) baseStart_643067 baseEnd_643067 := by
    simpa [prefixWord, tailWord_643067, baseEnd_643067] using wordTrace_append hprefix tailTrace_643067
  have hstable : (prefixWord ++ tailWord_643067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643067).length < 2 ^ (prefixWord ++ tailWord_643067).sum := by decide
  have hdescent : baseEnd_643067 < baseStart_643067 := by decide
  rcases family_descends (prefixWord ++ tailWord_643067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643091 : List Nat := [1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_643091 : Nat := 118140960795 + 643091 * 2 ^ 59
def prefixEnd_643091 : Nat := 4983230072969 + 3 ^ 40 * 643091 * 2
def baseEnd_643091 : Nat := 97841418542414411023699

theorem tailTrace_643091 : CollatzResearch.WordTrace tailWord_643091 prefixEnd_643091 97841418542414411023699 := by
  unfold tailWord_643091
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455455713198613043801127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15636970475465742029200751 23455455713198613043801127)
  ·
    refine ⟨35183183569797919565701691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23455455713198613043801127 35183183569797919565701691)
    ·
      refine ⟨52774775354696879348552537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35183183569797919565701691 52774775354696879348552537)
      ·
        refine ⟨39581081516022659511414403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52774775354696879348552537 39581081516022659511414403)
        ·
          refine ⟨59371622274033989267121605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39581081516022659511414403 59371622274033989267121605)
          ·
            refine ⟨11132179176381372987585301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59371622274033989267121605 11132179176381372987585301)
            ·
              refine ⟨521820898892876858793061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11132179176381372987585301 521820898892876858793061)
              ·
                refine ⟨97841418542414411023699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521820898892876858793061 97841418542414411023699)
                ·
                  rfl

theorem cell20_643091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_643091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643091 prefixEnd_643091 := by exact prefixLift 643091
  have htrace : WordTrace (prefixWord ++ tailWord_643091) baseStart_643091 baseEnd_643091 := by
    simpa [prefixWord, tailWord_643091, baseEnd_643091] using wordTrace_append hprefix tailTrace_643091
  have hstable : (prefixWord ++ tailWord_643091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643091).length < 2 ^ (prefixWord ++ tailWord_643091).sum := by decide
  have hdescent : baseEnd_643091 < baseStart_643091 := by decide
  rcases family_descends (prefixWord ++ tailWord_643091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643098 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_643098 : Nat := 118140960795 + 643098 * 2 ^ 59
def prefixEnd_643098 : Nat := 4983230072969 + 3 ^ 40 * 643098 * 2
def baseEnd_643098 : Nat := 293527450617982319837735

theorem tailTrace_643098 : CollatzResearch.WordTrace tailWord_643098 prefixEnd_643098 293527450617982319837735 := by
  unfold tailWord_643098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863927756043313309826487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15637140682782168826203965 5863927756043313309826487)
  ·
    refine ⟨8795891634064969964739731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5863927756043313309826487 8795891634064969964739731)
    ·
      refine ⟨13193837451097454947109597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8795891634064969964739731 13193837451097454947109597)
      ·
        refine ⟨4947689044161545605166099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13193837451097454947109597 4947689044161545605166099)
        ·
          refine ⟨7421533566242318407749149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947689044161545605166099 7421533566242318407749149)
          ·
            refine ⟨2783075087340869402905931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7421533566242318407749149 2783075087340869402905931)
            ·
              refine ⟨4174612631011304104358897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783075087340869402905931 4174612631011304104358897)
              ·
                refine ⟨3130959473258478078269173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174612631011304104358897 3130959473258478078269173)
                ·
                  refine ⟨293527450617982319837735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130959473258478078269173 293527450617982319837735)
                  ·
                    rfl

theorem cell20_643098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_643098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643098 prefixEnd_643098 := by exact prefixLift 643098
  have htrace : WordTrace (prefixWord ++ tailWord_643098) baseStart_643098 baseEnd_643098 := by
    simpa [prefixWord, tailWord_643098, baseEnd_643098] using wordTrace_append hprefix tailTrace_643098
  have hstable : (prefixWord ++ tailWord_643098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643098).length < 2 ^ (prefixWord ++ tailWord_643098).sum := by decide
  have hdescent : baseEnd_643098 < baseStart_643098 := by decide
  rcases family_descends (prefixWord ++ tailWord_643098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643108 : List Nat := [2, 3, 1, 4, 2, 2, 6]
def baseStart_643108 : Nat := 118140960795 + 643108 * 2 ^ 59
def prefixEnd_643108 : Nat := 4983230072969 + 3 ^ 40 * 643108 * 2
def baseEnd_643108 : Nat := 32614668321162969944929

theorem tailTrace_643108 : CollatzResearch.WordTrace tailWord_643108 prefixEnd_643108 32614668321162969944929 := by
  unfold tailWord_643108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728037877068512473584989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15637383836091349964779985 11728037877068512473584989)
  ·
    refine ⟨4398014203900692177594371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11728037877068512473584989 4398014203900692177594371)
    ·
      refine ⟨6597021305851038266391557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398014203900692177594371 6597021305851038266391557)
      ·
        refine ⟨1236941494847069674948417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6597021305851038266391557 1236941494847069674948417)
        ·
          refine ⟨927706121135302256211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236941494847069674948417 927706121135302256211313)
          ·
            refine ⟨695779590851476692158485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927706121135302256211313 695779590851476692158485)
            ·
              refine ⟨32614668321162969944929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 695779590851476692158485 32614668321162969944929)
              ·
                rfl

theorem cell20_643108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_643108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643108 prefixEnd_643108 := by exact prefixLift 643108
  have htrace : WordTrace (prefixWord ++ tailWord_643108) baseStart_643108 baseEnd_643108 := by
    simpa [prefixWord, tailWord_643108, baseEnd_643108] using wordTrace_append hprefix tailTrace_643108
  have hstable : (prefixWord ++ tailWord_643108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643108).length < 2 ^ (prefixWord ++ tailWord_643108).sum := by decide
  have hdescent : baseEnd_643108 < baseStart_643108 := by decide
  rcases family_descends (prefixWord ++ tailWord_643108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643122 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_643122 : Nat := 118140960795 + 643122 * 2 ^ 59
def prefixEnd_643122 : Nat := 4983230072969 + 3 ^ 40 * 643122 * 2
def baseEnd_643122 : Nat := 293538404871944903037637

theorem tailTrace_643122 : CollatzResearch.WordTrace tailWord_643122 prefixEnd_643122 293538404871944903037637 := by
  unfold tailWord_643122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864146594021576334544905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15637724250724203558786413 5864146594021576334544905)
  ·
    refine ⟨4398109945516182250908679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5864146594021576334544905 4398109945516182250908679)
    ·
      refine ⟨6597164918274273376363019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398109945516182250908679 6597164918274273376363019)
      ·
        refine ⟨9895747377411410064544529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6597164918274273376363019 9895747377411410064544529)
        ·
          refine ⟨7421810533058557548408397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895747377411410064544529 7421810533058557548408397)
          ·
            refine ⟨2783178949896959080653149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7421810533058557548408397 2783178949896959080653149)
            ·
              refine ⟨1043692106211359655244931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2783178949896959080653149 1043692106211359655244931)
              ·
                refine ⟨1565538159317039482867397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043692106211359655244931 1565538159317039482867397)
                ·
                  refine ⟨293538404871944903037637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565538159317039482867397 293538404871944903037637)
                  ·
                    rfl

theorem cell20_643122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_643122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643122 prefixEnd_643122 := by exact prefixLift 643122
  have htrace : WordTrace (prefixWord ++ tailWord_643122) baseStart_643122 baseEnd_643122 := by
    simpa [prefixWord, tailWord_643122, baseEnd_643122] using wordTrace_append hprefix tailTrace_643122
  have hstable : (prefixWord ++ tailWord_643122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643122).length < 2 ^ (prefixWord ++ tailWord_643122).sum := by decide
  have hdescent : baseEnd_643122 < baseStart_643122 := by decide
  rcases family_descends (prefixWord ++ tailWord_643122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643143 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_643143 : Nat := 118140960795 + 643143 * 2 ^ 59
def prefixEnd_643143 : Nat := 4983230072969 + 3 ^ 40 * 643143 * 2
def baseEnd_643143 : Nat := 293547989844162163337551

theorem tailTrace_643143 : CollatzResearch.WordTrace tailWord_643143 prefixEnd_643143 293547989844162163337551 := by
  unfold tailWord_643143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23457352309010225924694083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15638234872673483949796055 23457352309010225924694083)
  ·
    refine ⟨35186028463515338887041125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23457352309010225924694083 35186028463515338887041125)
    ·
      refine ⟨6597380336909126041320211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35186028463515338887041125 6597380336909126041320211)
      ·
        refine ⟨9896070505363689061980317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6597380336909126041320211 9896070505363689061980317)
        ·
          refine ⟨3711026439511383398242619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9896070505363689061980317 3711026439511383398242619)
          ·
            refine ⟨5566539659267075097363929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711026439511383398242619 5566539659267075097363929)
            ·
              refine ⟨4174904744450306323022947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566539659267075097363929 4174904744450306323022947)
              ·
                refine ⟨6262357116675459484534421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174904744450306323022947 6262357116675459484534421)
                ·
                  refine ⟨293547989844162163337551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6262357116675459484534421 293547989844162163337551)
                  ·
                    rfl

theorem cell20_643143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_643143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643143 prefixEnd_643143 := by exact prefixLift 643143
  have htrace : WordTrace (prefixWord ++ tailWord_643143) baseStart_643143 baseEnd_643143 := by
    simpa [prefixWord, tailWord_643143, baseEnd_643143] using wordTrace_append hprefix tailTrace_643143
  have hstable : (prefixWord ++ tailWord_643143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643143).length < 2 ^ (prefixWord ++ tailWord_643143).sum := by decide
  have hdescent : baseEnd_643143 < baseStart_643143 := by decide
  rcases family_descends (prefixWord ++ tailWord_643143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643166 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_643166 : Nat := 118140960795 + 643166 * 2 ^ 59
def prefixEnd_643166 : Nat := 4983230072969 + 3 ^ 40 * 643166 * 2
def baseEnd_643166 : Nat := 293558487670876305570791

theorem tailTrace_643166 : CollatzResearch.WordTrace tailWord_643166 prefixEnd_643166 293558487670876305570791 := by
  unfold tailWord_643166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932273898490862606597669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15638794125284600568520901 2932273898490862606597669)
  ·
    refine ⟨549801355967036738737063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2932273898490862606597669 549801355967036738737063)
    ·
      refine ⟨824702033950555108105595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549801355967036738737063 824702033950555108105595)
      ·
        refine ⟨1237053050925832662158393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824702033950555108105595 1237053050925832662158393)
        ·
          refine ⟨927789788194374496618795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237053050925832662158393 927789788194374496618795)
          ·
            refine ⟨1391684682291561744928193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927789788194374496618795 1391684682291561744928193)
            ·
              refine ⟨1043763511718671308696145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391684682291561744928193 1043763511718671308696145)
              ·
                refine ⟨782822633789003481522109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043763511718671308696145 782822633789003481522109)
                ·
                  refine ⟨293558487670876305570791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782822633789003481522109 293558487670876305570791)
                  ·
                    rfl

theorem cell20_643166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_643166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643166 prefixEnd_643166 := by exact prefixLift 643166
  have htrace : WordTrace (prefixWord ++ tailWord_643166) baseStart_643166 baseEnd_643166 := by
    simpa [prefixWord, tailWord_643166, baseEnd_643166] using wordTrace_append hprefix tailTrace_643166
  have hstable : (prefixWord ++ tailWord_643166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643166).length < 2 ^ (prefixWord ++ tailWord_643166).sum := by decide
  have hdescent : baseEnd_643166 < baseStart_643166 := by decide
  rcases family_descends (prefixWord ++ tailWord_643166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643195 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_643195 : Nat := 118140960795 + 643195 * 2 ^ 59
def prefixEnd_643195 : Nat := 4983230072969 + 3 ^ 40 * 643195 * 2
def baseEnd_643195 : Nat := 293571724061081093604005

theorem tailTrace_643195 : CollatzResearch.WordTrace tailWord_643195 prefixEnd_643195 293571724061081093604005 := by
  unfold tailWord_643195
  simp only [CollatzResearch.WordTrace]
  refine ⟨23459248904821838805587039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15639499269881225870391359 23459248904821838805587039)
  ·
    refine ⟨35188873357232758208380559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23459248904821838805587039 35188873357232758208380559)
    ·
      refine ⟨52783310035849137312570839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35188873357232758208380559 52783310035849137312570839)
      ·
        refine ⟨79174965053773705968856259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52783310035849137312570839 79174965053773705968856259)
        ·
          refine ⟨118762447580660558953284389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79174965053773705968856259 118762447580660558953284389)
          ·
            refine ⟨22267958921373854803740823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118762447580660558953284389 22267958921373854803740823)
            ·
              refine ⟨33401938382060782205611235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22267958921373854803740823 33401938382060782205611235)
              ·
                refine ⟨50102907573091173308416853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33401938382060782205611235 50102907573091173308416853)
                ·
                  refine ⟨293571724061081093604005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50102907573091173308416853 293571724061081093604005)
                  ·
                    rfl

theorem cell20_643195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_643195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643195 prefixEnd_643195 := by exact prefixLift 643195
  have htrace : WordTrace (prefixWord ++ tailWord_643195) baseStart_643195 baseEnd_643195 := by
    simpa [prefixWord, tailWord_643195, baseEnd_643195] using wordTrace_append hprefix tailTrace_643195
  have hstable : (prefixWord ++ tailWord_643195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643195).length < 2 ^ (prefixWord ++ tailWord_643195).sum := by decide
  have hdescent : baseEnd_643195 < baseStart_643195 := by decide
  rcases family_descends (prefixWord ++ tailWord_643195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643229 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_643229 : Nat := 118140960795 + 643229 * 2 ^ 59
def prefixEnd_643229 : Nat := 4983230072969 + 3 ^ 40 * 643229 * 2
def baseEnd_643229 : Nat := 293587242587528086470533

theorem tailTrace_643229 : CollatzResearch.WordTrace tailWord_643229 prefixEnd_643229 293587242587528086470533 := by
  unfold tailWord_643229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23460488986698662612324741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15640325991132441741549827 23460488986698662612324741)
  ·
    refine ⟨4398841685005999239810889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23460488986698662612324741 4398841685005999239810889)
    ·
      refine ⟨3299131263754499429858167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4398841685005999239810889 3299131263754499429858167)
      ·
        refine ⟨4948696895631749144787251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299131263754499429858167 4948696895631749144787251)
        ·
          refine ⟨7423045343447623717180877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948696895631749144787251 7423045343447623717180877)
          ·
            refine ⟨2783642003792858893942829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7423045343447623717180877 2783642003792858893942829)
            ·
              refine ⟨1043865751422322085228561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2783642003792858893942829 1043865751422322085228561)
              ·
                refine ⟨782899313566741563921421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043865751422322085228561 782899313566741563921421)
                ·
                  refine ⟨293587242587528086470533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782899313566741563921421 293587242587528086470533)
                  ·
                    rfl

theorem cell20_643229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_643229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643229 prefixEnd_643229 := by exact prefixLift 643229
  have htrace : WordTrace (prefixWord ++ tailWord_643229) baseStart_643229 baseEnd_643229 := by
    simpa [prefixWord, tailWord_643229, baseEnd_643229] using wordTrace_append hprefix tailTrace_643229
  have hstable : (prefixWord ++ tailWord_643229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643229).length < 2 ^ (prefixWord ++ tailWord_643229).sum := by decide
  have hdescent : baseEnd_643229 < baseStart_643229 := by decide
  rcases family_descends (prefixWord ++ tailWord_643229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643252 : List Nat := [2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_643252 : Nat := 118140960795 + 643252 * 2 ^ 59
def prefixEnd_643252 : Nat := 4983230072969 + 3 ^ 40 * 643252 * 2
def baseEnd_643252 : Nat := 97865913471414076234591

theorem tailTrace_643252 : CollatzResearch.WordTrace tailWord_643252 prefixEnd_643252 97865913471414076234591 := by
  unfold tailWord_643252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11730663932807668770206005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15640885243743558360274673 11730663932807668770206005)
  ·
    refine ⟨1099749743700718947206813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11730663932807668770206005 1099749743700718947206813)
    ·
      refine ⟨412406153887769605202555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1099749743700718947206813 412406153887769605202555)
      ·
        refine ⟨618609230831654407803833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412406153887769605202555 618609230831654407803833)
        ·
          refine ⟨463956923123740805852875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618609230831654407803833 463956923123740805852875)
          ·
            refine ⟨695935384685611208779313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463956923123740805852875 695935384685611208779313)
            ·
              refine ⟨521951538514208406584485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695935384685611208779313 521951538514208406584485)
              ·
                refine ⟨97865913471414076234591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521951538514208406584485 97865913471414076234591)
                ·
                  rfl

theorem cell20_643252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_643252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643252 prefixEnd_643252 := by exact prefixLift 643252
  have htrace : WordTrace (prefixWord ++ tailWord_643252) baseStart_643252 baseEnd_643252 := by
    simpa [prefixWord, tailWord_643252, baseEnd_643252] using wordTrace_append hprefix tailTrace_643252
  have hstable : (prefixWord ++ tailWord_643252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643252).length < 2 ^ (prefixWord ++ tailWord_643252).sum := by decide
  have hdescent : baseEnd_643252 < baseStart_643252 := by decide
  rcases family_descends (prefixWord ++ tailWord_643252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643257 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_643257 : Nat := 118140960795 + 643257 * 2 ^ 59
def prefixEnd_643257 : Nat := 4983230072969 + 3 ^ 40 * 643257 * 2
def baseEnd_643257 : Nat := 293600022550484433537085

theorem tailTrace_643257 : CollatzResearch.WordTrace tailWord_643257 prefixEnd_643257 293600022550484433537085 := by
  unfold tailWord_643257
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461510230597223394344025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15641006820398148929562683 23461510230597223394344025)
  ·
    refine ⟨17596132672947917545758019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23461510230597223394344025 17596132672947917545758019)
    ·
      refine ⟨26394199009421876318637029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17596132672947917545758019 26394199009421876318637029)
      ·
        refine ⟨4948912314266601809744443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26394199009421876318637029 4948912314266601809744443)
        ·
          refine ⟨7423368471399902714616665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948912314266601809744443 7423368471399902714616665)
          ·
            refine ⟨5567526353549927035962499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7423368471399902714616665 5567526353549927035962499)
            ·
              refine ⟨8351289530324890553943749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567526353549927035962499 8351289530324890553943749)
              ·
                refine ⟨1565866786935916978864453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8351289530324890553943749 1565866786935916978864453)
                ·
                  refine ⟨293600022550484433537085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565866786935916978864453 293600022550484433537085)
                  ·
                    rfl

theorem cell20_643257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_643257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643257 prefixEnd_643257 := by exact prefixLift 643257
  have htrace : WordTrace (prefixWord ++ tailWord_643257) baseStart_643257 baseEnd_643257 := by
    simpa [prefixWord, tailWord_643257, baseEnd_643257] using wordTrace_append hprefix tailTrace_643257
  have hstable : (prefixWord ++ tailWord_643257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643257).length < 2 ^ (prefixWord ++ tailWord_643257).sum := by decide
  have hdescent : baseEnd_643257 < baseStart_643257 := by decide
  rcases family_descends (prefixWord ++ tailWord_643257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643266 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_643266 : Nat := 118140960795 + 643266 * 2 ^ 59
def prefixEnd_643266 : Nat := 4983230072969 + 3 ^ 40 * 643266 * 2
def baseEnd_643266 : Nat := 293604130395720402237049

theorem tailTrace_643266 : CollatzResearch.WordTrace tailWord_643266 prefixEnd_643266 293604130395720402237049 := by
  unfold tailWord_643266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865459621891154482855413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15641225658376411954281101 5865459621891154482855413)
  ·
    refine ⟨549886839552295732767695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5865459621891154482855413 549886839552295732767695)
    ·
      refine ⟨824830259328443599151543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549886839552295732767695 824830259328443599151543)
      ·
        refine ⟨1237245388992665398727315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824830259328443599151543 1237245388992665398727315)
        ·
          refine ⟨1855868083488998098090973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237245388992665398727315 1855868083488998098090973)
          ·
            refine ⟨695950531308374286784115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1855868083488998098090973 695950531308374286784115)
            ·
              refine ⟨1043925796962561430176173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695950531308374286784115 1043925796962561430176173)
              ·
                refine ⟨391472173860960536316065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043925796962561430176173 391472173860960536316065)
                ·
                  refine ⟨293604130395720402237049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391472173860960536316065 293604130395720402237049)
                  ·
                    rfl

theorem cell20_643266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_643266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643266 prefixEnd_643266 := by exact prefixLift 643266
  have htrace : WordTrace (prefixWord ++ tailWord_643266) baseStart_643266 baseEnd_643266 := by
    simpa [prefixWord, tailWord_643266, baseEnd_643266] using wordTrace_append hprefix tailTrace_643266
  have hstable : (prefixWord ++ tailWord_643266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643266).length < 2 ^ (prefixWord ++ tailWord_643266).sum := by decide
  have hdescent : baseEnd_643266 < baseStart_643266 := by decide
  rcases family_descends (prefixWord ++ tailWord_643266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643288 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_643288 : Nat := 118140960795 + 643288 * 2 ^ 59
def prefixEnd_643288 : Nat := 4983230072969 + 3 ^ 40 * 643288 * 2
def baseEnd_643288 : Nat := 293614171795186103503625

theorem tailTrace_643288 : CollatzResearch.WordTrace tailWord_643288 prefixEnd_643288 293614171795186103503625 := by
  unfold tailWord_643288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731320446742457844361259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15641760595656610459148345 11731320446742457844361259)
  ·
    refine ⟨17596980670113686766541889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11731320446742457844361259 17596980670113686766541889)
    ·
      refine ⟨13197735502585265074906417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17596980670113686766541889 13197735502585265074906417)
      ·
        refine ⟨9898301626938948806179813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13197735502585265074906417 9898301626938948806179813)
        ·
          refine ⟨1855931555051052901158715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9898301626938948806179813 1855931555051052901158715)
          ·
            refine ⟨2783897332576579351738073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855931555051052901158715 2783897332576579351738073)
            ·
              refine ⟨2087922999432434513803555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2783897332576579351738073 2087922999432434513803555)
              ·
                refine ⟨3131884499148651770705333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087922999432434513803555 3131884499148651770705333)
                ·
                  refine ⟨293614171795186103503625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131884499148651770705333 293614171795186103503625)
                  ·
                    rfl

theorem cell20_643288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_643288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643288 prefixEnd_643288 := by exact prefixLift 643288
  have htrace : WordTrace (prefixWord ++ tailWord_643288) baseStart_643288 baseEnd_643288 := by
    simpa [prefixWord, tailWord_643288, baseEnd_643288] using wordTrace_append hprefix tailTrace_643288
  have hstable : (prefixWord ++ tailWord_643288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643288).length < 2 ^ (prefixWord ++ tailWord_643288).sum := by decide
  have hdescent : baseEnd_643288 < baseStart_643288 := by decide
  rcases family_descends (prefixWord ++ tailWord_643288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643347 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_643347 : Nat := 118140960795 + 643347 * 2 ^ 59
def prefixEnd_643347 : Nat := 4983230072969 + 3 ^ 40 * 643347 * 2
def baseEnd_643347 : Nat := 293641101002844120536717

theorem tailTrace_643347 : CollatzResearch.WordTrace tailWord_643347 prefixEnd_643347 293641101002844120536717 := by
  unfold tailWord_643347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464792800271168765120295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15643195200180779176746863 23464792800271168765120295)
  ·
    refine ⟨35197189200406753147680443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23464792800271168765120295 35197189200406753147680443)
    ·
      refine ⟨52795783800610129721520665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35197189200406753147680443 52795783800610129721520665)
      ·
        refine ⟨39596837850457597291140499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52795783800610129721520665 39596837850457597291140499)
        ·
          refine ⟨59395256775686395936710749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39596837850457597291140499 59395256775686395936710749)
          ·
            refine ⟨22273221290882398476266531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59395256775686395936710749 22273221290882398476266531)
            ·
              refine ⟨33409831936323597714399797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22273221290882398476266531 33409831936323597714399797)
              ·
                refine ⟨3132171744030337285724981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33409831936323597714399797 3132171744030337285724981)
                ·
                  refine ⟨293641101002844120536717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132171744030337285724981 293641101002844120536717)
                  ·
                    rfl

theorem cell20_643347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_643347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643347 prefixEnd_643347 := by exact prefixLift 643347
  have htrace : WordTrace (prefixWord ++ tailWord_643347) baseStart_643347 baseEnd_643347 := by
    simpa [prefixWord, tailWord_643347, baseEnd_643347] using wordTrace_append hprefix tailTrace_643347
  have hstable : (prefixWord ++ tailWord_643347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643347).length < 2 ^ (prefixWord ++ tailWord_643347).sum := by decide
  have hdescent : baseEnd_643347 < baseStart_643347 := by decide
  rcases family_descends (prefixWord ++ tailWord_643347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643409 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_643409 : Nat := 118140960795 + 643409 * 2 ^ 59
def prefixEnd_643409 : Nat := 4983230072969 + 3 ^ 40 * 643409 * 2
def baseEnd_643409 : Nat := 293669399492247460469797

theorem tailTrace_643409 : CollatzResearch.WordTrace tailWord_643409 prefixEnd_643409 293669399492247460469797 := by
  unfold tailWord_643409
  simp only [CollatzResearch.WordTrace]
  refine ⟨23467054126046553353877281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15644702750697702235918187 23467054126046553353877281)
  ·
    refine ⟨17600290594534915015407961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23467054126046553353877281 17600290594534915015407961)
    ·
      refine ⟨13200217945901186261555971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17600290594534915015407961 13200217945901186261555971)
      ·
        refine ⟨19800326918851779392333957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13200217945901186261555971 19800326918851779392333957)
        ·
          refine ⟨3712561297284708636062617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19800326918851779392333957 3712561297284708636062617)
          ·
            refine ⟨2784420972963531477046963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712561297284708636062617 2784420972963531477046963)
            ·
              refine ⟨4176631459445297215570445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784420972963531477046963 4176631459445297215570445)
              ·
                refine ⟨1566236797291986455838917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176631459445297215570445 1566236797291986455838917)
                ·
                  refine ⟨293669399492247460469797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566236797291986455838917 293669399492247460469797)
                  ·
                    rfl

theorem cell20_643409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_643409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643409 prefixEnd_643409 := by exact prefixLift 643409
  have htrace : WordTrace (prefixWord ++ tailWord_643409) baseStart_643409 baseEnd_643409 := by
    simpa [prefixWord, tailWord_643409, baseEnd_643409] using wordTrace_append hprefix tailTrace_643409
  have hstable : (prefixWord ++ tailWord_643409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643409).length < 2 ^ (prefixWord ++ tailWord_643409).sum := by decide
  have hdescent : baseEnd_643409 < baseStart_643409 := by decide
  rcases family_descends (prefixWord ++ tailWord_643409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643426 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_643426 : Nat := 118140960795 + 643426 * 2 ^ 59
def prefixEnd_643426 : Nat := 4983230072969 + 3 ^ 40 * 643426 * 2
def baseEnd_643426 : Nat := 293677158755470956903061

theorem tailTrace_643426 : CollatzResearch.WordTrace tailWord_643426 prefixEnd_643426 293677158755470956903061 := by
  unfold tailWord_643426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866918541746241314311533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15645116111323310171497421 5866918541746241314311533)
  ·
    refine ⟨2200094453154840492866825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5866918541746241314311533 2200094453154840492866825)
    ·
      refine ⟨1650070839866130369650119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200094453154840492866825 1650070839866130369650119)
      ·
        refine ⟨2475106259799195554475179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650070839866130369650119 2475106259799195554475179)
        ·
          refine ⟨3712659389698793331712769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475106259799195554475179 3712659389698793331712769)
          ·
            refine ⟨2784494542274094998784577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712659389698793331712769 2784494542274094998784577)
            ·
              refine ⟨2088370906705571249088433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784494542274094998784577 2088370906705571249088433)
              ·
                refine ⟨1566278180029178436816325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088370906705571249088433 1566278180029178436816325)
                ·
                  refine ⟨293677158755470956903061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566278180029178436816325 293677158755470956903061)
                  ·
                    rfl

theorem cell20_643426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_643426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643426 prefixEnd_643426 := by exact prefixLift 643426
  have htrace : WordTrace (prefixWord ++ tailWord_643426) baseStart_643426 baseEnd_643426 := by
    simpa [prefixWord, tailWord_643426, baseEnd_643426] using wordTrace_append hprefix tailTrace_643426
  have hstable : (prefixWord ++ tailWord_643426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643426).length < 2 ^ (prefixWord ++ tailWord_643426).sum := by decide
  have hdescent : baseEnd_643426 < baseStart_643426 := by decide
  rcases family_descends (prefixWord ++ tailWord_643426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643492 : List Nat := [2, 3, 1, 2, 1, 1, 4, 6]
def baseStart_643492 : Nat := 118140960795 + 643492 * 2 ^ 59
def prefixEnd_643492 : Nat := 4983230072969 + 3 ^ 40 * 643492 * 2
def baseEnd_643492 : Nat := 97902427651289353567597

theorem tailTrace_643492 : CollatzResearch.WordTrace tailWord_643492 prefixEnd_643492 97902427651289353567597 := by
  unfold tailWord_643492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735040692372929264574365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15646720923163905686099153 11735040692372929264574365)
  ·
    refine ⟨4400640259639848474215387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11735040692372929264574365 4400640259639848474215387)
    ·
      refine ⟨6600960389459772711323081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400640259639848474215387 6600960389459772711323081)
      ·
        refine ⟨4950720292094829533492311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6600960389459772711323081 4950720292094829533492311)
        ·
          refine ⟨7426080438142244300238467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950720292094829533492311 7426080438142244300238467)
          ·
            refine ⟨11139120657213366450357701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426080438142244300238467 11139120657213366450357701)
            ·
              refine ⟨2088585123227506209442069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11139120657213366450357701 2088585123227506209442069)
              ·
                refine ⟨97902427651289353567597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2088585123227506209442069 97902427651289353567597)
                ·
                  rfl

theorem cell20_643492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_643492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643492 prefixEnd_643492 := by exact prefixLift 643492
  have htrace : WordTrace (prefixWord ++ tailWord_643492) baseStart_643492 baseEnd_643492 := by
    simpa [prefixWord, tailWord_643492, baseEnd_643492] using wordTrace_append hprefix tailTrace_643492
  have hstable : (prefixWord ++ tailWord_643492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643492).length < 2 ^ (prefixWord ++ tailWord_643492).sum := by decide
  have hdescent : baseEnd_643492 < baseStart_643492 := by decide
  rcases family_descends (prefixWord ++ tailWord_643492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643509 : List Nat := [1, 3, 3, 2, 4, 7]
def baseStart_643509 : Nat := 118140960795 + 643509 * 2 ^ 59
def prefixEnd_643509 : Nat := 4983230072969 + 3 ^ 40 * 643509 * 2
def baseEnd_643509 : Nat := 10878334896929316930965

theorem tailTrace_643509 : CollatzResearch.WordTrace tailWord_643509 prefixEnd_643509 10878334896929316930965 := by
  unfold tailWord_643509
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470701425684270432517581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15647134283789513621678387 23470701425684270432517581)
  ·
    refine ⟨8801513034631601412194093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23470701425684270432517581 8801513034631601412194093)
    ·
      refine ⟨3300567387986850529572785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8801513034631601412194093 3300567387986850529572785)
      ·
        refine ⟨2475425540990137897179589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3300567387986850529572785 2475425540990137897179589)
        ·
          refine ⟨464142288935650855721173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2475425540990137897179589 464142288935650855721173)
          ·
            refine ⟨10878334896929316930965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 464142288935650855721173 10878334896929316930965)
            ·
              rfl

theorem cell20_643509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 7].length) (baseStart_643509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643509 prefixEnd_643509 := by exact prefixLift 643509
  have htrace : WordTrace (prefixWord ++ tailWord_643509) baseStart_643509 baseEnd_643509 := by
    simpa [prefixWord, tailWord_643509, baseEnd_643509] using wordTrace_append hprefix tailTrace_643509
  have hstable : (prefixWord ++ tailWord_643509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643509).length < 2 ^ (prefixWord ++ tailWord_643509).sum := by decide
  have hdescent : baseEnd_643509 < baseStart_643509 := by decide
  rcases family_descends (prefixWord ++ tailWord_643509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643540 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_643540 : Nat := 118140960795 + 643540 * 2 ^ 59
def prefixEnd_643540 : Nat := 4983230072969 + 3 ^ 40 * 643540 * 2
def baseEnd_643540 : Nat := 293729191461793227102595

theorem tailTrace_643540 : CollatzResearch.WordTrace tailWord_643540 prefixEnd_643540 293729191461793227102595 := by
  unfold tailWord_643540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735916044285981363448037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15647888059047975151264049 11735916044285981363448037)
  ·
    refine ⟨2200484258303621505646507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11735916044285981363448037 2200484258303621505646507)
    ·
      refine ⟨3300726387455432258469761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200484258303621505646507 3300726387455432258469761)
      ·
        refine ⟨2475544790591574193852321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3300726387455432258469761 2475544790591574193852321)
        ·
          refine ⟨1856658592943680645389241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475544790591574193852321 1856658592943680645389241)
          ·
            refine ⟨1392493944707760484041931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1856658592943680645389241 1392493944707760484041931)
            ·
              refine ⟨2088740917061640726062897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392493944707760484041931 2088740917061640726062897)
              ·
                refine ⟨1566555687796230544547173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088740917061640726062897 1566555687796230544547173)
                ·
                  refine ⟨293729191461793227102595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566555687796230544547173 293729191461793227102595)
                  ·
                    rfl

theorem cell20_643540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_643540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643540 prefixEnd_643540 := by exact prefixLift 643540
  have htrace : WordTrace (prefixWord ++ tailWord_643540) baseStart_643540 baseEnd_643540 := by
    simpa [prefixWord, tailWord_643540, baseEnd_643540] using wordTrace_append hprefix tailTrace_643540
  have hstable : (prefixWord ++ tailWord_643540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643540).length < 2 ^ (prefixWord ++ tailWord_643540).sum := by decide
  have hdescent : baseEnd_643540 < baseStart_643540 := by decide
  rcases family_descends (prefixWord ++ tailWord_643540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643588 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_643588 : Nat := 118140960795 + 643588 * 2 ^ 59
def prefixEnd_643588 : Nat := 4983230072969 + 3 ^ 40 * 643588 * 2
def baseEnd_643588 : Nat := 293751099969718393502399

theorem tailTrace_643588 : CollatzResearch.WordTrace tailWord_643588 prefixEnd_643588 293751099969718393502399 := by
  unfold tailWord_643588
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736791396199033462321709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15649055194932044616428945 11736791396199033462321709)
  ·
    refine ⟨4401296773574637548370641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11736791396199033462321709 4401296773574637548370641)
    ·
      refine ⟨3300972580180978161277981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4401296773574637548370641 3300972580180978161277981)
      ·
        refine ⟨1237864717567866810479243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3300972580180978161277981 1237864717567866810479243)
        ·
          refine ⟨1856797076351800215718865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237864717567866810479243 1856797076351800215718865)
          ·
            refine ⟨1392597807263850161789149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1856797076351800215718865 1392597807263850161789149)
            ·
              refine ⟨522224177723943810670931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392597807263850161789149 522224177723943810670931)
              ·
                refine ⟨783336266585915716006397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522224177723943810670931 783336266585915716006397)
                ·
                  refine ⟨293751099969718393502399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783336266585915716006397 293751099969718393502399)
                  ·
                    rfl

theorem cell20_643588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_643588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643588 prefixEnd_643588 := by exact prefixLift 643588
  have htrace : WordTrace (prefixWord ++ tailWord_643588) baseStart_643588 baseEnd_643588 := by
    simpa [prefixWord, tailWord_643588, baseEnd_643588] using wordTrace_append hprefix tailTrace_643588
  have hstable : (prefixWord ++ tailWord_643588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643588).length < 2 ^ (prefixWord ++ tailWord_643588).sum := by decide
  have hdescent : baseEnd_643588 < baseStart_643588 := by decide
  rcases family_descends (prefixWord ++ tailWord_643588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643629 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 4]
def baseStart_643629 : Nat := 118140960795 + 643629 * 2 ^ 59
def prefixEnd_643629 : Nat := 4983230072969 + 3 ^ 40 * 643629 * 2
def baseEnd_643629 : Nat := 293769813486904473135565

theorem tailTrace_643629 : CollatzResearch.WordTrace tailWord_643629 prefixEnd_643629 293769813486904473135565 := by
  unfold tailWord_643629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475078185249530926885941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650052123499687284590627 23475078185249530926885941)
  ·
    refine ⟨2200788579867143524395557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23475078185249530926885941 2200788579867143524395557)
    ·
      refine ⟨412647858725089410824167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2200788579867143524395557 412647858725089410824167)
      ·
        refine ⟨618971788087634116236251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412647858725089410824167 618971788087634116236251)
        ·
          refine ⟨928457682131451174354377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618971788087634116236251 928457682131451174354377)
          ·
            refine ⟨696343261598588380765783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928457682131451174354377 696343261598588380765783)
            ·
              refine ⟨1044514892397882571148675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696343261598588380765783 1044514892397882571148675)
              ·
                refine ⟨1566772338596823856723013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044514892397882571148675 1566772338596823856723013)
                ·
                  refine ⟨293769813486904473135565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566772338596823856723013 293769813486904473135565)
                  ·
                    rfl

theorem cell20_643629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_643629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643629 prefixEnd_643629 := by exact prefixLift 643629
  have htrace : WordTrace (prefixWord ++ tailWord_643629) baseStart_643629 baseEnd_643629 := by
    simpa [prefixWord, tailWord_643629, baseEnd_643629] using wordTrace_append hprefix tailTrace_643629
  have hstable : (prefixWord ++ tailWord_643629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643629).length < 2 ^ (prefixWord ++ tailWord_643629).sum := by decide
  have hdescent : baseEnd_643629 < baseStart_643629 := by decide
  rcases family_descends (prefixWord ++ tailWord_643629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643644 : List Nat := [2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_643644 : Nat := 118140960795 + 643644 * 2 ^ 59
def prefixEnd_643644 : Nat := 4983230072969 + 3 ^ 40 * 643644 * 2
def baseEnd_643644 : Nat := 97925553298543695878501

theorem tailTrace_643644 : CollatzResearch.WordTrace tailWord_643644 prefixEnd_643644 97925553298543695878501 := by
  unfold tailWord_643644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737812640097594244340993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15650416853463458992454657 11737812640097594244340993)
  ·
    refine ⟨8803359480073195683255745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11737812640097594244340993 8803359480073195683255745)
    ·
      refine ⟨6602519610054896762441809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8803359480073195683255745 6602519610054896762441809)
      ·
        refine ⟨4951889707541172571831357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6602519610054896762441809 4951889707541172571831357)
        ·
          refine ⟨1856958640327939714436759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4951889707541172571831357 1856958640327939714436759)
          ·
            refine ⟨2785437960491909571655139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856958640327939714436759 2785437960491909571655139)
            ·
              refine ⟨4178156940737864357482709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785437960491909571655139 4178156940737864357482709)
              ·
                refine ⟨97925553298543695878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4178156940737864357482709 97925553298543695878501)
                ·
                  rfl

theorem cell20_643644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_643644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643644 prefixEnd_643644 := by exact prefixLift 643644
  have htrace : WordTrace (prefixWord ++ tailWord_643644) baseStart_643644 baseEnd_643644 := by
    simpa [prefixWord, tailWord_643644, baseEnd_643644] using wordTrace_append hprefix tailTrace_643644
  have hstable : (prefixWord ++ tailWord_643644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643644).length < 2 ^ (prefixWord ++ tailWord_643644).sum := by decide
  have hdescent : baseEnd_643644 < baseStart_643644 := by decide
  rcases family_descends (prefixWord ++ tailWord_643644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643661 : List Nat := [1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_643661 : Nat := 118140960795 + 643661 * 2 ^ 59
def prefixEnd_643661 : Nat := 4983230072969 + 3 ^ 40 * 643661 * 2
def baseEnd_643661 : Nat := 97928139719618194689589

theorem tailTrace_643661 : CollatzResearch.WordTrace tailWord_643661 prefixEnd_643661 97928139719618194689589 := by
  unfold tailWord_643661
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476245321133600392050837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650830214089066928033891 23476245321133600392050837)
  ·
    refine ⟨1100448999428137518377383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23476245321133600392050837 1100448999428137518377383)
    ·
      refine ⟨1650673499142206277566075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100448999428137518377383 1650673499142206277566075)
      ·
        refine ⟨2476010248713309416349113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650673499142206277566075 2476010248713309416349113)
        ·
          refine ⟨1857007686534982062261835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2476010248713309416349113 1857007686534982062261835)
          ·
            refine ⟨2785511529802473093392753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857007686534982062261835 2785511529802473093392753)
            ·
              refine ⟨2089133647351854820044565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785511529802473093392753 2089133647351854820044565)
              ·
                refine ⟨97928139719618194689589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2089133647351854820044565 97928139719618194689589)
                ·
                  rfl

theorem cell20_643661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_643661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643661 prefixEnd_643661 := by exact prefixLift 643661
  have htrace : WordTrace (prefixWord ++ tailWord_643661) baseStart_643661 baseEnd_643661 := by
    simpa [prefixWord, tailWord_643661, baseEnd_643661] using wordTrace_append hprefix tailTrace_643661
  have hstable : (prefixWord ++ tailWord_643661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643661).length < 2 ^ (prefixWord ++ tailWord_643661).sum := by decide
  have hdescent : baseEnd_643661 < baseStart_643661 := by decide
  rcases family_descends (prefixWord ++ tailWord_643661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643678 : List Nat := [4, 4, 1, 2, 9]
def baseStart_643678 : Nat := 118140960795 + 643678 * 2 ^ 59
def prefixEnd_643678 : Nat := 4983230072969 + 3 ^ 40 * 643678 * 2
def baseEnd_643678 : Nat := 3627063931136766425951

theorem tailTrace_643678 : CollatzResearch.WordTrace tailWord_643678 prefixEnd_643678 3627063931136766425951 := by
  unfold tailWord_643678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934608170259001536927461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15651243574714674863613125 2934608170259001536927461)
  ·
    refine ⟨550239031923562788173899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2934608170259001536927461 550239031923562788173899)
    ·
      refine ⟨825358547885344182260849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550239031923562788173899 825358547885344182260849)
      ·
        refine ⟨619018910914008136695637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825358547885344182260849 619018910914008136695637)
        ·
          refine ⟨3627063931136766425951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 619018910914008136695637 3627063931136766425951)
          ·
            rfl

theorem cell20_643678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 9].length) (baseStart_643678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643678 prefixEnd_643678 := by exact prefixLift 643678
  have htrace : WordTrace (prefixWord ++ tailWord_643678) baseStart_643678 baseEnd_643678 := by
    simpa [prefixWord, tailWord_643678, baseEnd_643678] using wordTrace_append hprefix tailTrace_643678
  have hstable : (prefixWord ++ tailWord_643678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643678).length < 2 ^ (prefixWord ++ tailWord_643678).sum := by decide
  have hdescent : baseEnd_643678 < baseStart_643678 := by decide
  rcases family_descends (prefixWord ++ tailWord_643678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643685 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_643685 : Nat := 118140960795 + 643685 * 2 ^ 59
def prefixEnd_643685 : Nat := 4983230072969 + 3 ^ 40 * 643685 * 2
def baseEnd_643685 : Nat := 293795373412817167268669

theorem tailTrace_643685 : CollatzResearch.WordTrace tailWord_643685 prefixEnd_643685 293795373412817167268669 := by
  unfold tailWord_643685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23477120673046652490924509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15651413782031101660616339 23477120673046652490924509)
  ·
    refine ⟨8803920252392494684096691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23477120673046652490924509 8803920252392494684096691)
    ·
      refine ⟨13205880378588742026145037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803920252392494684096691 13205880378588742026145037)
      ·
        refine ⟨4952205141970778259804389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13205880378588742026145037 4952205141970778259804389)
        ·
          refine ⟨928538464119520923713323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4952205141970778259804389 928538464119520923713323)
          ·
            refine ⟨1392807696179281385569985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928538464119520923713323 1392807696179281385569985)
            ·
              refine ⟨1044605772134461039177489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392807696179281385569985 1044605772134461039177489)
              ·
                refine ⟨783454329100845779383117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044605772134461039177489 783454329100845779383117)
                ·
                  refine ⟨293795373412817167268669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783454329100845779383117 293795373412817167268669)
                  ·
                    rfl

theorem cell20_643685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_643685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643685 prefixEnd_643685 := by exact prefixLift 643685
  have htrace : WordTrace (prefixWord ++ tailWord_643685) baseStart_643685 baseEnd_643685 := by
    simpa [prefixWord, tailWord_643685, baseEnd_643685] using wordTrace_append hprefix tailTrace_643685
  have hstable : (prefixWord ++ tailWord_643685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643685).length < 2 ^ (prefixWord ++ tailWord_643685).sum := by decide
  have hdescent : baseEnd_643685 < baseStart_643685 := by decide
  rcases family_descends (prefixWord ++ tailWord_643685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643713 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_643713 : Nat := 118140960795 + 643713 * 2 ^ 59
def prefixEnd_643713 : Nat := 4983230072969 + 3 ^ 40 * 643713 * 2
def baseEnd_643713 : Nat := 293808153375773514335221

theorem tailTrace_643713 : CollatzResearch.WordTrace tailWord_643713 prefixEnd_643713 293808153375773514335221 := by
  unfold tailWord_643713
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478141916945213272943793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15652094611296808848629195 23478141916945213272943793)
  ·
    refine ⟨17608606437708909954707845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23478141916945213272943793 17608606437708909954707845)
    ·
      refine ⟨3301613707070420616507721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17608606437708909954707845 3301613707070420616507721)
      ·
        refine ⟨2476210280302815462380791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301613707070420616507721 2476210280302815462380791)
        ·
          refine ⟨3714315420454223193571187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476210280302815462380791 3714315420454223193571187)
          ·
            refine ⟨5571473130681334790356781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714315420454223193571187 5571473130681334790356781)
            ·
              refine ⟨2089302424005500546383793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5571473130681334790356781 2089302424005500546383793)
              ·
                refine ⟨1566976818004125409787845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089302424005500546383793 1566976818004125409787845)
                ·
                  refine ⟨293808153375773514335221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566976818004125409787845 293808153375773514335221)
                  ·
                    rfl

theorem cell20_643713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_643713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643713 prefixEnd_643713 := by exact prefixLift 643713
  have htrace : WordTrace (prefixWord ++ tailWord_643713) baseStart_643713 baseEnd_643713 := by
    simpa [prefixWord, tailWord_643713, baseEnd_643713] using wordTrace_append hprefix tailTrace_643713
  have hstable : (prefixWord ++ tailWord_643713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643713).length < 2 ^ (prefixWord ++ tailWord_643713).sum := by decide
  have hdescent : baseEnd_643713 < baseStart_643713 := by decide
  rcases family_descends (prefixWord ++ tailWord_643713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643744 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_643744 : Nat := 118140960795 + 643744 * 2 ^ 59
def prefixEnd_643744 : Nat := 4983230072969 + 3 ^ 40 * 643744 * 2
def baseEnd_643744 : Nat := 293822302620475184301761

theorem tailTrace_643744 : CollatzResearch.WordTrace tailWord_643744 prefixEnd_643744 293822302620475184301761 := by
  unfold tailWord_643744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739636289916452783661143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15652848386555270378214857 11739636289916452783661143)
  ·
    refine ⟨17609454434874679175491715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11739636289916452783661143 17609454434874679175491715)
    ·
      refine ⟨26414181652312018763237573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17609454434874679175491715 26414181652312018763237573)
      ·
        refine ⟨4952659059808503518107045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26414181652312018763237573 4952659059808503518107045)
        ·
          refine ⟨928623573714094409645071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4952659059808503518107045 928623573714094409645071)
          ·
            refine ⟨1392935360571141614467607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928623573714094409645071 1392935360571141614467607)
            ·
              refine ⟨2089403040856712421701411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392935360571141614467607 2089403040856712421701411)
              ·
                refine ⟨3134104561285068632552117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089403040856712421701411 3134104561285068632552117)
                ·
                  refine ⟨293822302620475184301761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3134104561285068632552117 293822302620475184301761)
                  ·
                    rfl

theorem cell20_643744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_643744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643744 prefixEnd_643744 := by exact prefixLift 643744
  have htrace : WordTrace (prefixWord ++ tailWord_643744) baseStart_643744 baseEnd_643744 := by
    simpa [prefixWord, tailWord_643744, baseEnd_643744] using wordTrace_append hprefix tailTrace_643744
  have hstable : (prefixWord ++ tailWord_643744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643744).length < 2 ^ (prefixWord ++ tailWord_643744).sum := by decide
  have hdescent : baseEnd_643744 < baseStart_643744 := by decide
  rcases family_descends (prefixWord ++ tailWord_643744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643775 : List Nat := [1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_643775 : Nat := 118140960795 + 643775 * 2 ^ 59
def prefixEnd_643775 : Nat := 4983230072969 + 3 ^ 40 * 643775 * 2
def baseEnd_643775 : Nat := 97945483955058951422767

theorem tailTrace_643775 : CollatzResearch.WordTrace tailWord_643775 prefixEnd_643775 97945483955058951422767 := by
  unfold tailWord_643775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23480403242720597861700779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15653602161813731907800519 23480403242720597861700779)
  ·
    refine ⟨35220604864080896792551169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23480403242720597861700779 35220604864080896792551169)
    ·
      refine ⟨26415453648060672594413377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35220604864080896792551169 26415453648060672594413377)
      ·
        refine ⟨19811590236045504445810033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26415453648060672594413377 19811590236045504445810033)
        ·
          refine ⟨14858692677034128334357525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19811590236045504445810033 14858692677034128334357525)
          ·
            refine ⟨696501219235974765673009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14858692677034128334357525 696501219235974765673009)
            ·
              refine ⟨522375914426981074254757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696501219235974765673009 522375914426981074254757)
              ·
                refine ⟨97945483955058951422767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522375914426981074254757 97945483955058951422767)
                ·
                  rfl

theorem cell20_643775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_643775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643775 prefixEnd_643775 := by exact prefixLift 643775
  have htrace : WordTrace (prefixWord ++ tailWord_643775) baseStart_643775 baseEnd_643775 := by
    simpa [prefixWord, tailWord_643775, baseEnd_643775] using wordTrace_append hprefix tailTrace_643775
  have hstable : (prefixWord ++ tailWord_643775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643775).length < 2 ^ (prefixWord ++ tailWord_643775).sum := by decide
  have hdescent : baseEnd_643775 < baseStart_643775 := by decide
  rcases family_descends (prefixWord ++ tailWord_643775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643816 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_643816 : Nat := 118140960795 + 643816 * 2 ^ 59
def prefixEnd_643816 : Nat := 4983230072969 + 3 ^ 40 * 643816 * 2
def baseEnd_643816 : Nat := 293855165382362933901467

theorem tailTrace_643816 : CollatzResearch.WordTrace tailWord_643816 prefixEnd_643816 293855165382362933901467 := by
  unfold tailWord_643816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740949317786030931971651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15654599090381374575962201 11740949317786030931971651)
  ·
    refine ⟨17611423976679046397957477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11740949317786030931971651 17611423976679046397957477)
    ·
      refine ⟨3302141995627321199617027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17611423976679046397957477 3302141995627321199617027)
      ·
        refine ⟨4953212993440981799425541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302141995627321199617027 4953212993440981799425541)
        ·
          refine ⟨928727436270184087392289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4953212993440981799425541 928727436270184087392289)
          ·
            refine ⟨696545577202638065544217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928727436270184087392289 696545577202638065544217)
            ·
              refine ⟨522409182901978549158163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696545577202638065544217 522409182901978549158163)
              ·
                refine ⟨783613774352967823737245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522409182901978549158163 783613774352967823737245)
                ·
                  refine ⟨293855165382362933901467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783613774352967823737245 293855165382362933901467)
                  ·
                    rfl

theorem cell20_643816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_643816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643816 prefixEnd_643816 := by exact prefixLift 643816
  have htrace : WordTrace (prefixWord ++ tailWord_643816) baseStart_643816 baseEnd_643816 := by
    simpa [prefixWord, tailWord_643816, baseEnd_643816] using wordTrace_append hprefix tailTrace_643816
  have hstable : (prefixWord ++ tailWord_643816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643816).length < 2 ^ (prefixWord ++ tailWord_643816).sum := by decide
  have hdescent : baseEnd_643816 < baseStart_643816 := by decide
  rcases family_descends (prefixWord ++ tailWord_643816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643817 : List Nat := [1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_643817 : Nat := 118140960795 + 643817 * 2 ^ 59
def prefixEnd_643817 : Nat := 4983230072969 + 3 ^ 40 * 643817 * 2
def baseEnd_643817 : Nat := 97951873936537124956043

theorem tailTrace_643817 : CollatzResearch.WordTrace tailWord_643817 prefixEnd_643817 97951873936537124956043 := by
  unfold tailWord_643817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23481935108568439034729705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15654623405712292689819803 23481935108568439034729705)
  ·
    refine ⟨17611451331426329276047279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23481935108568439034729705 17611451331426329276047279)
    ·
      refine ⟨26417176997139493914070919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17611451331426329276047279 26417176997139493914070919)
      ·
        refine ⟨39625765495709240871106379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26417176997139493914070919 39625765495709240871106379)
        ·
          refine ⟨59438648243563861306659569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39625765495709240871106379 59438648243563861306659569)
          ·
            refine ⟨44578986182672895979994677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59438648243563861306659569 44578986182672895979994677)
            ·
              refine ⟨4179279954625583998124501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44578986182672895979994677 4179279954625583998124501)
              ·
                refine ⟨97951873936537124956043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4179279954625583998124501 97951873936537124956043)
                ·
                  rfl

theorem cell20_643817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_643817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643817 prefixEnd_643817 := by exact prefixLift 643817
  have htrace : WordTrace (prefixWord ++ tailWord_643817) baseStart_643817 baseEnd_643817 := by
    simpa [prefixWord, tailWord_643817, baseEnd_643817] using wordTrace_append hprefix tailTrace_643817
  have hstable : (prefixWord ++ tailWord_643817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643817).length < 2 ^ (prefixWord ++ tailWord_643817).sum := by decide
  have hdescent : baseEnd_643817 < baseStart_643817 := by decide
  rcases family_descends (prefixWord ++ tailWord_643817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643844 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_643844 : Nat := 118140960795 + 643844 * 2 ^ 59
def prefixEnd_643844 : Nat := 4983230072969 + 3 ^ 40 * 643844 * 2
def baseEnd_643844 : Nat := 293867945345319280968019

theorem tailTrace_643844 : CollatzResearch.WordTrace tailWord_643844 prefixEnd_643844 293867945345319280968019 := by
  unfold tailWord_643844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741459939735311322981293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15655279919647081763975057 11741459939735311322981293)
  ·
    refine ⟨4403047477400741746117985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11741459939735311322981293 4403047477400741746117985)
    ·
      refine ⟨3302285608050556309588489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4403047477400741746117985 3302285608050556309588489)
      ·
        refine ⟨2476714206037917232191367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302285608050556309588489 2476714206037917232191367)
        ·
          refine ⟨3715071309056875848287051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476714206037917232191367 3715071309056875848287051)
          ·
            refine ⟨5572606963585313772430577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715071309056875848287051 5572606963585313772430577)
            ·
              refine ⟨4179455222688985329322933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572606963585313772430577 4179455222688985329322933)
              ·
                refine ⟨391823927127092374624025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4179455222688985329322933 391823927127092374624025)
                ·
                  refine ⟨293867945345319280968019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391823927127092374624025 293867945345319280968019)
                  ·
                    rfl

theorem cell20_643844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_643844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643844 prefixEnd_643844 := by exact prefixLift 643844
  have htrace : WordTrace (prefixWord ++ tailWord_643844) baseStart_643844 baseEnd_643844 := by
    simpa [prefixWord, tailWord_643844, baseEnd_643844] using wordTrace_append hprefix tailTrace_643844
  have hstable : (prefixWord ++ tailWord_643844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643844).length < 2 ^ (prefixWord ++ tailWord_643844).sum := by decide
  have hdescent : baseEnd_643844 < baseStart_643844 := by decide
  rcases family_descends (prefixWord ++ tailWord_643844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643872 : List Nat := [2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_643872 : Nat := 118140960795 + 643872 * 2 ^ 59
def prefixEnd_643872 : Nat := 4983230072969 + 3 ^ 40 * 643872 * 2
def baseEnd_643872 : Nat := 97960241769425209344857

theorem tailTrace_643872 : CollatzResearch.WordTrace tailWord_643872 prefixEnd_643872 97960241769425209344857 := by
  unfold tailWord_643872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741970561684591713990935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15655960748912788951987913 11741970561684591713990935)
  ·
    refine ⟨17612955842526887570986403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11741970561684591713990935 17612955842526887570986403)
    ·
      refine ⟨26419433763790331356479605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17612955842526887570986403 26419433763790331356479605)
      ·
        refine ⟨2476821915355343564669963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26419433763790331356479605 2476821915355343564669963)
        ·
          refine ⟨3715232873033015347004945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476821915355343564669963 3715232873033015347004945)
          ·
            refine ⟨2786424654774761510253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3715232873033015347004945 2786424654774761510253709)
            ·
              refine ⟨1044909245540535566345141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2786424654774761510253709 1044909245540535566345141)
              ·
                refine ⟨97960241769425209344857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044909245540535566345141 97960241769425209344857)
                ·
                  rfl

theorem cell20_643872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_643872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643872 prefixEnd_643872 := by exact prefixLift 643872
  have htrace : WordTrace (prefixWord ++ tailWord_643872) baseStart_643872 baseEnd_643872 := by
    simpa [prefixWord, tailWord_643872, baseEnd_643872] using wordTrace_append hprefix tailTrace_643872
  have hstable : (prefixWord ++ tailWord_643872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643872).length < 2 ^ (prefixWord ++ tailWord_643872).sum := by decide
  have hdescent : baseEnd_643872 < baseStart_643872 := by decide
  rcases family_descends (prefixWord ++ tailWord_643872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643885 : List Nat := [1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_643885 : Nat := 118140960795 + 643885 * 2 ^ 59
def prefixEnd_643885 : Nat := 4983230072969 + 3 ^ 40 * 643885 * 2
def baseEnd_643885 : Nat := 97962219620835120200395

theorem tailTrace_643885 : CollatzResearch.WordTrace tailWord_643885 prefixEnd_643885 97962219620835120200395 := by
  unfold tailWord_643885
  simp only [CollatzResearch.WordTrace]
  refine ⟨23484415272322086648205109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15656276848214724432136739 23484415272322086648205109)
  ·
    refine ⟨2201663931780195623269229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23484415272322086648205109 2201663931780195623269229)
    ·
      refine ⟨825623974417573358725961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2201663931780195623269229 825623974417573358725961)
      ·
        refine ⟨619217980813180019044471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825623974417573358725961 619217980813180019044471)
        ·
          refine ⟨928826971219770028566707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619217980813180019044471 928826971219770028566707)
          ·
            refine ⟨1393240456829655042850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928826971219770028566707 1393240456829655042850061)
            ·
              refine ⟨522465171311120641068773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393240456829655042850061 522465171311120641068773)
              ·
                refine ⟨97962219620835120200395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522465171311120641068773 97962219620835120200395)
                ·
                  rfl

theorem cell20_643885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_643885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643885 prefixEnd_643885 := by exact prefixLift 643885
  have htrace : WordTrace (prefixWord ++ tailWord_643885) baseStart_643885 baseEnd_643885 := by
    simpa [prefixWord, tailWord_643885, baseEnd_643885] using wordTrace_append hprefix tailTrace_643885
  have hstable : (prefixWord ++ tailWord_643885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643885).length < 2 ^ (prefixWord ++ tailWord_643885).sum := by decide
  have hdescent : baseEnd_643885 < baseStart_643885 := by decide
  rcases family_descends (prefixWord ++ tailWord_643885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643975 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 2]
def baseStart_643975 : Nat := 118140960795 + 643975 * 2 ^ 59
def prefixEnd_643975 : Nat := 4983230072969 + 3 ^ 40 * 643975 * 2
def baseEnd_643975 : Nat := 293927737314865047600817

theorem tailTrace_643975 : CollatzResearch.WordTrace tailWord_643975 prefixEnd_643975 293927737314865047600817 := by
  unfold tailWord_643975
  simp only [CollatzResearch.WordTrace]
  refine ⟨23487697841996032018981379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15658465227997354679320919 23487697841996032018981379)
  ·
    refine ⟨35231546762994048028472069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23487697841996032018981379 35231546762994048028472069)
    ·
      refine ⟨6605915018061384005338513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35231546762994048028472069 6605915018061384005338513)
      ·
        refine ⟨4954436263546038004003885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605915018061384005338513 4954436263546038004003885)
        ·
          refine ⟨1857913598829764251501457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4954436263546038004003885 1857913598829764251501457)
          ·
            refine ⟨1393435199122323188626093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857913598829764251501457 1393435199122323188626093)
            ·
              refine ⟨522538199670871195734785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393435199122323188626093 522538199670871195734785)
              ·
                refine ⟨391903649753153396801089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522538199670871195734785 391903649753153396801089)
                ·
                  refine ⟨293927737314865047600817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391903649753153396801089 293927737314865047600817)
                  ·
                    rfl

theorem cell20_643975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2].length) (baseStart_643975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643975 prefixEnd_643975 := by exact prefixLift 643975
  have htrace : WordTrace (prefixWord ++ tailWord_643975) baseStart_643975 baseEnd_643975 := by
    simpa [prefixWord, tailWord_643975, baseEnd_643975] using wordTrace_append hprefix tailTrace_643975
  have hstable : (prefixWord ++ tailWord_643975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643975).length < 2 ^ (prefixWord ++ tailWord_643975).sum := by decide
  have hdescent : baseEnd_643975 < baseStart_643975 := by decide
  rcases family_descends (prefixWord ++ tailWord_643975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643979 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 2]
def baseStart_643979 : Nat := 118140960795 + 643979 * 2 ^ 59
def prefixEnd_643979 : Nat := 4983230072969 + 3 ^ 40 * 643979 * 2
def baseEnd_643979 : Nat := 293929563023858811467467

theorem tailTrace_643979 : CollatzResearch.WordTrace tailWord_643979 prefixEnd_643979 293929563023858811467467 := by
  unfold tailWord_643979
  simp only [CollatzResearch.WordTrace]
  refine ⟨23487843733981540702126991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15658562489321027134751327 23487843733981540702126991)
  ·
    refine ⟨35231765600972311053190487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23487843733981540702126991 35231765600972311053190487)
    ·
      refine ⟨52847648401458466579785731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35231765600972311053190487 52847648401458466579785731)
      ·
        refine ⟨79271472602187699869678597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52847648401458466579785731 79271472602187699869678597)
        ·
          refine ⟨14863401112910193725564737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79271472602187699869678597 14863401112910193725564737)
          ·
            refine ⟨11147550834682645294173553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14863401112910193725564737 11147550834682645294173553)
            ·
              refine ⟨8360663126011983970630165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11147550834682645294173553 8360663126011983970630165)
              ·
                refine ⟨391906084031811748623289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8360663126011983970630165 391906084031811748623289)
                ·
                  refine ⟨293929563023858811467467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391906084031811748623289 293929563023858811467467)
                  ·
                    rfl

theorem cell20_643979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2].length) (baseStart_643979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643979 prefixEnd_643979 := by exact prefixLift 643979
  have htrace : WordTrace (prefixWord ++ tailWord_643979) baseStart_643979 baseEnd_643979 := by
    simpa [prefixWord, tailWord_643979, baseEnd_643979] using wordTrace_append hprefix tailTrace_643979
  have hstable : (prefixWord ++ tailWord_643979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643979).length < 2 ^ (prefixWord ++ tailWord_643979).sum := by decide
  have hdescent : baseEnd_643979 < baseStart_643979 := by decide
  rcases family_descends (prefixWord ++ tailWord_643979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643989 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_643989 : Nat := 118140960795 + 643989 * 2 ^ 59
def prefixEnd_643989 : Nat := 4983230072969 + 3 ^ 40 * 643989 * 2
def baseEnd_643989 : Nat := 293934127296343221134093

theorem tailTrace_643989 : CollatzResearch.WordTrace tailWord_643989 prefixEnd_643989 293934127296343221134093 := by
  unfold tailWord_643989
  simp only [CollatzResearch.WordTrace]
  refine ⟨23488208463945312409991021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15658805642630208273327347 23488208463945312409991021)
  ·
    refine ⟨8808078173979492153746633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23488208463945312409991021 8808078173979492153746633)
    ·
      refine ⟨6606058630484619115309975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8808078173979492153746633 6606058630484619115309975)
      ·
        refine ⟨9909087945726928672964963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606058630484619115309975 9909087945726928672964963)
        ·
          refine ⟨14863631918590393009447445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909087945726928672964963 14863631918590393009447445)
          ·
            refine ⟨696732746183924672317849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14863631918590393009447445 696732746183924672317849)
            ·
              refine ⟨522549559637943504238387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696732746183924672317849 522549559637943504238387)
              ·
                refine ⟨783824339456915256357581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522549559637943504238387 783824339456915256357581)
                ·
                  refine ⟨293934127296343221134093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783824339456915256357581 293934127296343221134093)
                  ·
                    rfl

theorem cell20_643989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_643989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_643989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_643989 prefixEnd_643989 := by exact prefixLift 643989
  have htrace : WordTrace (prefixWord ++ tailWord_643989) baseStart_643989 baseEnd_643989 := by
    simpa [prefixWord, tailWord_643989, baseEnd_643989] using wordTrace_append hprefix tailTrace_643989
  have hstable : (prefixWord ++ tailWord_643989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643989).length < 2 ^ (prefixWord ++ tailWord_643989).sum := by decide
  have hdescent : baseEnd_643989 < baseStart_643989 := by decide
  rcases family_descends (prefixWord ++ tailWord_643989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644000 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_644000 : Nat := 118140960795 + 644000 * 2 ^ 59
def prefixEnd_644000 : Nat := 4983230072969 + 3 ^ 40 * 644000 * 2
def baseEnd_644000 : Nat := 293939147996076071767381

theorem tailTrace_644000 : CollatzResearch.WordTrace tailWord_644000 prefixEnd_644000 293939147996076071767381 := by
  unfold tailWord_644000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744304833452730644320727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15659073111270307525760969 11744304833452730644320727)
  ·
    refine ⟨17616457250179095966481091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11744304833452730644320727 17616457250179095966481091)
    ·
      refine ⟨26424685875268643949721637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17616457250179095966481091 26424685875268643949721637)
      ·
        refine ⟨4954628601612870740572807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26424685875268643949721637 4954628601612870740572807)
        ·
          refine ⟨7431942902419306110859211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954628601612870740572807 7431942902419306110859211)
          ·
            refine ⟨11147914353628959166288817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431942902419306110859211 11147914353628959166288817)
            ·
              refine ⟨8360935765221719374716613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11147914353628959166288817 8360935765221719374716613)
              ·
                refine ⟨1567675455979072382759365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8360935765221719374716613 1567675455979072382759365)
                ·
                  refine ⟨293939147996076071767381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1567675455979072382759365 293939147996076071767381)
                  ·
                    rfl

theorem cell20_644000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_644000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644000 prefixEnd_644000 := by exact prefixLift 644000
  have htrace : WordTrace (prefixWord ++ tailWord_644000) baseStart_644000 baseEnd_644000 := by
    simpa [prefixWord, tailWord_644000, baseEnd_644000] using wordTrace_append hprefix tailTrace_644000
  have hstable : (prefixWord ++ tailWord_644000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644000).length < 2 ^ (prefixWord ++ tailWord_644000).sum := by decide
  have hdescent : baseEnd_644000 < baseStart_644000 := by decide
  rcases family_descends (prefixWord ++ tailWord_644000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644082 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_644082 : Nat := 118140960795 + 644082 * 2 ^ 59
def prefixEnd_644082 : Nat := 4983230072969 + 3 ^ 40 * 644082 * 2
def baseEnd_644082 : Nat := 293976575030448231033713

theorem tailTrace_644082 : CollatzResearch.WordTrace tailWord_644082 prefixEnd_644082 293976575030448231033713 := by
  unfold tailWord_644082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872900113152097323281625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15661066968405592862084333 5872900113152097323281625)
  ·
    refine ⟨4404675084864072992461219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872900113152097323281625 4404675084864072992461219)
    ·
      refine ⟨6607012627296109488691829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404675084864072992461219 6607012627296109488691829)
      ·
        refine ⟨619407433809010264564859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6607012627296109488691829 619407433809010264564859)
        ·
          refine ⟨929111150713515396847289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619407433809010264564859 929111150713515396847289)
          ·
            refine ⟨696833363035136547635467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929111150713515396847289 696833363035136547635467)
            ·
              refine ⟨1045250044552704821453201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696833363035136547635467 1045250044552704821453201)
              ·
                refine ⟨783937533414528616089901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045250044552704821453201 783937533414528616089901)
                ·
                  refine ⟨293976575030448231033713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783937533414528616089901 293976575030448231033713)
                  ·
                    rfl

theorem cell20_644082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_644082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644082 prefixEnd_644082 := by exact prefixLift 644082
  have htrace : WordTrace (prefixWord ++ tailWord_644082) baseStart_644082 baseEnd_644082 := by
    simpa [prefixWord, tailWord_644082, baseEnd_644082] using wordTrace_append hprefix tailTrace_644082
  have hstable : (prefixWord ++ tailWord_644082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644082).length < 2 ^ (prefixWord ++ tailWord_644082).sum := by decide
  have hdescent : baseEnd_644082 < baseStart_644082 := by decide
  rcases family_descends (prefixWord ++ tailWord_644082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644086 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_644086 : Nat := 118140960795 + 644086 * 2 ^ 59
def prefixEnd_644086 : Nat := 4983230072969 + 3 ^ 40 * 644086 * 2
def baseEnd_644086 : Nat := 293978400739441994900363

theorem tailTrace_644086 : CollatzResearch.WordTrace tailWord_644086 prefixEnd_644086 293978400739441994900363 := by
  unfold tailWord_644086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468234146537118623517007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15661164229729265317514741 1468234146537118623517007)
  ·
    refine ⟨2202351219805677935275511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468234146537118623517007 2202351219805677935275511)
    ·
      refine ⟨3303526829708516902913267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202351219805677935275511 3303526829708516902913267)
      ·
        refine ⟨4955290244562775354369901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303526829708516902913267 4955290244562775354369901)
        ·
          refine ⟨1858233841711040757888713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4955290244562775354369901 1858233841711040757888713)
          ·
            refine ⟨1393675381283280568416535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858233841711040757888713 1393675381283280568416535)
            ·
              refine ⟨2090513071924920852624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393675381283280568416535 2090513071924920852624803)
              ·
                refine ⟨3135769607887381278937205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090513071924920852624803 3135769607887381278937205)
                ·
                  refine ⟨293978400739441994900363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135769607887381278937205 293978400739441994900363)
                  ·
                    rfl

theorem cell20_644086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_644086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644086 prefixEnd_644086 := by exact prefixLift 644086
  have htrace : WordTrace (prefixWord ++ tailWord_644086) baseStart_644086 baseEnd_644086 := by
    simpa [prefixWord, tailWord_644086, baseEnd_644086] using wordTrace_append hprefix tailTrace_644086
  have hstable : (prefixWord ++ tailWord_644086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644086).length < 2 ^ (prefixWord ++ tailWord_644086).sum := by decide
  have hdescent : baseEnd_644086 < baseStart_644086 := by decide
  rcases family_descends (prefixWord ++ tailWord_644086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644117 : List Nat := [1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_644117 : Nat := 118140960795 + 644117 * 2 ^ 59
def prefixEnd_644117 : Nat := 4983230072969 + 3 ^ 40 * 644117 * 2
def baseEnd_644117 : Nat := 97997516661381221622301

theorem tailTrace_644117 : CollatzResearch.WordTrace tailWord_644117 prefixEnd_644117 97997516661381221622301 := by
  unfold tailWord_644117
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492877007481590270650605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15661918004987726847100403 23492877007481590270650605)
  ·
    refine ⟨8809828877805596351493977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23492877007481590270650605 8809828877805596351493977)
    ·
      refine ⟨6607371658354197263620483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809828877805596351493977 6607371658354197263620483)
      ·
        refine ⟨9911057487531295895430725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607371658354197263620483 9911057487531295895430725)
        ·
          refine ⟨1858323278912117980393261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9911057487531295895430725 1858323278912117980393261)
          ·
            refine ⟨696871229592044242647473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858323278912117980393261 696871229592044242647473)
            ·
              refine ⟨522653422194033181985605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696871229592044242647473 522653422194033181985605)
              ·
                refine ⟨97997516661381221622301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522653422194033181985605 97997516661381221622301)
                ·
                  rfl

theorem cell20_644117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_644117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644117 prefixEnd_644117 := by exact prefixLift 644117
  have htrace : WordTrace (prefixWord ++ tailWord_644117) baseStart_644117 baseEnd_644117 := by
    simpa [prefixWord, tailWord_644117, baseEnd_644117] using wordTrace_append hprefix tailTrace_644117
  have hstable : (prefixWord ++ tailWord_644117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644117).length < 2 ^ (prefixWord ++ tailWord_644117).sum := by decide
  have hdescent : baseEnd_644117 < baseStart_644117 := by decide
  rcases family_descends (prefixWord ++ tailWord_644117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644145 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_644145 : Nat := 118140960795 + 644145 * 2 ^ 59
def prefixEnd_644145 : Nat := 4983230072969 + 3 ^ 40 * 644145 * 2
def baseEnd_644145 : Nat := 294005329947100011933455

theorem tailTrace_644145 : CollatzResearch.WordTrace tailWord_644145 prefixEnd_644145 294005329947100011933455 := by
  unfold tailWord_644145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23493898251380151052669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15662598834253434035113259 23493898251380151052669889)
  ·
    refine ⟨17620423688535113289502417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23493898251380151052669889 17620423688535113289502417)
    ·
      refine ⟨13215317766401334967126813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17620423688535113289502417 13215317766401334967126813)
      ·
        refine ⟨4955744162400500612672555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13215317766401334967126813 4955744162400500612672555)
        ·
          refine ⟨7433616243600750919008833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955744162400500612672555 7433616243600750919008833)
          ·
            refine ⟨5575212182700563189256625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7433616243600750919008833 5575212182700563189256625)
            ·
              refine ⟨4181409137025422391942469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575212182700563189256625 4181409137025422391942469)
              ·
                refine ⟨784014213192266698489213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4181409137025422391942469 784014213192266698489213)
                ·
                  refine ⟨294005329947100011933455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784014213192266698489213 294005329947100011933455)
                  ·
                    rfl

theorem cell20_644145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_644145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644145 prefixEnd_644145 := by exact prefixLift 644145
  have htrace : WordTrace (prefixWord ++ tailWord_644145) baseStart_644145 baseEnd_644145 := by
    simpa [prefixWord, tailWord_644145, baseEnd_644145] using wordTrace_append hprefix tailTrace_644145
  have hstable : (prefixWord ++ tailWord_644145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644145).length < 2 ^ (prefixWord ++ tailWord_644145).sum := by decide
  have hdescent : baseEnd_644145 < baseStart_644145 := by decide
  rcases family_descends (prefixWord ++ tailWord_644145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644148 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_644148 : Nat := 118140960795 + 644148 * 2 ^ 59
def prefixEnd_644148 : Nat := 4983230072969 + 3 ^ 40 * 644148 * 2
def baseEnd_644148 : Nat := 294006699228845334833443

theorem tailTrace_644148 : CollatzResearch.WordTrace tailWord_644148 prefixEnd_644148 294006699228845334833443 := by
  unfold tailWord_644148
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747003835184641282514549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15662671780246188376686065 11747003835184641282514549)
  ·
    refine ⟨1101281609548560120235739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11747003835184641282514549 1101281609548560120235739)
    ·
      refine ⟨1651922414322840180353609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101281609548560120235739 1651922414322840180353609)
      ·
        refine ⟨1238941810742130135265207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1651922414322840180353609 1238941810742130135265207)
        ·
          refine ⟨1858412716113195202897811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238941810742130135265207 1858412716113195202897811)
          ·
            refine ⟨2787619074169792804346717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858412716113195202897811 2787619074169792804346717)
            ·
              refine ⟨1045357152813672301630019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2787619074169792804346717 1045357152813672301630019)
              ·
                refine ⟨1568035729220508452445029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045357152813672301630019 1568035729220508452445029)
                ·
                  refine ⟨294006699228845334833443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568035729220508452445029 294006699228845334833443)
                  ·
                    rfl

theorem cell20_644148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_644148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644148 prefixEnd_644148 := by exact prefixLift 644148
  have htrace : WordTrace (prefixWord ++ tailWord_644148) baseStart_644148 baseEnd_644148 := by
    simpa [prefixWord, tailWord_644148, baseEnd_644148] using wordTrace_append hprefix tailTrace_644148
  have hstable : (prefixWord ++ tailWord_644148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644148).length < 2 ^ (prefixWord ++ tailWord_644148).sum := by decide
  have hdescent : baseEnd_644148 < baseStart_644148 := by decide
  rcases family_descends (prefixWord ++ tailWord_644148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644158 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_644158 : Nat := 118140960795 + 644158 * 2 ^ 59
def prefixEnd_644158 : Nat := 4983230072969 + 3 ^ 40 * 644158 * 2
def baseEnd_644158 : Nat := 294011263501329744500069

theorem tailTrace_644158 : CollatzResearch.WordTrace tailWord_644158 prefixEnd_644158 294011263501329744500069 := by
  unfold tailWord_644158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936796550041631784111641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15662914933555369515262085 2936796550041631784111641)
  ·
    refine ⟨2202597412531223838083731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2936796550041631784111641 2202597412531223838083731)
    ·
      refine ⟨3303896118796835757125597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202597412531223838083731 3303896118796835757125597)
      ·
        refine ⟨1238961044548813408922099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3303896118796835757125597 1238961044548813408922099)
        ·
          refine ⟨1858441566823220113383149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238961044548813408922099 1858441566823220113383149)
          ·
            refine ⟨696915587558707542518681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858441566823220113383149 696915587558707542518681)
            ·
              refine ⟨522686690669030656889011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696915587558707542518681 522686690669030656889011)
              ·
                refine ⟨784030036003545985333517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522686690669030656889011 784030036003545985333517)
                ·
                  refine ⟨294011263501329744500069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784030036003545985333517 294011263501329744500069)
                  ·
                    rfl

theorem cell20_644158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_644158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644158 prefixEnd_644158 := by exact prefixLift 644158
  have htrace : WordTrace (prefixWord ++ tailWord_644158) baseStart_644158 baseEnd_644158 := by
    simpa [prefixWord, tailWord_644158, baseEnd_644158] using wordTrace_append hprefix tailTrace_644158
  have hstable : (prefixWord ++ tailWord_644158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644158).length < 2 ^ (prefixWord ++ tailWord_644158).sum := by decide
  have hdescent : baseEnd_644158 < baseStart_644158 := by decide
  rcases family_descends (prefixWord ++ tailWord_644158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644207 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 2]
def baseStart_644207 : Nat := 118140960795 + 644207 * 2 ^ 59
def prefixEnd_644207 : Nat := 4983230072969 + 3 ^ 40 * 644207 * 2
def baseEnd_644207 : Nat := 294033628436503351866535

theorem tailTrace_644207 : CollatzResearch.WordTrace tailWord_644207 prefixEnd_644207 294033628436503351866535 := by
  unfold tailWord_644207
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496159577155535641426875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664106384770357094284583 23496159577155535641426875)
  ·
    refine ⟨35244239365733303462140313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23496159577155535641426875 35244239365733303462140313)
    ·
      refine ⟨26433179524299977596605235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35244239365733303462140313 26433179524299977596605235)
      ·
        refine ⟨39649769286449966394907853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26433179524299977596605235 39649769286449966394907853)
        ·
          refine ⟨14868663482418737398090445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39649769286449966394907853 14868663482418737398090445)
          ·
            refine ⟨5575748805907026524283917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14868663482418737398090445 5575748805907026524283917)
            ·
              refine ⟨2090905802215134946606469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5575748805907026524283917 2090905802215134946606469)
              ·
                refine ⟨392044837915337802488713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2090905802215134946606469 392044837915337802488713)
                ·
                  refine ⟨294033628436503351866535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392044837915337802488713 294033628436503351866535)
                  ·
                    rfl

theorem cell20_644207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 2].length) (baseStart_644207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644207 prefixEnd_644207 := by exact prefixLift 644207
  have htrace : WordTrace (prefixWord ++ tailWord_644207) baseStart_644207 baseEnd_644207 := by
    simpa [prefixWord, tailWord_644207, baseEnd_644207] using wordTrace_append hprefix tailTrace_644207
  have hstable : (prefixWord ++ tailWord_644207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644207).length < 2 ^ (prefixWord ++ tailWord_644207).sum := by decide
  have hdescent : baseEnd_644207 < baseStart_644207 := by decide
  rcases family_descends (prefixWord ++ tailWord_644207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_644211 : Nat := 118140960795 + 644211 * 2 ^ 59
def prefixEnd_644211 : Nat := 4983230072969 + 3 ^ 40 * 644211 * 2
def baseEnd_644211 : Nat := 294035454145497115733185

theorem tailTrace_644211 : CollatzResearch.WordTrace tailWord_644211 prefixEnd_644211 294035454145497115733185 := by
  unfold tailWord_644211
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496305469141044324572487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664203646094029549714991 23496305469141044324572487)
  ·
    refine ⟨35244458203711566486858731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23496305469141044324572487 35244458203711566486858731)
    ·
      refine ⟨52866687305567349730288097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35244458203711566486858731 52866687305567349730288097)
      ·
        refine ⟨39650015479175512297716073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52866687305567349730288097 39650015479175512297716073)
        ·
          refine ⟨29737511609381634223287055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39650015479175512297716073 29737511609381634223287055)
          ·
            refine ⟨44606267414072451334930583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29737511609381634223287055 44606267414072451334930583)
            ·
              refine ⟨66909401121108677002395875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44606267414072451334930583 66909401121108677002395875)
              ·
                refine ⟨100364101681663015503593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66909401121108677002395875 100364101681663015503593813)
                ·
                  refine ⟨294035454145497115733185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100364101681663015503593813 294035454145497115733185)
                  ·
                    rfl

theorem cell20_644211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_644211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644211 prefixEnd_644211 := by exact prefixLift 644211
  have htrace : WordTrace (prefixWord ++ tailWord_644211) baseStart_644211 baseEnd_644211 := by
    simpa [prefixWord, tailWord_644211, baseEnd_644211] using wordTrace_append hprefix tailTrace_644211
  have hstable : (prefixWord ++ tailWord_644211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644211).length < 2 ^ (prefixWord ++ tailWord_644211).sum := by decide
  have hdescent : baseEnd_644211 < baseStart_644211 := by decide
  rcases family_descends (prefixWord ++ tailWord_644211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644221 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_644221 : Nat := 118140960795 + 644221 * 2 ^ 59
def prefixEnd_644221 : Nat := 4983230072969 + 3 ^ 40 * 644221 * 2
def baseEnd_644221 : Nat := 294040018417981525399811

theorem tailTrace_644221 : CollatzResearch.WordTrace tailWord_644221 prefixEnd_644221 294040018417981525399811 := by
  unfold tailWord_644221
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496670199104816032436517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15664446799403210688291011 23496670199104816032436517)
  ·
    refine ⟨4405625662332153006081847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23496670199104816032436517 4405625662332153006081847)
    ·
      refine ⟨6608438493498229509122771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405625662332153006081847 6608438493498229509122771)
      ·
        refine ⟨9912657740247344263684157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608438493498229509122771 9912657740247344263684157)
        ·
          refine ⟨3717246652592754098881559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9912657740247344263684157 3717246652592754098881559)
          ·
            refine ⟨5575869978889131148322339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717246652592754098881559 5575869978889131148322339)
            ·
              refine ⟨8363804968333696722483509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575869978889131148322339 8363804968333696722483509)
              ·
                refine ⟨784106715781284067732829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8363804968333696722483509 784106715781284067732829)
                ·
                  refine ⟨294040018417981525399811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784106715781284067732829 294040018417981525399811)
                  ·
                    rfl

theorem cell20_644221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_644221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644221 prefixEnd_644221 := by exact prefixLift 644221
  have htrace : WordTrace (prefixWord ++ tailWord_644221) baseStart_644221 baseEnd_644221 := by
    simpa [prefixWord, tailWord_644221, baseEnd_644221] using wordTrace_append hprefix tailTrace_644221
  have hstable : (prefixWord ++ tailWord_644221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644221).length < 2 ^ (prefixWord ++ tailWord_644221).sum := by decide
  have hdescent : baseEnd_644221 < baseStart_644221 := by decide
  rcases family_descends (prefixWord ++ tailWord_644221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644228 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_644228 : Nat := 118140960795 + 644228 * 2 ^ 59
def prefixEnd_644228 : Nat := 4983230072969 + 3 ^ 40 * 644228 * 2
def baseEnd_644228 : Nat := 294043213408720612166449

theorem tailTrace_644228 : CollatzResearch.WordTrace tailWord_644228 prefixEnd_644228 294043213408720612166449 := by
  unfold tailWord_644228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748462755039728113970669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15664617006719637485294225 11748462755039728113970669)
  ·
    refine ⟨4405673533139898042739001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11748462755039728113970669 4405673533139898042739001)
    ·
      refine ⟨3304255149854923532054251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405673533139898042739001 3304255149854923532054251)
      ·
        refine ⟨4956382724782385298081377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304255149854923532054251 4956382724782385298081377)
        ·
          refine ⟨3717287043586788973561033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4956382724782385298081377 3717287043586788973561033)
          ·
            refine ⟨2787965282690091730170775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3717287043586788973561033 2787965282690091730170775)
            ·
              refine ⟨4181947924035137595256163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787965282690091730170775 4181947924035137595256163)
              ·
                refine ⟨6272921886052706392884245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181947924035137595256163 6272921886052706392884245)
                ·
                  refine ⟨294043213408720612166449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6272921886052706392884245 294043213408720612166449)
                  ·
                    rfl

theorem cell20_644228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_644228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644228 prefixEnd_644228 := by exact prefixLift 644228
  have htrace : WordTrace (prefixWord ++ tailWord_644228) baseStart_644228 baseEnd_644228 := by
    simpa [prefixWord, tailWord_644228, baseEnd_644228] using wordTrace_append hprefix tailTrace_644228
  have hstable : (prefixWord ++ tailWord_644228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644228).length < 2 ^ (prefixWord ++ tailWord_644228).sum := by decide
  have hdescent : baseEnd_644228 < baseStart_644228 := by decide
  rcases family_descends (prefixWord ++ tailWord_644228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644255 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_644255 : Nat := 118140960795 + 644255 * 2 ^ 59
def prefixEnd_644255 : Nat := 4983230072969 + 3 ^ 40 * 644255 * 2
def baseEnd_644255 : Nat := 294055536944428518266339

theorem tailTrace_644255 : CollatzResearch.WordTrace tailWord_644255 prefixEnd_644255 294055536944428518266339 := by
  unfold tailWord_644255
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497910280981639839174219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15665273520654426559449479 23497910280981639839174219)
  ·
    refine ⟨35246865421472459758761329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23497910280981639839174219 35246865421472459758761329)
    ·
      refine ⟨26435149066104344819070997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35246865421472459758761329 26435149066104344819070997)
      ·
        refine ⟨1239147612473641163393953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26435149066104344819070997 1239147612473641163393953)
        ·
          refine ⟨929360709355230872545465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239147612473641163393953 929360709355230872545465)
          ·
            refine ⟨697020532016423154409099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929360709355230872545465 697020532016423154409099)
            ·
              refine ⟨1045530798024634731613649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697020532016423154409099 1045530798024634731613649)
              ·
                refine ⟨784148098518476048710237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045530798024634731613649 784148098518476048710237)
                ·
                  refine ⟨294055536944428518266339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784148098518476048710237 294055536944428518266339)
                  ·
                    rfl

theorem cell20_644255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_644255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644255 prefixEnd_644255 := by exact prefixLift 644255
  have htrace : WordTrace (prefixWord ++ tailWord_644255) baseStart_644255 baseEnd_644255 := by
    simpa [prefixWord, tailWord_644255, baseEnd_644255] using wordTrace_append hprefix tailTrace_644255
  have hstable : (prefixWord ++ tailWord_644255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644255).length < 2 ^ (prefixWord ++ tailWord_644255).sum := by decide
  have hdescent : baseEnd_644255 < baseStart_644255 := by decide
  rcases family_descends (prefixWord ++ tailWord_644255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644317 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 4]
def baseStart_644317 : Nat := 118140960795 + 644317 * 2 ^ 59
def prefixEnd_644317 : Nat := 4983230072969 + 3 ^ 40 * 644317 * 2
def baseEnd_644317 : Nat := 294083835433831858199419

theorem tailTrace_644317 : CollatzResearch.WordTrace tailWord_644317 prefixEnd_644317 294083835433831858199419 := by
  unfold tailWord_644317
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500171606757024427931205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666781071171349618620803 23500171606757024427931205)
  ·
    refine ⟨4406282176266942080237101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23500171606757024427931205 4406282176266942080237101)
    ·
      refine ⟨1652355816100103280088913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4406282176266942080237101 1652355816100103280088913)
      ·
        refine ⟨1239266862075077460066685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652355816100103280088913 1239266862075077460066685)
        ·
          refine ⟨464725073278154047525007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1239266862075077460066685 464725073278154047525007)
          ·
            refine ⟨697087609917231071287511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464725073278154047525007 697087609917231071287511)
            ·
              refine ⟨1045631414875846606931267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697087609917231071287511 1045631414875846606931267)
              ·
                refine ⟨1568447122313769910396901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045631414875846606931267 1568447122313769910396901)
                ·
                  refine ⟨294083835433831858199419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568447122313769910396901 294083835433831858199419)
                  ·
                    rfl

theorem cell20_644317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_644317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644317 prefixEnd_644317 := by exact prefixLift 644317
  have htrace : WordTrace (prefixWord ++ tailWord_644317) baseStart_644317 baseEnd_644317 := by
    simpa [prefixWord, tailWord_644317, baseEnd_644317] using wordTrace_append hprefix tailTrace_644317
  have hstable : (prefixWord ++ tailWord_644317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644317).length < 2 ^ (prefixWord ++ tailWord_644317).sum := by decide
  have hdescent : baseEnd_644317 < baseStart_644317 := by decide
  rcases family_descends (prefixWord ++ tailWord_644317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644321 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_644321 : Nat := 118140960795 + 644321 * 2 ^ 59
def prefixEnd_644321 : Nat := 4983230072969 + 3 ^ 40 * 644321 * 2
def baseEnd_644321 : Nat := 294085661142825622066069

theorem tailTrace_644321 : CollatzResearch.WordTrace tailWord_644321 prefixEnd_644321 294085661142825622066069 := by
  unfold tailWord_644321
  simp only [CollatzResearch.WordTrace]
  refine ⟨23500317498742533111076817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666878332495022074051211 23500317498742533111076817)
  ·
    refine ⟨17625238124056899833307613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23500317498742533111076817 17625238124056899833307613)
    ·
      refine ⟨6609464296521337437490355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17625238124056899833307613 6609464296521337437490355)
      ·
        refine ⟨9914196444782006156235533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609464296521337437490355 9914196444782006156235533)
        ·
          refine ⟨3717823666793252308588325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9914196444782006156235533 3717823666793252308588325)
          ·
            refine ⟨697091937523734807860311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3717823666793252308588325 697091937523734807860311)
            ·
              refine ⟨1045637906285602211790467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697091937523734807860311 1045637906285602211790467)
              ·
                refine ⟨1568456859428403317685701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045637906285602211790467 1568456859428403317685701)
                ·
                  refine ⟨294085661142825622066069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568456859428403317685701 294085661142825622066069)
                  ·
                    rfl

theorem cell20_644321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_644321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644321 prefixEnd_644321 := by exact prefixLift 644321
  have htrace : WordTrace (prefixWord ++ tailWord_644321) baseStart_644321 baseEnd_644321 := by
    simpa [prefixWord, tailWord_644321, baseEnd_644321] using wordTrace_append hprefix tailTrace_644321
  have hstable : (prefixWord ++ tailWord_644321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644321).length < 2 ^ (prefixWord ++ tailWord_644321).sum := by decide
  have hdescent : baseEnd_644321 < baseStart_644321 := by decide
  rcases family_descends (prefixWord ++ tailWord_644321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644342 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_644342 : Nat := 118140960795 + 644342 * 2 ^ 59
def prefixEnd_644342 : Nat := 4983230072969 + 3 ^ 40 * 644342 * 2
def baseEnd_644342 : Nat := 294095246115042882365983

theorem tailTrace_644342 : CollatzResearch.WordTrace tailWord_644342 prefixEnd_644342 294095246115042882365983 := by
  unfold tailWord_644342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468817714479153356099455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15667388954444302465060853 1468817714479153356099455)
  ·
    refine ⟨2203226571718730034149183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468817714479153356099455 2203226571718730034149183)
    ·
      refine ⟨3304839857578095051223775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203226571718730034149183 3304839857578095051223775)
      ·
        refine ⟨4957259786367142576835663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304839857578095051223775 4957259786367142576835663)
        ·
          refine ⟨7435889679550713865253495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957259786367142576835663 7435889679550713865253495)
          ·
            refine ⟨11153834519326070797880243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435889679550713865253495 11153834519326070797880243)
            ·
              refine ⟨16730751778989106196820365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11153834519326070797880243 16730751778989106196820365)
              ·
                refine ⟨6274031917120914823807637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16730751778989106196820365 6274031917120914823807637)
                ·
                  refine ⟨294095246115042882365983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274031917120914823807637 294095246115042882365983)
                  ·
                    rfl

theorem cell20_644342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_644342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644342 prefixEnd_644342 := by exact prefixLift 644342
  have htrace : WordTrace (prefixWord ++ tailWord_644342) baseStart_644342 baseEnd_644342 := by
    simpa [prefixWord, tailWord_644342, baseEnd_644342] using wordTrace_append hprefix tailTrace_644342
  have hstable : (prefixWord ++ tailWord_644342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644342).length < 2 ^ (prefixWord ++ tailWord_644342).sum := by decide
  have hdescent : baseEnd_644342 < baseStart_644342 := by decide
  rcases family_descends (prefixWord ++ tailWord_644342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644376 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_644376 : Nat := 118140960795 + 644376 * 2 ^ 59
def prefixEnd_644376 : Nat := 4983230072969 + 3 ^ 40 * 644376 * 2
def baseEnd_644376 : Nat := 294110764641489875232511

theorem tailTrace_644376 : CollatzResearch.WordTrace tailWord_644376 prefixEnd_644376 294110764641489875232511 := by
  unfold tailWord_644376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751161756771638752164491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15668215675695518336219321 11751161756771638752164491)
  ·
    refine ⟨17626742635157458128246737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751161756771638752164491 17626742635157458128246737)
    ·
      refine ⟨13220056976368093596185053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17626742635157458128246737 13220056976368093596185053)
      ·
        refine ⟨4957521366138035098569395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13220056976368093596185053 4957521366138035098569395)
        ·
          refine ⟨7436282049207052647854093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957521366138035098569395 7436282049207052647854093)
          ·
            refine ⟨2788605768452644742945285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7436282049207052647854093 2788605768452644742945285)
            ·
              refine ⟨522863581584870889302241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2788605768452644742945285 522863581584870889302241)
              ·
                refine ⟨392147686188653166976681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522863581584870889302241 392147686188653166976681)
                ·
                  refine ⟨294110764641489875232511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392147686188653166976681 294110764641489875232511)
                  ·
                    rfl

theorem cell20_644376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_644376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644376 prefixEnd_644376 := by exact prefixLift 644376
  have htrace : WordTrace (prefixWord ++ tailWord_644376) baseStart_644376 baseEnd_644376 := by
    simpa [prefixWord, tailWord_644376, baseEnd_644376] using wordTrace_append hprefix tailTrace_644376
  have hstable : (prefixWord ++ tailWord_644376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644376).length < 2 ^ (prefixWord ++ tailWord_644376).sum := by decide
  have hdescent : baseEnd_644376 < baseStart_644376 := by decide
  rcases family_descends (prefixWord ++ tailWord_644376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644383 : List Nat := [1, 1, 2, 4, 5, 1, 1, 5]
def baseStart_644383 : Nat := 118140960795 + 644383 * 2 ^ 59
def prefixEnd_644383 : Nat := 4983230072969 + 3 ^ 40 * 644383 * 2
def baseEnd_644383 : Nat := 98037986544076320666383

theorem tailTrace_644383 : CollatzResearch.WordTrace tailWord_644383 prefixEnd_644383 98037986544076320666383 := by
  unfold tailWord_644383
  simp only [CollatzResearch.WordTrace]
  refine ⟨23502578824517917699833803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15668385883011945133222535 23502578824517917699833803)
  ·
    refine ⟨35253868236776876549750705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23502578824517917699833803 35253868236776876549750705)
    ·
      refine ⟨26440401177582657412313029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35253868236776876549750705 26440401177582657412313029)
      ·
        refine ⟨4957575220796748264808693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26440401177582657412313029 4957575220796748264808693)
        ·
          refine ⟨464772676949695149825815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4957575220796748264808693 464772676949695149825815)
          ·
            refine ⟨697159015424542724738723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464772676949695149825815 697159015424542724738723)
            ·
              refine ⟨1045738523136814087108085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697159015424542724738723 1045738523136814087108085)
              ·
                refine ⟨98037986544076320666383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045738523136814087108085 98037986544076320666383)
                ·
                  rfl

theorem cell20_644383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_644383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644383 prefixEnd_644383 := by exact prefixLift 644383
  have htrace : WordTrace (prefixWord ++ tailWord_644383) baseStart_644383 baseEnd_644383 := by
    simpa [prefixWord, tailWord_644383, baseEnd_644383] using wordTrace_append hprefix tailTrace_644383
  have hstable : (prefixWord ++ tailWord_644383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644383).length < 2 ^ (prefixWord ++ tailWord_644383).sum := by decide
  have hdescent : baseEnd_644383 < baseStart_644383 := by decide
  rcases family_descends (prefixWord ++ tailWord_644383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644387 : List Nat := [1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_644387 : Nat := 118140960795 + 644387 * 2 ^ 59
def prefixEnd_644387 : Nat := 4983230072969 + 3 ^ 40 * 644387 * 2
def baseEnd_644387 : Nat := 98038595113740908621933

theorem tailTrace_644387 : CollatzResearch.WordTrace tailWord_644387 prefixEnd_644387 98038595113740908621933 := by
  unfold tailWord_644387
  simp only [CollatzResearch.WordTrace]
  refine ⟨23502724716503426382979415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15668483144335617588652943 23502724716503426382979415)
  ·
    refine ⟨35254087074755139574469123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23502724716503426382979415 35254087074755139574469123)
    ·
      refine ⟨52881130612132709361703685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35254087074755139574469123 52881130612132709361703685)
      ·
        refine ⟨9915211989774883005319441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52881130612132709361703685 9915211989774883005319441)
        ·
          refine ⟨7436408992331162253989581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9915211989774883005319441 7436408992331162253989581)
          ·
            refine ⟨2788653372124185845246093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7436408992331162253989581 2788653372124185845246093)
            ·
              refine ⟨1045745014546569691967285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2788653372124185845246093 1045745014546569691967285)
              ·
                refine ⟨98038595113740908621933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045745014546569691967285 98038595113740908621933)
                ·
                  rfl

theorem cell20_644387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_644387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644387 prefixEnd_644387 := by exact prefixLift 644387
  have htrace : WordTrace (prefixWord ++ tailWord_644387) baseStart_644387 baseEnd_644387 := by
    simpa [prefixWord, tailWord_644387, baseEnd_644387] using wordTrace_append hprefix tailTrace_644387
  have hstable : (prefixWord ++ tailWord_644387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644387).length < 2 ^ (prefixWord ++ tailWord_644387).sum := by decide
  have hdescent : baseEnd_644387 < baseStart_644387 := by decide
  rcases family_descends (prefixWord ++ tailWord_644387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644397 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_644397 : Nat := 118140960795 + 644397 * 2 ^ 59
def prefixEnd_644397 : Nat := 4983230072969 + 3 ^ 40 * 644397 * 2
def baseEnd_644397 : Nat := 294120349613707135532425

theorem tailTrace_644397 : CollatzResearch.WordTrace tailWord_644397 prefixEnd_644397 294120349613707135532425 := by
  unfold tailWord_644397
  simp only [CollatzResearch.WordTrace]
  refine ⟨23503089446467198090843445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15668726297644798727228963 23503089446467198090843445)
  ·
    refine ⟨2203414635606299821016573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23503089446467198090843445 2203414635606299821016573)
    ·
      refine ⟨826280488352362432881215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2203414635606299821016573 826280488352362432881215)
      ·
        refine ⟨1239420732528543649321823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826280488352362432881215 1239420732528543649321823)
        ·
          refine ⟨1859131098792815473982735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239420732528543649321823 1859131098792815473982735)
          ·
            refine ⟨2788696648189223210974103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859131098792815473982735 2788696648189223210974103)
            ·
              refine ⟨4183044972283834816461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788696648189223210974103 4183044972283834816461155)
              ·
                refine ⟨6274567458425752224691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183044972283834816461155 6274567458425752224691733)
                ·
                  refine ⟨294120349613707135532425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274567458425752224691733 294120349613707135532425)
                  ·
                    rfl

theorem cell20_644397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_644397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644397 prefixEnd_644397 := by exact prefixLift 644397
  have htrace : WordTrace (prefixWord ++ tailWord_644397) baseStart_644397 baseEnd_644397 := by
    simpa [prefixWord, tailWord_644397, baseEnd_644397] using wordTrace_append hprefix tailTrace_644397
  have hstable : (prefixWord ++ tailWord_644397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644397).length < 2 ^ (prefixWord ++ tailWord_644397).sum := by decide
  have hdescent : baseEnd_644397 < baseStart_644397 := by decide
  rcases family_descends (prefixWord ++ tailWord_644397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644414 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_644414 : Nat := 118140960795 + 644414 * 2 ^ 59
def prefixEnd_644414 : Nat := 4983230072969 + 3 ^ 40 * 644414 * 2
def baseEnd_644414 : Nat := 294128108876930631965689

theorem tailTrace_644414 : CollatzResearch.WordTrace tailWord_644414 prefixEnd_644414 294128108876930631965689 := by
  unfold tailWord_644414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937963685925701249276537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15669139658270406662808197 2937963685925701249276537)
  ·
    refine ⟨2203472764444275936957403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2937963685925701249276537 2203472764444275936957403)
    ·
      refine ⟨3305209146666413905436105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203472764444275936957403 3305209146666413905436105)
      ·
        refine ⟨2478906859999810429077079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305209146666413905436105 2478906859999810429077079)
        ·
          refine ⟨3718360289999715643615619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478906859999810429077079 3718360289999715643615619)
          ·
            refine ⟨5577540434999573465423429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718360289999715643615619 5577540434999573465423429)
            ·
              refine ⟨1045788831562420024766893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5577540434999573465423429 1045788831562420024766893)
              ·
                refine ⟨392170811835907509287585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045788831562420024766893 392170811835907509287585)
                ·
                  refine ⟨294128108876930631965689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392170811835907509287585 294128108876930631965689)
                  ·
                    rfl

theorem cell20_644414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_644414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644414 prefixEnd_644414 := by exact prefixLift 644414
  have htrace : WordTrace (prefixWord ++ tailWord_644414) baseStart_644414 baseEnd_644414 := by
    simpa [prefixWord, tailWord_644414, baseEnd_644414] using wordTrace_append hprefix tailTrace_644414
  have hstable : (prefixWord ++ tailWord_644414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644414).length < 2 ^ (prefixWord ++ tailWord_644414).sum := by decide
  have hdescent : baseEnd_644414 < baseStart_644414 := by decide
  rcases family_descends (prefixWord ++ tailWord_644414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644428 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_644428 : Nat := 118140960795 + 644428 * 2 ^ 59
def prefixEnd_644428 : Nat := 4983230072969 + 3 ^ 40 * 644428 * 2
def baseEnd_644428 : Nat := 294134498858408805498965

theorem tailTrace_644428 : CollatzResearch.WordTrace tailWord_644428 prefixEnd_644428 294134498858408805498965 := by
  unfold tailWord_644428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752110054677445192610969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15669480072903260256814625 11752110054677445192610969)
  ·
    refine ⟨8814082541008083894458227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11752110054677445192610969 8814082541008083894458227)
    ·
      refine ⟨13221123811512125841687341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8814082541008083894458227 13221123811512125841687341)
      ·
        refine ⟨4957921429317047190632753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13221123811512125841687341 4957921429317047190632753)
        ·
          refine ⟨3718441071987785392974565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4957921429317047190632753 3718441071987785392974565)
          ·
            refine ⟨697207700997709761182731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3718441071987785392974565 697207700997709761182731)
            ·
              refine ⟨1045811551496564641774097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697207700997709761182731 1045811551496564641774097)
              ·
                refine ⟨784358663622423481330573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045811551496564641774097 784358663622423481330573)
                ·
                  refine ⟨294134498858408805498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784358663622423481330573 294134498858408805498965)
                  ·
                    rfl

theorem cell20_644428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_644428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_644428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_644428 prefixEnd_644428 := by exact prefixLift 644428
  have htrace : WordTrace (prefixWord ++ tailWord_644428) baseStart_644428 baseEnd_644428 := by
    simpa [prefixWord, tailWord_644428, baseEnd_644428] using wordTrace_append hprefix tailTrace_644428
  have hstable : (prefixWord ++ tailWord_644428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644428).length < 2 ^ (prefixWord ++ tailWord_644428).sum := by decide
  have hdescent : baseEnd_644428 < baseStart_644428 := by decide
  rcases family_descends (prefixWord ++ tailWord_644428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
