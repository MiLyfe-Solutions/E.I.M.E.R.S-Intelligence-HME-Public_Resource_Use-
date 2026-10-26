import V185TrunkScan22Chunk287

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2568792 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_2568792 : Nat := 118140960795 + 2568792 * 2 ^ 59
def prefixEnd_2568792 : Nat := 4983230072969 + 3 ^ 40 * 2568792 * 2
def baseEnd_2568792 : Nat := 879349998282945882124231

theorem tailTrace_2568792 : CollatzResearch.WordTrace tailWord_2568792 prefixEnd_2568792 879349998282945882124231 := by
  unfold tailWord_2568792
  simp only [CollatzResearch.WordTrace]
  refine ⟨46845770654856386795422315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62461027539808515727229753 46845770654856386795422315)
  ·
    refine ⟨70268655982284580193133473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46845770654856386795422315 70268655982284580193133473)
    ·
      refine ⟨52701491986713435144850105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70268655982284580193133473 52701491986713435144850105)
      ·
        refine ⟨39526118990035076358637579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52701491986713435144850105 39526118990035076358637579)
        ·
          refine ⟨59289178485052614537956369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39526118990035076358637579 59289178485052614537956369)
          ·
            refine ⟨44466883863789460903467277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59289178485052614537956369 44466883863789460903467277)
            ·
              refine ⟨16675081448921047838800229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44466883863789460903467277 16675081448921047838800229)
              ·
                refine ⟨3126577771672696469775043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16675081448921047838800229 3126577771672696469775043)
                ·
                  refine ⟨4689866657509044704662565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126577771672696469775043 4689866657509044704662565)
                  ·
                    refine ⟨879349998282945882124231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689866657509044704662565 879349998282945882124231)
                    ·
                      rfl

theorem cell22_2568792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_2568792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568792 prefixEnd_2568792 := by exact prefixLift 2568792
  have htrace : WordTrace (prefixWord ++ tailWord_2568792) baseStart_2568792 baseEnd_2568792 := by
    simpa [prefixWord, tailWord_2568792, baseEnd_2568792] using wordTrace_append hprefix tailTrace_2568792
  have hstable : (prefixWord ++ tailWord_2568792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568792).length < 2 ^ (prefixWord ++ tailWord_2568792).sum := by decide
  have hdescent : baseEnd_2568792 < baseStart_2568792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568835 : List Nat := [1, 1, 1, 3, 3, 1, 3, 9]
def baseStart_2568835 : Nat := 118140960795 + 2568835 * 2 ^ 59
def prefixEnd_2568835 : Nat := 4983230072969 + 3 ^ 40 * 2568835 * 2
def baseEnd_2568835 : Nat := 97707190895745344811011

theorem tailTrace_2568835 : CollatzResearch.WordTrace tailWord_2568835 prefixEnd_2568835 97707190895745344811011 := by
  unfold tailWord_2568835
  simp only [CollatzResearch.WordTrace]
  refine ⟨93693109648556991934659959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62462073099037994623106639 93693109648556991934659959)
  ·
    refine ⟨140539664472835487901989939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93693109648556991934659959 140539664472835487901989939)
    ·
      refine ⟨210809496709253231852984909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140539664472835487901989939 210809496709253231852984909)
      ·
        refine ⟨79053561265969961944869341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210809496709253231852984909 79053561265969961944869341)
        ·
          refine ⟨29645085474738735729326003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79053561265969961944869341 29645085474738735729326003)
          ·
            refine ⟨44467628212108103593989005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29645085474738735729326003 44467628212108103593989005)
            ·
              refine ⟨16675360579540538847745877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44467628212108103593989005 16675360579540538847745877)
              ·
                refine ⟨97707190895745344811011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16675360579540538847745877 97707190895745344811011)
                ·
                  rfl

theorem cell22_2568835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_2568835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568835 prefixEnd_2568835 := by exact prefixLift 2568835
  have htrace : WordTrace (prefixWord ++ tailWord_2568835) baseStart_2568835 baseEnd_2568835 := by
    simpa [prefixWord, tailWord_2568835, baseEnd_2568835] using wordTrace_append hprefix tailTrace_2568835
  have hstable : (prefixWord ++ tailWord_2568835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568835).length < 2 ^ (prefixWord ++ tailWord_2568835).sum := by decide
  have hdescent : baseEnd_2568835 < baseStart_2568835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568839 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 2, 3]
def baseStart_2568839 : Nat := 118140960795 + 2568839 * 2 ^ 59
def prefixEnd_2568839 : Nat := 4983230072969 + 3 ^ 40 * 2568839 * 2
def baseEnd_2568839 : Nat := 879366087343453426199087

theorem tailTrace_2568839 : CollatzResearch.WordTrace tailWord_2568839 prefixEnd_2568839 879366087343453426199087 := by
  unfold tailWord_2568839
  simp only [CollatzResearch.WordTrace]
  refine ⟨93693255540542500617805571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62462170360361667078537047 93693255540542500617805571)
  ·
    refine ⟨140539883310813750926708357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93693255540542500617805571 140539883310813750926708357)
    ·
      refine ⟨26351228120777578298757817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140539883310813750926708357 26351228120777578298757817)
      ·
        refine ⟨19763421090583183724068363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26351228120777578298757817 19763421090583183724068363)
        ·
          refine ⟨29645131635874775586102545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19763421090583183724068363 29645131635874775586102545)
          ·
            refine ⟨22233848726906081689576909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29645131635874775586102545 22233848726906081689576909)
            ·
              refine ⟨8337693272589780633591341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22233848726906081689576909 8337693272589780633591341)
              ·
                refine ⟨3126634977221167737596753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8337693272589780633591341 3126634977221167737596753)
                ·
                  refine ⟨2344976232915875803197565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126634977221167737596753 2344976232915875803197565)
                  ·
                    refine ⟨879366087343453426199087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344976232915875803197565 879366087343453426199087)
                    ·
                      rfl

theorem cell22_2568839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_2568839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568839 prefixEnd_2568839 := by exact prefixLift 2568839
  have htrace : WordTrace (prefixWord ++ tailWord_2568839) baseStart_2568839 baseEnd_2568839 := by
    simpa [prefixWord, tailWord_2568839, baseEnd_2568839] using wordTrace_append hprefix tailTrace_2568839
  have hstable : (prefixWord ++ tailWord_2568839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568839).length < 2 ^ (prefixWord ++ tailWord_2568839).sum := by decide
  have hdescent : baseEnd_2568839 < baseStart_2568839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568867 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 7, 3]
def baseStart_2568867 : Nat := 118140960795 + 2568867 * 2 ^ 59
def prefixEnd_2568867 : Nat := 4983230072969 + 3 ^ 40 * 2568867 * 2
def baseEnd_2568867 : Nat := 879375672315670686499001

theorem tailTrace_2568867 : CollatzResearch.WordTrace tailWord_2568867 prefixEnd_2568867 879375672315670686499001 := by
  unfold tailWord_2568867
  simp only [CollatzResearch.WordTrace]
  refine ⟨93694276784441061399824855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62462851189627374266549903 93694276784441061399824855)
  ·
    refine ⟨140541415176661592099737283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93694276784441061399824855 140541415176661592099737283)
    ·
      refine ⟨210812122764992388149605925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140541415176661592099737283 210812122764992388149605925)
      ·
        refine ⟨39527273018436072778051111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210812122764992388149605925 39527273018436072778051111)
        ·
          refine ⟨59290909527654109167076667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39527273018436072778051111 59290909527654109167076667)
          ·
            refine ⟨88936364291481163750615001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59290909527654109167076667 88936364291481163750615001)
            ·
              refine ⟨66702273218610872812961251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88936364291481163750615001 66702273218610872812961251)
              ·
                refine ⟨100053409827916309219441877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66702273218610872812961251 100053409827916309219441877)
                ·
                  refine ⟨2345001792841788497330669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 100053409827916309219441877 2345001792841788497330669)
                  ·
                    refine ⟨879375672315670686499001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345001792841788497330669 879375672315670686499001)
                    ·
                      rfl

theorem cell22_2568867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].length) (baseStart_2568867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568867 prefixEnd_2568867 := by exact prefixLift 2568867
  have htrace : WordTrace (prefixWord ++ tailWord_2568867) baseStart_2568867 baseEnd_2568867 := by
    simpa [prefixWord, tailWord_2568867, baseEnd_2568867] using wordTrace_append hprefix tailTrace_2568867
  have hstable : (prefixWord ++ tailWord_2568867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568867).length < 2 ^ (prefixWord ++ tailWord_2568867).sum := by decide
  have hdescent : baseEnd_2568867 < baseStart_2568867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568931 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 5]
def baseStart_2568931 : Nat := 118140960795 + 2568931 * 2 ^ 59
def prefixEnd_2568931 : Nat := 4983230072969 + 3 ^ 40 * 2568931 * 2
def baseEnd_2568931 : Nat := 293132526941198617632935

theorem tailTrace_2568931 : CollatzResearch.WordTrace tailWord_2568931 prefixEnd_2568931 293132526941198617632935 := by
  unfold tailWord_2568931
  simp only [CollatzResearch.WordTrace]
  refine ⟨93696611056209200330154647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62464407370806133553436431 93696611056209200330154647)
  ·
    refine ⟨140544916584313800495231971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93696611056209200330154647 140544916584313800495231971)
    ·
      refine ⟨210817374876470700742847957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140544916584313800495231971 210817374876470700742847957)
      ·
        refine ⟨4941032223667282048660499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 210817374876470700742847957 4941032223667282048660499)
        ·
          refine ⟨7411548335500923072990749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941032223667282048660499 7411548335500923072990749)
          ·
            refine ⟨2779330625812846152371531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7411548335500923072990749 2779330625812846152371531)
            ·
              refine ⟨4168995938719269228557297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779330625812846152371531 4168995938719269228557297)
              ·
                refine ⟨3126746954039451921417973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168995938719269228557297 3126746954039451921417973)
                ·
                  refine ⟨293132526941198617632935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126746954039451921417973 293132526941198617632935)
                  ·
                    rfl

theorem cell22_2568931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].length) (baseStart_2568931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2568931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2568931 prefixEnd_2568931 := by exact prefixLift 2568931
  have htrace : WordTrace (prefixWord ++ tailWord_2568931) baseStart_2568931 baseEnd_2568931 := by
    simpa [prefixWord, tailWord_2568931, baseEnd_2568931] using wordTrace_append hprefix tailTrace_2568931
  have hstable : (prefixWord ++ tailWord_2568931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568931).length < 2 ^ (prefixWord ++ tailWord_2568931).sum := by decide
  have hdescent : baseEnd_2568931 < baseStart_2568931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569049 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 5]
def baseStart_2569049 : Nat := 118140960795 + 2569049 * 2 ^ 59
def prefixEnd_2569049 : Nat := 4983230072969 + 3 ^ 40 * 2569049 * 2
def baseEnd_2569049 : Nat := 293145991545027626149481

theorem tailTrace_2569049 : CollatzResearch.WordTrace tailWord_2569049 prefixEnd_2569049 293145991545027626149481 := by
  unfold tailWord_2569049
  simp only [CollatzResearch.WordTrace]
  refine ⟨93700914869781706482950201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62467276579854470988633467 93700914869781706482950201)
  ·
    refine ⟨70275686152336279862212651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93700914869781706482950201 70275686152336279862212651)
    ·
      refine ⟨105413529228504419793318977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70275686152336279862212651 105413529228504419793318977)
      ·
        refine ⟨79060146921378314844989233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105413529228504419793318977 79060146921378314844989233)
        ·
          refine ⟨59295110191033736133741925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79060146921378314844989233 59295110191033736133741925)
          ·
            refine ⟨11117833160818825525076611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59295110191033736133741925 11117833160818825525076611)
            ·
              refine ⟨16676749741228238287614917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117833160818825525076611 16676749741228238287614917)
              ·
                refine ⟨3126890576480294678927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16676749741228238287614917 3126890576480294678927797)
                ·
                  refine ⟨293145991545027626149481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126890576480294678927797 293145991545027626149481)
                  ·
                    rfl

theorem cell22_2569049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_2569049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569049 prefixEnd_2569049 := by exact prefixLift 2569049
  have htrace : WordTrace (prefixWord ++ tailWord_2569049) baseStart_2569049 baseEnd_2569049 := by
    simpa [prefixWord, tailWord_2569049, baseEnd_2569049] using wordTrace_append hprefix tailTrace_2569049
  have hstable : (prefixWord ++ tailWord_2569049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569049).length < 2 ^ (prefixWord ++ tailWord_2569049).sum := by decide
  have hdescent : baseEnd_2569049 < baseStart_2569049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569064 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2569064 : Nat := 118140960795 + 2569064 * 2 ^ 59
def prefixEnd_2569064 : Nat := 4983230072969 + 3 ^ 40 * 2569064 * 2
def baseEnd_2569064 : Nat := 879443109441627839323397

theorem tailTrace_2569064 : CollatzResearch.WordTrace tailWord_2569064 prefixEnd_2569064 879443109441627839323397 := by
  unfold tailWord_2569064
  simp only [CollatzResearch.WordTrace]
  refine ⟨46850730982363682022373123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62467641309818242696497497 46850730982363682022373123)
  ·
    refine ⟨70276096473545523033559685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46850730982363682022373123 70276096473545523033559685)
    ·
      refine ⟨13176768088789785568792441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70276096473545523033559685 13176768088789785568792441)
      ·
        refine ⟨9882576066592339176594331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13176768088789785568792441 9882576066592339176594331)
        ·
          refine ⟨14823864099888508764891497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882576066592339176594331 14823864099888508764891497)
          ·
            refine ⟨11117898074916381573668623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14823864099888508764891497 11117898074916381573668623)
            ·
              refine ⟨16676847112374572360502935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117898074916381573668623 16676847112374572360502935)
              ·
                refine ⟨25015270668561858540754403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16676847112374572360502935 25015270668561858540754403)
                ·
                  refine ⟨37522906002842787811131605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25015270668561858540754403 37522906002842787811131605)
                  ·
                    refine ⟨879443109441627839323397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37522906002842787811131605 879443109441627839323397)
                    ·
                      rfl

theorem cell22_2569064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2569064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569064 prefixEnd_2569064 := by exact prefixLift 2569064
  have htrace : WordTrace (prefixWord ++ tailWord_2569064) baseStart_2569064 baseEnd_2569064 := by
    simpa [prefixWord, tailWord_2569064, baseEnd_2569064] using wordTrace_append hprefix tailTrace_2569064
  have hstable : (prefixWord ++ tailWord_2569064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569064).length < 2 ^ (prefixWord ++ tailWord_2569064).sum := by decide
  have hdescent : baseEnd_2569064 < baseStart_2569064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569111 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 4]
def baseStart_2569111 : Nat := 118140960795 + 2569111 * 2 ^ 59
def prefixEnd_2569111 : Nat := 4983230072969 + 3 ^ 40 * 2569111 * 2
def baseEnd_2569111 : Nat := 293153066167378461132751

theorem tailTrace_2569111 : CollatzResearch.WordTrace tailWord_2569111 prefixEnd_2569111 293153066167378461132751 := by
  unfold tailWord_2569111
  simp only [CollatzResearch.WordTrace]
  refine ⟨93703176195557091071707187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62468784130371394047804791 93703176195557091071707187)
  ·
    refine ⟨140554764293335636607560781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93703176195557091071707187 140554764293335636607560781)
    ·
      refine ⟨52708036610000863727835293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140554764293335636607560781 52708036610000863727835293)
      ·
        refine ⟨19765513728750323897938235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52708036610000863727835293 19765513728750323897938235)
        ·
          refine ⟨29648270593125485846907353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19765513728750323897938235 29648270593125485846907353)
          ·
            refine ⟨22236202944844114385180515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29648270593125485846907353 22236202944844114385180515)
            ·
              refine ⟨33354304417266171577770773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236202944844114385180515 33354304417266171577770773)
              ·
                refine ⟨1563483019559351792708005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33354304417266171577770773 1563483019559351792708005)
                ·
                  refine ⟨293153066167378461132751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563483019559351792708005 293153066167378461132751)
                  ·
                    rfl

theorem cell22_2569111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 4].length) (baseStart_2569111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569111 prefixEnd_2569111 := by exact prefixLift 2569111
  have htrace : WordTrace (prefixWord ++ tailWord_2569111) baseStart_2569111 baseEnd_2569111 := by
    simpa [prefixWord, tailWord_2569111, baseEnd_2569111] using wordTrace_append hprefix tailTrace_2569111
  have hstable : (prefixWord ++ tailWord_2569111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569111).length < 2 ^ (prefixWord ++ tailWord_2569111).sum := by decide
  have hdescent : baseEnd_2569111 < baseStart_2569111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569124 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2569124 : Nat := 118140960795 + 2569124 * 2 ^ 59
def prefixEnd_2569124 : Nat := 4983230072969 + 3 ^ 40 * 2569124 * 2
def baseEnd_2569124 : Nat := 879463648667807682823213

theorem tailTrace_2569124 : CollatzResearch.WordTrace tailWord_2569124 prefixEnd_2569124 879463648667807682823213 := by
  unfold tailWord_2569124
  simp only [CollatzResearch.WordTrace]
  refine ⟨46851825172254997145965213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62469100229673329527953617 46851825172254997145965213)
  ·
    refine ⟨17569434439595623929736955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46851825172254997145965213 17569434439595623929736955)
    ·
      refine ⟨26354151659393435894605433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17569434439595623929736955 26354151659393435894605433)
      ·
        refine ⟨19765613744545076920954075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26354151659393435894605433 19765613744545076920954075)
        ·
          refine ⟨29648420616817615381431113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19765613744545076920954075 29648420616817615381431113)
          ·
            refine ⟨22236315462613211536073335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29648420616817615381431113 22236315462613211536073335)
            ·
              refine ⟨33354473193919817304110003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236315462613211536073335 33354473193919817304110003)
              ·
                refine ⟨50031709790879725956165005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33354473193919817304110003 50031709790879725956165005)
                ·
                  refine ⟨18761891171579897233561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50031709790879725956165005 18761891171579897233561877)
                  ·
                    refine ⟨879463648667807682823213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18761891171579897233561877 879463648667807682823213)
                    ·
                      rfl

theorem cell22_2569124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2569124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569124 prefixEnd_2569124 := by exact prefixLift 2569124
  have htrace : WordTrace (prefixWord ++ tailWord_2569124) baseStart_2569124 baseEnd_2569124 := by
    simpa [prefixWord, tailWord_2569124, baseEnd_2569124] using wordTrace_append hprefix tailTrace_2569124
  have hstable : (prefixWord ++ tailWord_2569124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569124).length < 2 ^ (prefixWord ++ tailWord_2569124).sum := by decide
  have hdescent : baseEnd_2569124 < baseStart_2569124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569141 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2569141 : Nat := 118140960795 + 2569141 * 2 ^ 59
def prefixEnd_2569141 : Nat := 4983230072969 + 3 ^ 40 * 2569141 * 2
def baseEnd_2569141 : Nat := 879469468115225305148161

theorem tailTrace_2569141 : CollatzResearch.WordTrace tailWord_2569141 prefixEnd_2569141 879469468115225305148161 := by
  unfold tailWord_2569141
  simp only [CollatzResearch.WordTrace]
  refine ⟨93704270385448406195299277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62469513590298937463532851 93704270385448406195299277)
  ·
    refine ⟨35139101394543152323237229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93704270385448406195299277 35139101394543152323237229)
    ·
      refine ⟨13177163022953682121213961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35139101394543152323237229 13177163022953682121213961)
      ·
        refine ⟨9882872267215261590910471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13177163022953682121213961 9882872267215261590910471)
        ·
          refine ⟨14824308400822892386365707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882872267215261590910471 14824308400822892386365707)
          ·
            refine ⟨22236462601234338579548561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824308400822892386365707 22236462601234338579548561)
            ·
              refine ⟨16677346950925753934661421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22236462601234338579548561 16677346950925753934661421)
              ·
                refine ⟨6254005106597157725498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16677346950925753934661421 6254005106597157725498033)
                ·
                  refine ⟨4690503829947868294123525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254005106597157725498033 4690503829947868294123525)
                  ·
                    refine ⟨879469468115225305148161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4690503829947868294123525 879469468115225305148161)
                    ·
                      rfl

theorem cell22_2569141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2569141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569141 prefixEnd_2569141 := by exact prefixLift 2569141
  have htrace : WordTrace (prefixWord ++ tailWord_2569141) baseStart_2569141 baseEnd_2569141 := by
    simpa [prefixWord, tailWord_2569141, baseEnd_2569141] using wordTrace_append hprefix tailTrace_2569141
  have hstable : (prefixWord ++ tailWord_2569141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569141).length < 2 ^ (prefixWord ++ tailWord_2569141).sum := by decide
  have hdescent : baseEnd_2569141 < baseStart_2569141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569169 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2569169 : Nat := 118140960795 + 2569169 * 2 ^ 59
def prefixEnd_2569169 : Nat := 4983230072969 + 3 ^ 40 * 2569169 * 2
def baseEnd_2569169 : Nat := 879479053087442565448075

theorem tailTrace_2569169 : CollatzResearch.WordTrace tailWord_2569169 prefixEnd_2569169 879479053087442565448075 := by
  unfold tailWord_2569169
  simp only [CollatzResearch.WordTrace]
  refine ⟨93705291629346966977318561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62470194419564644651545707 93705291629346966977318561)
  ·
    refine ⟨70278968722010225232988921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93705291629346966977318561 70278968722010225232988921)
    ·
      refine ⟨52709226541507668924741691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70278968722010225232988921 52709226541507668924741691)
      ·
        refine ⟨79063839812261503387112537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52709226541507668924741691 79063839812261503387112537)
        ·
          refine ⟨59297879859196127540334403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79063839812261503387112537 59297879859196127540334403)
          ·
            refine ⟨88946819788794191310501605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59297879859196127540334403 88946819788794191310501605)
            ·
              refine ⟨16677528710398910870719051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88946819788794191310501605 16677528710398910870719051)
              ·
                refine ⟨25016293065598366306078577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16677528710398910870719051 25016293065598366306078577)
                ·
                  refine ⟨18762219799198774729558933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25016293065598366306078577 18762219799198774729558933)
                  ·
                    refine ⟨879479053087442565448075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18762219799198774729558933 879479053087442565448075)
                    ·
                      rfl

theorem cell22_2569169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2569169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569169 prefixEnd_2569169 := by exact prefixLift 2569169
  have htrace : WordTrace (prefixWord ++ tailWord_2569169) baseStart_2569169 baseEnd_2569169 := by
    simpa [prefixWord, tailWord_2569169, baseEnd_2569169] using wordTrace_append hprefix tailTrace_2569169
  have hstable : (prefixWord ++ tailWord_2569169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569169).length < 2 ^ (prefixWord ++ tailWord_2569169).sum := by decide
  have hdescent : baseEnd_2569169 < baseStart_2569169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569293 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2569293 : Nat := 118140960795 + 2569293 * 2 ^ 59
def prefixEnd_2569293 : Nat := 4983230072969 + 3 ^ 40 * 2569293 * 2
def baseEnd_2569293 : Nat := 879521500821547575347695

theorem tailTrace_2569293 : CollatzResearch.WordTrace tailWord_2569293 prefixEnd_2569293 879521500821547575347695 := by
  unfold tailWord_2569293
  simp only [CollatzResearch.WordTrace]
  refine ⟨93709814280897736154832533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62473209520598490769888355 93709814280897736154832533)
  ·
    refine ⟨4392647544417081382257775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93709814280897736154832533 4392647544417081382257775)
    ·
      refine ⟨6588971316625622073386663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392647544417081382257775 6588971316625622073386663)
      ·
        refine ⟨9883456974938433110079995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6588971316625622073386663 9883456974938433110079995)
        ·
          refine ⟨14825185462407649665119993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883456974938433110079995 14825185462407649665119993)
          ·
            refine ⟨11118889096805737248839995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14825185462407649665119993 11118889096805737248839995)
            ·
              refine ⟨16678333645208605873259993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11118889096805737248839995 16678333645208605873259993)
              ·
                refine ⟨12508750233906454404944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16678333645208605873259993 12508750233906454404944995)
                ·
                  refine ⟨18763125350859681607417493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12508750233906454404944995 18763125350859681607417493)
                  ·
                    refine ⟨879521500821547575347695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18763125350859681607417493 879521500821547575347695)
                    ·
                      rfl

theorem cell22_2569293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2569293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569293 prefixEnd_2569293 := by exact prefixLift 2569293
  have htrace : WordTrace (prefixWord ++ tailWord_2569293) baseStart_2569293 baseEnd_2569293 := by
    simpa [prefixWord, tailWord_2569293, baseEnd_2569293] using wordTrace_append hprefix tailTrace_2569293
  have hstable : (prefixWord ++ tailWord_2569293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569293).length < 2 ^ (prefixWord ++ tailWord_2569293).sum := by decide
  have hdescent : baseEnd_2569293 < baseStart_2569293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569336 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_2569336 : Nat := 118140960795 + 2569336 * 2 ^ 59
def prefixEnd_2569336 : Nat := 4983230072969 + 3 ^ 40 * 2569336 * 2
def baseEnd_2569336 : Nat := 293178740200103265507521

theorem tailTrace_2569336 : CollatzResearch.WordTrace tailWord_2569336 prefixEnd_2569336 293178740200103265507521 := by
  unfold tailWord_2569336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46855691309870977249323931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62474255079827969665765241 46855691309870977249323931)
  ·
    refine ⟨70283536964806465873985897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46855691309870977249323931 70283536964806465873985897)
    ·
      refine ⟨52712652723604849405489423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70283536964806465873985897 52712652723604849405489423)
      ·
        refine ⟨79068979085407274108234135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52712652723604849405489423 79068979085407274108234135)
        ·
          refine ⟨118603468628110911162351203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79068979085407274108234135 118603468628110911162351203)
          ·
            refine ⟨177905202942166366743526805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118603468628110911162351203 177905202942166366743526805)
            ·
              refine ⟨8339306387914048441102819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177905202942166366743526805 8339306387914048441102819)
              ·
                refine ⟨12508959581871072661654229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339306387914048441102819 12508959581871072661654229)
                ·
                  refine ⟨293178740200103265507521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12508959581871072661654229 293178740200103265507521)
                  ·
                    rfl

theorem cell22_2569336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_2569336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569336 prefixEnd_2569336 := by exact prefixLift 2569336
  have htrace : WordTrace (prefixWord ++ tailWord_2569336) baseStart_2569336 baseEnd_2569336 := by
    simpa [prefixWord, tailWord_2569336, baseEnd_2569336] using wordTrace_append hprefix tailTrace_2569336
  have hstable : (prefixWord ++ tailWord_2569336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569336).length < 2 ^ (prefixWord ++ tailWord_2569336).sum := by decide
  have hdescent : baseEnd_2569336 < baseStart_2569336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569351 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2569351 : Nat := 118140960795 + 2569351 * 2 ^ 59
def prefixEnd_2569351 : Nat := 4983230072969 + 3 ^ 40 * 2569351 * 2
def baseEnd_2569351 : Nat := 879541355406854757397517

theorem tailTrace_2569351 : CollatzResearch.WordTrace tailWord_2569351 prefixEnd_2569351 879541355406854757397517 := by
  unfold tailWord_2569351
  simp only [CollatzResearch.WordTrace]
  refine ⟨93711929714687612060443907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62474619809791741373629271 93711929714687612060443907)
  ·
    refine ⟨140567894572031418090665861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93711929714687612060443907 140567894572031418090665861)
    ·
      refine ⟨26356480232255890891999849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140567894572031418090665861 26356480232255890891999849)
      ·
        refine ⟨19767360174191918168999887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26356480232255890891999849 19767360174191918168999887)
        ·
          refine ⟨29651040261287877253499831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19767360174191918168999887 29651040261287877253499831)
          ·
            refine ⟨44476560391931815880249747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29651040261287877253499831 44476560391931815880249747)
            ·
              refine ⟨66714840587897723820374621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44476560391931815880249747 66714840587897723820374621)
              ·
                refine ⟨25018065220461646432640483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66714840587897723820374621 25018065220461646432640483)
                ·
                  refine ⟨37527097830692469648960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25018065220461646432640483 37527097830692469648960725)
                  ·
                    refine ⟨879541355406854757397517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37527097830692469648960725 879541355406854757397517)
                    ·
                      rfl

theorem cell22_2569351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2569351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569351 prefixEnd_2569351 := by exact prefixLift 2569351
  have htrace : WordTrace (prefixWord ++ tailWord_2569351) baseStart_2569351 baseEnd_2569351 := by
    simpa [prefixWord, tailWord_2569351, baseEnd_2569351] using wordTrace_append hprefix tailTrace_2569351
  have hstable : (prefixWord ++ tailWord_2569351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569351).length < 2 ^ (prefixWord ++ tailWord_2569351).sum := by decide
  have hdescent : baseEnd_2569351 < baseStart_2569351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569353 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 5]
def baseStart_2569353 : Nat := 118140960795 + 2569353 * 2 ^ 59
def prefixEnd_2569353 : Nat := 4983230072969 + 3 ^ 40 * 2569353 * 2
def baseEnd_2569353 : Nat := 293180680015909139615837

theorem tailTrace_2569353 : CollatzResearch.WordTrace tailWord_2569353 prefixEnd_2569353 293180680015909139615837 := by
  unfold tailWord_2569353
  simp only [CollatzResearch.WordTrace]
  refine ⟨93712002660680366402016713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62474668440453577601344475 93712002660680366402016713)
  ·
    refine ⟨70284001995510274801512535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93712002660680366402016713 70284001995510274801512535)
    ·
      refine ⟨105426002993265412202268803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70284001995510274801512535 105426002993265412202268803)
      ·
        refine ⟨158139004489898118303403205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105426002993265412202268803 158139004489898118303403205)
        ·
          refine ⟨29651063341855897181888101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158139004489898118303403205 29651063341855897181888101)
          ·
            refine ⟨5559574376597980721604019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29651063341855897181888101 5559574376597980721604019)
            ·
              refine ⟨8339361564896971082406029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559574376597980721604019 8339361564896971082406029)
              ·
                refine ⟨3127260586836364155902261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8339361564896971082406029 3127260586836364155902261)
                ·
                  refine ⟨293180680015909139615837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127260586836364155902261 293180680015909139615837)
                  ·
                    rfl

theorem cell22_2569353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_2569353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569353 prefixEnd_2569353 := by exact prefixLift 2569353
  have htrace : WordTrace (prefixWord ++ tailWord_2569353) baseStart_2569353 baseEnd_2569353 := by
    simpa [prefixWord, tailWord_2569353, baseEnd_2569353] using wordTrace_append hprefix tailTrace_2569353
  have hstable : (prefixWord ++ tailWord_2569353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569353).length < 2 ^ (prefixWord ++ tailWord_2569353).sum := by decide
  have hdescent : baseEnd_2569353 < baseStart_2569353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569413 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_2569413 : Nat := 118140960795 + 2569413 * 2 ^ 59
def prefixEnd_2569413 : Nat := 4983230072969 + 3 ^ 40 * 2569413 * 2
def baseEnd_2569413 : Nat := 879562579273907262347327

theorem tailTrace_2569413 : CollatzResearch.WordTrace tailWord_2569413 prefixEnd_2569413 879562579273907262347327 := by
  unfold tailWord_2569413
  simp only [CollatzResearch.WordTrace]
  refine ⟨93714191040462996649200893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62476127360308664432800595 93714191040462996649200893)
  ·
    refine ⟨35142821640173623743450335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93714191040462996649200893 35142821640173623743450335)
    ·
      refine ⟨52714232460260435615175503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35142821640173623743450335 52714232460260435615175503)
      ·
        refine ⟨79071348690390653422763255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52714232460260435615175503 79071348690390653422763255)
        ·
          refine ⟨118607023035585980134144883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79071348690390653422763255 118607023035585980134144883)
          ·
            refine ⟨177910534553378970201217325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118607023035585980134144883 177910534553378970201217325)
            ·
              refine ⟨66716450457517113825456497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177910534553378970201217325 66716450457517113825456497)
              ·
                refine ⟨50037337843137835369092373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66716450457517113825456497 50037337843137835369092373)
                ·
                  refine ⟨2345500211397086032926205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50037337843137835369092373 2345500211397086032926205)
                  ·
                    refine ⟨879562579273907262347327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345500211397086032926205 879562579273907262347327)
                    ·
                      rfl

theorem cell22_2569413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_2569413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569413 prefixEnd_2569413 := by exact prefixLift 2569413
  have htrace : WordTrace (prefixWord ++ tailWord_2569413) baseStart_2569413 baseEnd_2569413 := by
    simpa [prefixWord, tailWord_2569413, baseEnd_2569413] using wordTrace_append hprefix tailTrace_2569413
  have hstable : (prefixWord ++ tailWord_2569413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569413).length < 2 ^ (prefixWord ++ tailWord_2569413).sum := by decide
  have hdescent : baseEnd_2569413 < baseStart_2569413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569432 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_2569432 : Nat := 118140960795 + 2569432 * 2 ^ 59
def prefixEnd_2569432 : Nat := 4983230072969 + 3 ^ 40 * 2569432 * 2
def baseEnd_2569432 : Nat := 293189694454065848707423

theorem tailTrace_2569432 : CollatzResearch.WordTrace tailWord_2569432 prefixEnd_2569432 293189694454065848707423 := by
  unfold tailWord_2569432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46857442013697081447071275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62476589351596108596095033 46857442013697081447071275)
  ·
    refine ⟨70286163020545622170606913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46857442013697081447071275 70286163020545622170606913)
    ·
      refine ⟨52714622265409216627955185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70286163020545622170606913 52714622265409216627955185)
      ·
        refine ⟨39535966699056912470966389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52714622265409216627955185 39535966699056912470966389)
        ·
          refine ⟨3706496878036585544153099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39535966699056912470966389 3706496878036585544153099)
          ·
            refine ⟨5559745317054878316229649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706496878036585544153099 5559745317054878316229649)
            ·
              refine ⟨4169808987791158737172237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5559745317054878316229649 4169808987791158737172237)
              ·
                refine ⟨1563678370421684526439589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4169808987791158737172237 1563678370421684526439589)
                ·
                  refine ⟨293189694454065848707423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1563678370421684526439589 293189694454065848707423)
                  ·
                    rfl

theorem cell22_2569432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_2569432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569432 prefixEnd_2569432 := by exact prefixLift 2569432
  have htrace : WordTrace (prefixWord ++ tailWord_2569432) baseStart_2569432 baseEnd_2569432 := by
    simpa [prefixWord, tailWord_2569432, baseEnd_2569432] using wordTrace_append hprefix tailTrace_2569432
  have hstable : (prefixWord ++ tailWord_2569432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569432).length < 2 ^ (prefixWord ++ tailWord_2569432).sum := by decide
  have hdescent : baseEnd_2569432 < baseStart_2569432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569447 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2569447 : Nat := 118140960795 + 2569447 * 2 ^ 59
def prefixEnd_2569447 : Nat := 4983230072969 + 3 ^ 40 * 2569447 * 2
def baseEnd_2569447 : Nat := 879574218168742506997223

theorem tailTrace_2569447 : CollatzResearch.WordTrace tailWord_2569447 prefixEnd_2569447 879574218168742506997223 := by
  unfold tailWord_2569447
  simp only [CollatzResearch.WordTrace]
  refine ⟨93715431122339820455938595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62476954081559880303959063 93715431122339820455938595)
  ·
    refine ⟨140573146683509730683907893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93715431122339820455938595 140573146683509730683907893)
    ·
      refine ⟨13178732501579037251616365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140573146683509730683907893 13178732501579037251616365)
      ·
        refine ⟨4942024688092138969356137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13178732501579037251616365 4942024688092138969356137)
        ·
          refine ⟨3706518516069104227017103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4942024688092138969356137 3706518516069104227017103)
          ·
            refine ⟨5559777774103656340525655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706518516069104227017103 5559777774103656340525655)
            ·
              refine ⟨8339666661155484510788483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559777774103656340525655 8339666661155484510788483)
              ·
                refine ⟨12509499991733226766182725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339666661155484510788483 12509499991733226766182725)
                ·
                  refine ⟨2345531248449980018659261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12509499991733226766182725 2345531248449980018659261)
                  ·
                    refine ⟨879574218168742506997223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345531248449980018659261 879574218168742506997223)
                    ·
                      rfl

theorem cell22_2569447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2569447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569447 prefixEnd_2569447 := by exact prefixLift 2569447
  have htrace : WordTrace (prefixWord ++ tailWord_2569447) baseStart_2569447 baseEnd_2569447 := by
    simpa [prefixWord, tailWord_2569447, baseEnd_2569447] using wordTrace_append hprefix tailTrace_2569447
  have hstable : (prefixWord ++ tailWord_2569447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569447).length < 2 ^ (prefixWord ++ tailWord_2569447).sum := by decide
  have hdescent : baseEnd_2569447 < baseStart_2569447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569475 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 3, 3]
def baseStart_2569475 : Nat := 118140960795 + 2569475 * 2 ^ 59
def prefixEnd_2569475 : Nat := 4983230072969 + 3 ^ 40 * 2569475 * 2
def baseEnd_2569475 : Nat := 879583803140959767297137

theorem tailTrace_2569475 : CollatzResearch.WordTrace tailWord_2569475 prefixEnd_2569475 879583803140959767297137 := by
  unfold tailWord_2569475
  simp only [CollatzResearch.WordTrace]
  refine ⟨93716452366238381237957879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62477634910825587491971919 93716452366238381237957879)
  ·
    refine ⟨140574678549357571856936819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93716452366238381237957879 140574678549357571856936819)
    ·
      refine ⟨210862017824036357785405229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140574678549357571856936819 210862017824036357785405229)
      ·
        refine ⟨79073256684013634169526961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210862017824036357785405229 79073256684013634169526961)
        ·
          refine ⟨59304942513010225627145221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79073256684013634169526961 59304942513010225627145221)
          ·
            refine ⟨11119676721189417305089729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59304942513010225627145221 11119676721189417305089729)
            ·
              refine ⟨8339757540892062978817297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11119676721189417305089729 8339757540892062978817297)
              ·
                refine ⟨6254818155669047234112973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8339757540892062978817297 6254818155669047234112973)
                ·
                  refine ⟨2345556808375892712792365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6254818155669047234112973 2345556808375892712792365)
                  ·
                    refine ⟨879583803140959767297137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345556808375892712792365 879583803140959767297137)
                    ·
                      rfl

theorem cell22_2569475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].length) (baseStart_2569475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569475 prefixEnd_2569475 := by exact prefixLift 2569475
  have htrace : WordTrace (prefixWord ++ tailWord_2569475) baseStart_2569475 baseEnd_2569475 := by
    simpa [prefixWord, tailWord_2569475, baseEnd_2569475] using wordTrace_append hprefix tailTrace_2569475
  have hstable : (prefixWord ++ tailWord_2569475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569475).length < 2 ^ (prefixWord ++ tailWord_2569475).sum := by decide
  have hdescent : baseEnd_2569475 < baseStart_2569475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569522 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_2569522 : Nat := 118140960795 + 2569522 * 2 ^ 59
def prefixEnd_2569522 : Nat := 4983230072969 + 3 ^ 40 * 2569522 * 2
def baseEnd_2569522 : Nat := 293199964067155770457331

theorem tailTrace_2569522 : CollatzResearch.WordTrace tailWord_2569522 prefixEnd_2569522 293199964067155770457331 := by
  unfold tailWord_2569522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429541649267027066229705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62478777731378738843279213 23429541649267027066229705)
  ·
    refine ⟨17572156236950270299672279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23429541649267027066229705 17572156236950270299672279)
    ·
      refine ⟨26358234355425405449508419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17572156236950270299672279 26358234355425405449508419)
      ·
        refine ⟨39537351533138108174262629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26358234355425405449508419 39537351533138108174262629)
        ·
          refine ⟨7413253412463395282674243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39537351533138108174262629 7413253412463395282674243)
          ·
            refine ⟨11119880118695092924011365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413253412463395282674243 11119880118695092924011365)
            ·
              refine ⟨2084977522255329923252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11119880118695092924011365 2084977522255329923252131)
              ·
                refine ⟨3127466283382994884878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084977522255329923252131 3127466283382994884878197)
                ·
                  refine ⟨293199964067155770457331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127466283382994884878197 293199964067155770457331)
                  ·
                    rfl

theorem cell22_2569522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_2569522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569522 prefixEnd_2569522 := by exact prefixLift 2569522
  have htrace : WordTrace (prefixWord ++ tailWord_2569522) baseStart_2569522 baseEnd_2569522 := by
    simpa [prefixWord, tailWord_2569522, baseEnd_2569522] using wordTrace_append hprefix tailTrace_2569522
  have hstable : (prefixWord ++ tailWord_2569522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569522).length < 2 ^ (prefixWord ++ tailWord_2569522).sum := by decide
  have hdescent : baseEnd_2569522 < baseStart_2569522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569535 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2569535 : Nat := 118140960795 + 2569535 * 2 ^ 59
def prefixEnd_2569535 : Nat := 4983230072969 + 3 ^ 40 * 2569535 * 2
def baseEnd_2569535 : Nat := 879604342367139610796953

theorem tailTrace_2569535 : CollatzResearch.WordTrace tailWord_2569535 prefixEnd_2569535 879604342367139610796953 := by
  unfold tailWord_2569535
  simp only [CollatzResearch.WordTrace]
  refine ⟨93718640746021011485142059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62479093830680674323428039 93718640746021011485142059)
  ·
    refine ⟨140577961119031517227713089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93718640746021011485142059 140577961119031517227713089)
    ·
      refine ⟨105433470839273637920784817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140577961119031517227713089 105433470839273637920784817)
      ·
        refine ⟨79075103129455228440588613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105433470839273637920784817 79075103129455228440588613)
        ·
          refine ⟨14826581836772855332610365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79075103129455228440588613 14826581836772855332610365)
          ·
            refine ⟨5559968188789820749728887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14826581836772855332610365 5559968188789820749728887)
            ·
              refine ⟨8339952283184731124593331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559968188789820749728887 8339952283184731124593331)
              ·
                refine ⟨12509928424777096686889997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339952283184731124593331 12509928424777096686889997)
                ·
                  refine ⟨4691223159291411257583749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12509928424777096686889997 4691223159291411257583749)
                  ·
                    refine ⟨879604342367139610796953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691223159291411257583749 879604342367139610796953)
                    ·
                      rfl

theorem cell22_2569535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2569535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569535 prefixEnd_2569535 := by exact prefixLift 2569535
  have htrace : WordTrace (prefixWord ++ tailWord_2569535) baseStart_2569535 baseEnd_2569535 := by
    simpa [prefixWord, tailWord_2569535, baseEnd_2569535] using wordTrace_append hprefix tailTrace_2569535
  have hstable : (prefixWord ++ tailWord_2569535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569535).length < 2 ^ (prefixWord ++ tailWord_2569535).sum := by decide
  have hdescent : baseEnd_2569535 < baseStart_2569535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569552 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_2569552 : Nat := 118140960795 + 2569552 * 2 ^ 59
def prefixEnd_2569552 : Nat := 4983230072969 + 3 ^ 40 * 2569552 * 2
def baseEnd_2569552 : Nat := 879610161814557233121901

theorem tailTrace_2569552 : CollatzResearch.WordTrace tailWord_2569552 prefixEnd_2569552 879610161814557233121901 := by
  unfold tailWord_2569552
  simp only [CollatzResearch.WordTrace]
  refine ⟨46859630393479711694255455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62479507191306282259007273 46859630393479711694255455)
  ·
    refine ⟨70289445590219567541383183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46859630393479711694255455 70289445590219567541383183)
    ·
      refine ⟨105434168385329351312074775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70289445590219567541383183 105434168385329351312074775)
      ·
        refine ⟨158151252577994026968112163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105434168385329351312074775 158151252577994026968112163)
        ·
          refine ⟨237226878866991040452168245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158151252577994026968112163 237226878866991040452168245)
          ·
            refine ⟨22240019893780410042390773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237226878866991040452168245 22240019893780410042390773)
            ·
              refine ⟨2085001865041913441474135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22240019893780410042390773 2085001865041913441474135)
              ·
                refine ⟨3127502797562870162211203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085001865041913441474135 3127502797562870162211203)
                ·
                  refine ⟨4691254196344305243316805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127502797562870162211203 4691254196344305243316805)
                  ·
                    refine ⟨879610161814557233121901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691254196344305243316805 879610161814557233121901)
                    ·
                      rfl

theorem cell22_2569552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_2569552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569552 prefixEnd_2569552 := by exact prefixLift 2569552
  have htrace : WordTrace (prefixWord ++ tailWord_2569552) baseStart_2569552 baseEnd_2569552 := by
    simpa [prefixWord, tailWord_2569552, baseEnd_2569552] using wordTrace_append hprefix tailTrace_2569552
  have hstable : (prefixWord ++ tailWord_2569552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569552).length < 2 ^ (prefixWord ++ tailWord_2569552).sum := by decide
  have hdescent : baseEnd_2569552 < baseStart_2569552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569595 : List Nat := [1, 1, 1, 1, 1, 6, 5, 6]
def baseStart_2569595 : Nat := 118140960795 + 2569595 * 2 ^ 59
def prefixEnd_2569595 : Nat := 4983230072969 + 3 ^ 40 * 2569595 * 2
def baseEnd_2569595 : Nat := 97736097954813272699641

theorem tailTrace_2569595 : CollatzResearch.WordTrace tailWord_2569595 prefixEnd_2569595 97736097954813272699641 := by
  unfold tailWord_2569595
  simp only [CollatzResearch.WordTrace]
  refine ⟨93720829125803641732326239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62480552750535761154884159 93720829125803641732326239)
  ·
    refine ⟨140581243688705462598489359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93720829125803641732326239 140581243688705462598489359)
    ·
      refine ⟨210871865533058193897734039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140581243688705462598489359 210871865533058193897734039)
      ·
        refine ⟨316307798299587290846601059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210871865533058193897734039 316307798299587290846601059)
        ·
          refine ⟨474461697449380936269901589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316307798299587290846601059 474461697449380936269901589)
          ·
            refine ⟨22240392067939731387651637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 474461697449380936269901589 22240392067939731387651637)
            ·
              refine ⟨2085036756369349817592341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22240392067939731387651637 2085036756369349817592341)
              ·
                refine ⟨97736097954813272699641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2085036756369349817592341 97736097954813272699641)
                ·
                  rfl

theorem cell22_2569595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 6].length) (baseStart_2569595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569595 prefixEnd_2569595 := by exact prefixLift 2569595
  have htrace : WordTrace (prefixWord ++ tailWord_2569595) baseStart_2569595 baseEnd_2569595 := by
    simpa [prefixWord, tailWord_2569595, baseEnd_2569595] using wordTrace_append hprefix tailTrace_2569595
  have hstable : (prefixWord ++ tailWord_2569595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569595).length < 2 ^ (prefixWord ++ tailWord_2569595).sum := by decide
  have hdescent : baseEnd_2569595 < baseStart_2569595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569700 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2569700 : Nat := 118140960795 + 2569700 * 2 ^ 59
def prefixEnd_2569700 : Nat := 4983230072969 + 3 ^ 40 * 2569700 * 2
def baseEnd_2569700 : Nat := 879660825239134180421447

theorem tailTrace_2569700 : CollatzResearch.WordTrace tailWord_2569700 prefixEnd_2569700 879660825239134180421447 := by
  unfold tailWord_2569700
  simp only [CollatzResearch.WordTrace]
  refine ⟨46862329395211622332449277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62483105860282163109932369 46862329395211622332449277)
  ·
    refine ⟨17573373523204358374668479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46862329395211622332449277 17573373523204358374668479)
    ·
      refine ⟨26360060284806537562002719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17573373523204358374668479 26360060284806537562002719)
      ·
        refine ⟨39540090427209806343004079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26360060284806537562002719 39540090427209806343004079)
        ·
          refine ⟨59310135640814709514506119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39540090427209806343004079 59310135640814709514506119)
          ·
            refine ⟨88965203461222064271759179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59310135640814709514506119 88965203461222064271759179)
            ·
              refine ⟨133447805191833096407638769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88965203461222064271759179 133447805191833096407638769)
              ·
                refine ⟨100085853893874822305729077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133447805191833096407638769 100085853893874822305729077)
                ·
                  refine ⟨9383048802550764591162101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100085853893874822305729077 9383048802550764591162101)
                  ·
                    refine ⟨879660825239134180421447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9383048802550764591162101 879660825239134180421447)
                    ·
                      rfl

theorem cell22_2569700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2569700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569700 prefixEnd_2569700 := by exact prefixLift 2569700
  have htrace : WordTrace (prefixWord ++ tailWord_2569700) baseStart_2569700 baseEnd_2569700 := by
    simpa [prefixWord, tailWord_2569700, baseEnd_2569700] using wordTrace_append hprefix tailTrace_2569700
  have hstable : (prefixWord ++ tailWord_2569700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569700).length < 2 ^ (prefixWord ++ tailWord_2569700).sum := by decide
  have hdescent : baseEnd_2569700 < baseStart_2569700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569747 : List Nat := [1, 1, 1, 2, 1, 8, 1, 7]
def baseStart_2569747 : Nat := 118140960795 + 2569747 * 2 ^ 59
def prefixEnd_2569747 : Nat := 4983230072969 + 3 ^ 40 * 2569747 * 2
def baseEnd_2569747 : Nat := 97741879366626858277367

theorem tailTrace_2569747 : CollatzResearch.WordTrace tailWord_2569747 prefixEnd_2569747 97741879366626858277367 := by
  unfold tailWord_2569747
  simp only [CollatzResearch.WordTrace]
  refine ⟨93726373021252971691859495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62484248680835314461239663 93726373021252971691859495)
  ·
    refine ⟨140589559531879457537789243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93726373021252971691859495 140589559531879457537789243)
    ·
      refine ⟨210884339297819186306683865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140589559531879457537789243 210884339297819186306683865)
      ·
        refine ⟨158163254473364389730012899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210884339297819186306683865 158163254473364389730012899)
        ·
          refine ⟨237244881710046584595019349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158163254473364389730012899 237244881710046584595019349)
          ·
            refine ⟨2780213457539608413222883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 237244881710046584595019349 2780213457539608413222883)
            ·
              refine ⟨4170320186309412619834325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780213457539608413222883 4170320186309412619834325)
              ·
                refine ⟨97741879366626858277367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4170320186309412619834325 97741879366626858277367)
                ·
                  rfl

theorem cell22_2569747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 7].length) (baseStart_2569747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569747 prefixEnd_2569747 := by exact prefixLift 2569747
  have htrace : WordTrace (prefixWord ++ tailWord_2569747) baseStart_2569747 baseEnd_2569747 := by
    simpa [prefixWord, tailWord_2569747, baseEnd_2569747] using wordTrace_append hprefix tailTrace_2569747
  have hstable : (prefixWord ++ tailWord_2569747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569747).length < 2 ^ (prefixWord ++ tailWord_2569747).sum := by decide
  have hdescent : baseEnd_2569747 < baseStart_2569747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569809 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 5]
def baseStart_2569809 : Nat := 118140960795 + 2569809 * 2 ^ 59
def prefixEnd_2569809 : Nat := 4983230072969 + 3 ^ 40 * 2569809 * 2
def baseEnd_2569809 : Nat := 293232712722231409815371

theorem tailTrace_2569809 : CollatzResearch.WordTrace tailWord_2569809 prefixEnd_2569809 293232712722231409815371 := by
  unfold tailWord_2569809
  simp only [CollatzResearch.WordTrace]
  refine ⟨93728634347028356280616481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62485756231352237520410987 93728634347028356280616481)
  ·
    refine ⟨70296475760271267210462361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93728634347028356280616481 70296475760271267210462361)
    ·
      refine ⟨52722356820203450407846771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70296475760271267210462361 52722356820203450407846771)
      ·
        refine ⟨79083535230305175611770157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52722356820203450407846771 79083535230305175611770157)
        ·
          refine ⟨29656325711364440854413809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79083535230305175611770157 29656325711364440854413809)
          ·
            refine ⟨22242244283523330640810357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29656325711364440854413809 22242244283523330640810357)
            ·
              refine ⟨2085210401580312247575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22242244283523330640810357 2085210401580312247575971)
              ·
                refine ⟨3127815602370468371363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085210401580312247575971 3127815602370468371363957)
                ·
                  refine ⟨293232712722231409815371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127815602370468371363957 293232712722231409815371)
                  ·
                    rfl

theorem cell22_2569809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_2569809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569809 prefixEnd_2569809 := by exact prefixLift 2569809
  have htrace : WordTrace (prefixWord ++ tailWord_2569809) baseStart_2569809 baseEnd_2569809 := by
    simpa [prefixWord, tailWord_2569809, baseEnd_2569809] using wordTrace_append hprefix tailTrace_2569809
  have hstable : (prefixWord ++ tailWord_2569809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569809).length < 2 ^ (prefixWord ++ tailWord_2569809).sum := by decide
  have hdescent : baseEnd_2569809 < baseStart_2569809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569867 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_2569867 : Nat := 118140960795 + 2569867 * 2 ^ 59
def prefixEnd_2569867 : Nat := 4983230072969 + 3 ^ 40 * 2569867 * 2
def baseEnd_2569867 : Nat := 879717992752001411495935

theorem tailTrace_2569867 : CollatzResearch.WordTrace tailWord_2569867 prefixEnd_2569867 879717992752001411495935 := by
  unfold tailWord_2569867
  simp only [CollatzResearch.WordTrace]
  refine ⟨93730749780818232186227855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62487166520545488124151903 93730749780818232186227855)
  ·
    refine ⟨140596124671227348279341783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93730749780818232186227855 140596124671227348279341783)
    ·
      refine ⟨210894187006841022419012675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140596124671227348279341783 210894187006841022419012675)
      ·
        refine ⟨316341280510261533628519013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210894187006841022419012675 316341280510261533628519013)
        ·
          refine ⟨59313990095674037555347315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316341280510261533628519013 59313990095674037555347315)
          ·
            refine ⟨88970985143511056333020973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59313990095674037555347315 88970985143511056333020973)
            ·
              refine ⟨33364119428816646124882865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88970985143511056333020973 33364119428816646124882865)
              ·
                refine ⟨25023089571612484593662149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33364119428816646124882865 25023089571612484593662149)
                ·
                  refine ⟨4691829294677340861311653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25023089571612484593662149 4691829294677340861311653)
                  ·
                    refine ⟨879717992752001411495935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691829294677340861311653 879717992752001411495935)
                    ·
                      rfl

theorem cell22_2569867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_2569867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569867 prefixEnd_2569867 := by exact prefixLift 2569867
  have htrace : WordTrace (prefixWord ++ tailWord_2569867) baseStart_2569867 baseEnd_2569867 := by
    simpa [prefixWord, tailWord_2569867, baseEnd_2569867] using wordTrace_append hprefix tailTrace_2569867
  have hstable : (prefixWord ++ tailWord_2569867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569867).length < 2 ^ (prefixWord ++ tailWord_2569867).sum := by decide
  have hdescent : baseEnd_2569867 < baseStart_2569867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569886 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2569886 : Nat := 118140960795 + 2569886 * 2 ^ 59
def prefixEnd_2569886 : Nat := 4983230072969 + 3 ^ 40 * 2569886 * 2
def baseEnd_2569886 : Nat := 879724496840291695270877

theorem tailTrace_2569886 : CollatzResearch.WordTrace tailWord_2569886 prefixEnd_2569886 879724496840291695270877 := by
  unfold tailWord_2569886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716430345968674803896189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62487628511832932287446341 11716430345968674803896189)
  ·
    refine ⟨4393661379738253051461071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11716430345968674803896189 4393661379738253051461071)
    ·
      refine ⟨6590492069607379577191607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4393661379738253051461071 6590492069607379577191607)
      ·
        refine ⟨9885738104411069365787411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6590492069607379577191607 9885738104411069365787411)
        ·
          refine ⟨14828607156616604048681117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9885738104411069365787411 14828607156616604048681117)
          ·
            refine ⟨5560727683731226518255419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14828607156616604048681117 5560727683731226518255419)
            ·
              refine ⟨8341091525596839777383129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5560727683731226518255419 8341091525596839777383129)
              ·
                refine ⟨6255818644197629833037347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8341091525596839777383129 6255818644197629833037347)
                ·
                  refine ⟨9383727966296444749556021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255818644197629833037347 9383727966296444749556021)
                  ·
                    refine ⟨879724496840291695270877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9383727966296444749556021 879724496840291695270877)
                    ·
                      rfl

theorem cell22_2569886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2569886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569886 prefixEnd_2569886 := by exact prefixLift 2569886
  have htrace : WordTrace (prefixWord ++ tailWord_2569886) baseStart_2569886 baseEnd_2569886 := by
    simpa [prefixWord, tailWord_2569886, baseEnd_2569886] using wordTrace_append hprefix tailTrace_2569886
  have hstable : (prefixWord ++ tailWord_2569886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569886).length < 2 ^ (prefixWord ++ tailWord_2569886).sum := by decide
  have hdescent : baseEnd_2569886 < baseStart_2569886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569890 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2569890 : Nat := 118140960795 + 2569890 * 2 ^ 59
def prefixEnd_2569890 : Nat := 4983230072969 + 3 ^ 40 * 2569890 * 2
def baseEnd_2569890 : Nat := 879725866122037018170865

theorem tailTrace_2569890 : CollatzResearch.WordTrace tailWord_2569890 prefixEnd_2569890 879725866122037018170865 := by
  unfold tailWord_2569890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23432897164933726778578781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62487725773156604742876749 23432897164933726778578781)
  ·
    refine ⟨8787336436850147541967043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23432897164933726778578781 8787336436850147541967043)
    ·
      refine ⟨13181004655275221312950565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8787336436850147541967043 13181004655275221312950565)
      ·
        refine ⟨2471438372864103996178231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13181004655275221312950565 2471438372864103996178231)
        ·
          refine ⟨3707157559296155994267347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471438372864103996178231 3707157559296155994267347)
          ·
            refine ⟨5560736338944233991401021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707157559296155994267347 5560736338944233991401021)
            ·
              refine ⟨2085276127104087746775383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5560736338944233991401021 2085276127104087746775383)
              ·
                refine ⟨3127914190656131620163075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085276127104087746775383 3127914190656131620163075)
                ·
                  refine ⟨4691871285984197430244613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127914190656131620163075 4691871285984197430244613)
                  ·
                    refine ⟨879725866122037018170865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691871285984197430244613 879725866122037018170865)
                    ·
                      rfl

theorem cell22_2569890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2569890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569890 prefixEnd_2569890 := by exact prefixLift 2569890
  have htrace : WordTrace (prefixWord ++ tailWord_2569890) baseStart_2569890 baseEnd_2569890 := by
    simpa [prefixWord, tailWord_2569890, baseEnd_2569890] using wordTrace_append hprefix tailTrace_2569890
  have hstable : (prefixWord ++ tailWord_2569890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569890).length < 2 ^ (prefixWord ++ tailWord_2569890).sum := by decide
  have hdescent : baseEnd_2569890 < baseStart_2569890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569933 : List Nat := [1, 6, 2, 1, 1, 2, 3, 6]
def baseStart_2569933 : Nat := 118140960795 + 2569933 * 2 ^ 59
def prefixEnd_2569933 : Nat := 4983230072969 + 3 ^ 40 * 2569933 * 2
def baseEnd_2569933 : Nat := 97748953988977693260637

theorem tailTrace_2569933 : CollatzResearch.WordTrace tailWord_2569933 prefixEnd_2569933 97748953988977693260637 := by
  unfold tailWord_2569933
  simp only [CollatzResearch.WordTrace]
  refine ⟨93733156998579125458130453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62488771332386083638753635 93733156998579125458130453)
  ·
    refine ⟨4393741734308396505849865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93733156998579125458130453 4393741734308396505849865)
    ·
      refine ⟨3295306300731297379387399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4393741734308396505849865 3295306300731297379387399)
      ·
        refine ⟨4942959451096946069081099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295306300731297379387399 4942959451096946069081099)
        ·
          refine ⟨7414439176645419103621649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942959451096946069081099 7414439176645419103621649)
          ·
            refine ⟨5560829382484064327716237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7414439176645419103621649 5560829382484064327716237)
            ·
              refine ⟨2085311018431524122893589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5560829382484064327716237 2085311018431524122893589)
              ·
                refine ⟨97748953988977693260637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2085311018431524122893589 97748953988977693260637)
                ·
                  rfl

theorem cell22_2569933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 6].length) (baseStart_2569933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2569933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2569933 prefixEnd_2569933 := by exact prefixLift 2569933
  have htrace : WordTrace (prefixWord ++ tailWord_2569933) baseStart_2569933 baseEnd_2569933 := by
    simpa [prefixWord, tailWord_2569933, baseEnd_2569933] using wordTrace_append hprefix tailTrace_2569933
  have hstable : (prefixWord ++ tailWord_2569933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569933).length < 2 ^ (prefixWord ++ tailWord_2569933).sum := by decide
  have hdescent : baseEnd_2569933 < baseStart_2569933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570019 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_2570019 : Nat := 118140960795 + 2570019 * 2 ^ 59
def prefixEnd_2570019 : Nat := 4983230072969 + 3 ^ 40 * 2570019 * 2
def baseEnd_2570019 : Nat := 879770025458323681695469

theorem tailTrace_2570019 : CollatzResearch.WordTrace tailWord_2570019 prefixEnd_2570019 879770025458323681695469 := by
  unfold tailWord_2570019
  simp only [CollatzResearch.WordTrace]
  refine ⟨93736293676267562145761111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62490862450845041430507407 93736293676267562145761111)
  ·
    refine ⟨140604440514401343218641667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93736293676267562145761111 140604440514401343218641667)
    ·
      refine ⟨210906660771602014827962501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140604440514401343218641667 210906660771602014827962501)
      ·
        refine ⟨39544998894675377780242969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210906660771602014827962501 39544998894675377780242969)
        ·
          refine ⟨29658749171006533335182227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39544998894675377780242969 29658749171006533335182227)
          ·
            refine ⟨44488123756509800002773341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29658749171006533335182227 44488123756509800002773341)
            ·
              refine ⟨16683046408691175001040003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44488123756509800002773341 16683046408691175001040003)
              ·
                refine ⟨25024569613036762501560005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16683046408691175001040003 25024569613036762501560005)
                ·
                  refine ⟨4692106802444392969042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25024569613036762501560005 4692106802444392969042501)
                  ·
                    refine ⟨879770025458323681695469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692106802444392969042501 879770025458323681695469)
                    ·
                      rfl

theorem cell22_2570019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_2570019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570019 prefixEnd_2570019 := by exact prefixLift 2570019
  have htrace : WordTrace (prefixWord ++ tailWord_2570019) baseStart_2570019 baseEnd_2570019 := by
    simpa [prefixWord, tailWord_2570019, baseEnd_2570019] using wordTrace_append hprefix tailTrace_2570019
  have hstable : (prefixWord ++ tailWord_2570019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570019).length < 2 ^ (prefixWord ++ tailWord_2570019).sum := by decide
  have hdescent : baseEnd_2570019 < baseStart_2570019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570021 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_2570021 : Nat := 118140960795 + 2570021 * 2 ^ 59
def prefixEnd_2570021 : Nat := 4983230072969 + 3 ^ 40 * 2570021 * 2
def baseEnd_2570021 : Nat := 879770710099196343145463

theorem tailTrace_2570021 : CollatzResearch.WordTrace tailWord_2570021 prefixEnd_2570021 879770710099196343145463 := by
  unfold tailWord_2570021
  simp only [CollatzResearch.WordTrace]
  refine ⟨93736366622260316487333917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62490911081506877658222611 93736366622260316487333917)
  ·
    refine ⟨35151137483347618682750219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93736366622260316487333917 35151137483347618682750219)
    ·
      refine ⟨52726706225021428024125329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35151137483347618682750219 52726706225021428024125329)
      ·
        refine ⟨39545029668766071018093997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52726706225021428024125329 39545029668766071018093997)
        ·
          refine ⟨14829386125787276631785249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39545029668766071018093997 14829386125787276631785249)
          ·
            refine ⟨11122039594340457473838937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14829386125787276631785249 11122039594340457473838937)
            ·
              refine ⟨8341529695755343105379203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11122039594340457473838937 8341529695755343105379203)
              ·
                refine ⟨12512294543633014658068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341529695755343105379203 12512294543633014658068805)
                ·
                  refine ⟨2346055226931190248387901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12512294543633014658068805 2346055226931190248387901)
                  ·
                    refine ⟨879770710099196343145463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346055226931190248387901 879770710099196343145463)
                    ·
                      rfl

theorem cell22_2570021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_2570021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570021 prefixEnd_2570021 := by exact prefixLift 2570021
  have htrace : WordTrace (prefixWord ++ tailWord_2570021) baseStart_2570021 baseEnd_2570021 := by
    simpa [prefixWord, tailWord_2570021, baseEnd_2570021] using wordTrace_append hprefix tailTrace_2570021
  have hstable : (prefixWord ++ tailWord_2570021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570021).length < 2 ^ (prefixWord ++ tailWord_2570021).sum := by decide
  have hdescent : baseEnd_2570021 < baseStart_2570021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570034 : List Nat := [3, 2, 1, 1, 3, 2, 1, 9]
def baseStart_2570034 : Nat := 118140960795 + 2570034 * 2 ^ 59
def prefixEnd_2570034 : Nat := 4983230072969 + 3 ^ 40 * 2570034 * 2
def baseEnd_2570034 : Nat := 97752795584985404730047

theorem tailTrace_2570034 : CollatzResearch.WordTrace tailWord_2570034 prefixEnd_2570034 97752795584985404730047 := by
  unfold tailWord_2570034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23434210192803304926889289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62491227180808813138371437 23434210192803304926889289)
  ·
    refine ⟨17575657644602478695166967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23434210192803304926889289 17575657644602478695166967)
    ·
      refine ⟨26363486466903718042750451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17575657644602478695166967 26363486466903718042750451)
      ·
        refine ⟨39545229700355577064125677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26363486466903718042750451 39545229700355577064125677)
        ·
          refine ⟨14829461137633341399047129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39545229700355577064125677 14829461137633341399047129)
          ·
            refine ⟨11122095853225006049285347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14829461137633341399047129 11122095853225006049285347)
            ·
              refine ⟨16683143779837509073928021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122095853225006049285347 16683143779837509073928021)
              ·
                refine ⟨97752795584985404730047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16683143779837509073928021 97752795584985404730047)
                ·
                  rfl

theorem cell22_2570034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_2570034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570034 prefixEnd_2570034 := by exact prefixLift 2570034
  have htrace : WordTrace (prefixWord ++ tailWord_2570034) baseStart_2570034 baseEnd_2570034 := by
    simpa [prefixWord, tailWord_2570034, baseEnd_2570034] using wordTrace_append hprefix tailTrace_2570034
  have hstable : (prefixWord ++ tailWord_2570034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570034).length < 2 ^ (prefixWord ++ tailWord_2570034).sum := by decide
  have hdescent : baseEnd_2570034 < baseStart_2570034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570124 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_2570124 : Nat := 118140960795 + 2570124 * 2 ^ 59
def prefixEnd_2570124 : Nat := 4983230072969 + 3 ^ 40 * 2570124 * 2
def baseEnd_2570124 : Nat := 293268656368046135940049

theorem tailTrace_2570124 : CollatzResearch.WordTrace tailWord_2570124 prefixEnd_2570124 293268656368046135940049 := by
  unfold tailWord_2570124
  simp only [CollatzResearch.WordTrace]
  refine ⟨46870061670443582539166713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62493415560591443385555617 46870061670443582539166713)
  ·
    refine ⟨35152546252832686904375035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46870061670443582539166713 35152546252832686904375035)
    ·
      refine ⟨52728819379249030356562553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35152546252832686904375035 52728819379249030356562553)
      ·
        refine ⟨39546614534436772767421915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52728819379249030356562553 39546614534436772767421915)
        ·
          refine ⟨59319921801655159151132873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39546614534436772767421915 59319921801655159151132873)
          ·
            refine ⟨44489941351241369363349655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59319921801655159151132873 44489941351241369363349655)
            ·
              refine ⟨66734912026862054045024483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44489941351241369363349655 66734912026862054045024483)
              ·
                refine ⟨100102368040293081067536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66734912026862054045024483 100102368040293081067536725)
                ·
                  refine ⟨293268656368046135940049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100102368040293081067536725 293268656368046135940049)
                  ·
                    rfl

theorem cell22_2570124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_2570124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570124 prefixEnd_2570124 := by exact prefixLift 2570124
  have htrace : WordTrace (prefixWord ++ tailWord_2570124) baseStart_2570124 baseEnd_2570124 := by
    simpa [prefixWord, tailWord_2570124, baseEnd_2570124] using wordTrace_append hprefix tailTrace_2570124
  have hstable : (prefixWord ++ tailWord_2570124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570124).length < 2 ^ (prefixWord ++ tailWord_2570124).sum := by decide
  have hdescent : baseEnd_2570124 < baseStart_2570124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570130 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_2570130 : Nat := 118140960795 + 2570130 * 2 ^ 59
def prefixEnd_2570130 : Nat := 4983230072969 + 3 ^ 40 * 2570130 * 2
def baseEnd_2570130 : Nat := 293269341008918797390043

theorem tailTrace_2570130 : CollatzResearch.WordTrace tailWord_2570130 prefixEnd_2570130 293269341008918797390043 := by
  unfold tailWord_2570130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435085544716357025762961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62493561452576952068701229 23435085544716357025762961)
  ·
    refine ⟨17576314158537267769322221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23435085544716357025762961 17576314158537267769322221)
    ·
      refine ⟨6591117809451475413495833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17576314158537267769322221 6591117809451475413495833)
      ·
        refine ⟨4943338357088606560121875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6591117809451475413495833 4943338357088606560121875)
        ·
          refine ⟨7415007535632909840182813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943338357088606560121875 7415007535632909840182813)
          ·
            refine ⟨2780627825862341190068555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7415007535632909840182813 2780627825862341190068555)
            ·
              refine ⟨4170941738793511785102833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780627825862341190068555 4170941738793511785102833)
              ·
                refine ⟨3128206304095133838827125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4170941738793511785102833 3128206304095133838827125)
                ·
                  refine ⟨293269341008918797390043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128206304095133838827125 293269341008918797390043)
                  ·
                    rfl

theorem cell22_2570130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_2570130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570130 prefixEnd_2570130 := by exact prefixLift 2570130
  have htrace : WordTrace (prefixWord ++ tailWord_2570130) baseStart_2570130 baseEnd_2570130 := by
    simpa [prefixWord, tailWord_2570130, baseEnd_2570130] using wordTrace_append hprefix tailTrace_2570130
  have hstable : (prefixWord ++ tailWord_2570130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570130).length < 2 ^ (prefixWord ++ tailWord_2570130).sum := by decide
  have hdescent : baseEnd_2570130 < baseStart_2570130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570134 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2570134 : Nat := 118140960795 + 2570134 * 2 ^ 59
def prefixEnd_2570134 : Nat := 4983230072969 + 3 ^ 40 * 2570134 * 2
def baseEnd_2570134 : Nat := 879809392308501715070117

theorem tailTrace_2570134 : CollatzResearch.WordTrace tailWord_2570134 prefixEnd_2570134 879809392308501715070117 := by
  unfold tailWord_2570134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858780504428183549137341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62493658713900624524131637 5858780504428183549137341)
  ·
    refine ⟨2197042689160568830926503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5858780504428183549137341 2197042689160568830926503)
    ·
      refine ⟨3295564033740853246389755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197042689160568830926503 3295564033740853246389755)
      ·
        refine ⟨4943346050611279869584633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295564033740853246389755 4943346050611279869584633)
        ·
          refine ⟨3707509537958459902188475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943346050611279869584633 3707509537958459902188475)
          ·
            refine ⟨5561264306937689853282713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707509537958459902188475 5561264306937689853282713)
            ·
              refine ⟨4170948230203267389962035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5561264306937689853282713 4170948230203267389962035)
              ·
                refine ⟨6256422345304901084943053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170948230203267389962035 6256422345304901084943053)
                ·
                  refine ⟨2346158379489337906853645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6256422345304901084943053 2346158379489337906853645)
                  ·
                    refine ⟨879809392308501715070117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346158379489337906853645 879809392308501715070117)
                    ·
                      rfl

theorem cell22_2570134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2570134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570134 prefixEnd_2570134 := by exact prefixLift 2570134
  have htrace : WordTrace (prefixWord ++ tailWord_2570134) baseStart_2570134 baseEnd_2570134 := by
    simpa [prefixWord, tailWord_2570134, baseEnd_2570134] using wordTrace_append hprefix tailTrace_2570134
  have hstable : (prefixWord ++ tailWord_2570134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570134).length < 2 ^ (prefixWord ++ tailWord_2570134).sum := by decide
  have hdescent : baseEnd_2570134 < baseStart_2570134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570141 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2570141 : Nat := 118140960795 + 2570141 * 2 ^ 59
def prefixEnd_2570141 : Nat := 4983230072969 + 3 ^ 40 * 2570141 * 2
def baseEnd_2570141 : Nat := 293270596183852010048365

theorem tailTrace_2570141 : CollatzResearch.WordTrace tailWord_2570141 prefixEnd_2570141 293270596183852010048365 := by
  unfold tailWord_2570141
  simp only [CollatzResearch.WordTrace]
  refine ⟨93740743381825576981702277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62493828921217051321134851 93740743381825576981702277)
  ·
    refine ⟨17576389384092295684069177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93740743381825576981702277 17576389384092295684069177)
    ·
      refine ⟨13182292038069221763051883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17576389384092295684069177 13182292038069221763051883)
      ·
        refine ⟨19773438057103832644577825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13182292038069221763051883 19773438057103832644577825)
        ·
          refine ⟨14830078542827874483433369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19773438057103832644577825 14830078542827874483433369)
          ·
            refine ⟨11122558907120905862575027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14830078542827874483433369 11122558907120905862575027)
            ·
              refine ⟨16683838360681358793862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122558907120905862575027 16683838360681358793862541)
              ·
                refine ⟨6256439385255509547698453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16683838360681358793862541 6256439385255509547698453)
                ·
                  refine ⟨293270596183852010048365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6256439385255509547698453 293270596183852010048365)
                  ·
                    rfl

theorem cell22_2570141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2570141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570141 prefixEnd_2570141 := by exact prefixLift 2570141
  have htrace : WordTrace (prefixWord ++ tailWord_2570141) baseStart_2570141 baseEnd_2570141 := by
    simpa [prefixWord, tailWord_2570141, baseEnd_2570141] using wordTrace_append hprefix tailTrace_2570141
  have hstable : (prefixWord ++ tailWord_2570141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570141).length < 2 ^ (prefixWord ++ tailWord_2570141).sum := by decide
  have hdescent : baseEnd_2570141 < baseStart_2570141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570156 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_2570156 : Nat := 118140960795 + 2570156 * 2 ^ 59
def prefixEnd_2570156 : Nat := 4983230072969 + 3 ^ 40 * 2570156 * 2
def baseEnd_2570156 : Nat := 879816923358100991020049

theorem tailTrace_2570156 : CollatzResearch.WordTrace tailWord_2570156 prefixEnd_2570156 879816923358100991020049 := by
  unfold tailWord_2570156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46870645238385617271749161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62494193651180823028998881 46870645238385617271749161)
  ·
    refine ⟨35152983928789212953811871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46870645238385617271749161 35152983928789212953811871)
    ·
      refine ⟨52729475893183819430717807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35152983928789212953811871 52729475893183819430717807)
      ·
        refine ⟨79094213839775729146076711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52729475893183819430717807 79094213839775729146076711)
        ·
          refine ⟨118641320759663593719115067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79094213839775729146076711 118641320759663593719115067)
          ·
            refine ⟨177961981139495390578672601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118641320759663593719115067 177961981139495390578672601)
            ·
              refine ⟨133471485854621542934004451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177961981139495390578672601 133471485854621542934004451)
              ·
                refine ⟨200207228781932314401006677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133471485854621542934004451 200207228781932314401006677)
                ·
                  refine ⟨2346178462288269309386797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 200207228781932314401006677 2346178462288269309386797)
                  ·
                    refine ⟨879816923358100991020049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346178462288269309386797 879816923358100991020049)
                    ·
                      rfl

theorem cell22_2570156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_2570156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570156 prefixEnd_2570156 := by exact prefixLift 2570156
  have htrace : WordTrace (prefixWord ++ tailWord_2570156) baseStart_2570156 baseEnd_2570156 := by
    simpa [prefixWord, tailWord_2570156, baseEnd_2570156] using wordTrace_append hprefix tailTrace_2570156
  have hstable : (prefixWord ++ tailWord_2570156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570156).length < 2 ^ (prefixWord ++ tailWord_2570156).sum := by decide
  have hdescent : baseEnd_2570156 < baseStart_2570156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570173 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_2570173 : Nat := 118140960795 + 2570173 * 2 ^ 59
def prefixEnd_2570173 : Nat := 4983230072969 + 3 ^ 40 * 2570173 * 2
def baseEnd_2570173 : Nat := 879822742805518613344997

theorem tailTrace_2570173 : CollatzResearch.WordTrace tailWord_2570173 prefixEnd_2570173 879822742805518613344997 := by
  unfold tailWord_2570173
  simp only [CollatzResearch.WordTrace]
  refine ⟨93741910517709646446867173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62494607011806430964578115 93741910517709646446867173)
  ·
    refine ⟨17576608222070558708787595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93741910517709646446867173 17576608222070558708787595)
    ·
      refine ⟨26364912333105838063181393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17576608222070558708787595 26364912333105838063181393)
      ·
        refine ⟨19773684249829378547386045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26364912333105838063181393 19773684249829378547386045)
        ·
          refine ⟨7415131593686016955269767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19773684249829378547386045 7415131593686016955269767)
          ·
            refine ⟨11122697390529025432904651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415131593686016955269767 11122697390529025432904651)
            ·
              refine ⟨16684046085793538149356977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122697390529025432904651 16684046085793538149356977)
              ·
                refine ⟨12513034564345153612017733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16684046085793538149356977 12513034564345153612017733)
                ·
                  refine ⟨2346193980814716302253325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12513034564345153612017733 2346193980814716302253325)
                  ·
                    refine ⟨879822742805518613344997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346193980814716302253325 879822742805518613344997)
                    ·
                      rfl

theorem cell22_2570173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_2570173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570173 prefixEnd_2570173 := by exact prefixLift 2570173
  have htrace : WordTrace (prefixWord ++ tailWord_2570173) baseStart_2570173 baseEnd_2570173 := by
    simpa [prefixWord, tailWord_2570173, baseEnd_2570173] using wordTrace_append hprefix tailTrace_2570173
  have hstable : (prefixWord ++ tailWord_2570173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570173).length < 2 ^ (prefixWord ++ tailWord_2570173).sum := by decide
  have hdescent : baseEnd_2570173 < baseStart_2570173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570188 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2570188 : Nat := 118140960795 + 2570188 * 2 ^ 59
def prefixEnd_2570188 : Nat := 4983230072969 + 3 ^ 40 * 2570188 * 2
def baseEnd_2570188 : Nat := 879827877612063574219951

theorem tailTrace_2570188 : CollatzResearch.WordTrace tailWord_2570188 prefixEnd_2570188 879827877612063574219951 := by
  unfold tailWord_2570188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46871228806327652004331609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62494971741770202672442145 46871228806327652004331609)
  ·
    refine ⟨35153421604745739003248707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46871228806327652004331609 35153421604745739003248707)
    ·
      refine ⟨52730132407118608504873061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35153421604745739003248707 52730132407118608504873061)
      ·
        refine ⟨9886899826334739094663699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52730132407118608504873061 9886899826334739094663699)
        ·
          refine ⟨14830349739502108641995549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886899826334739094663699 14830349739502108641995549)
          ·
            refine ⟨5561381152313290740748331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14830349739502108641995549 5561381152313290740748331)
            ·
              refine ⟨8342071728469936111122497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561381152313290740748331 8342071728469936111122497)
              ·
                refine ⟨6256553796352452083341873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8342071728469936111122497 6256553796352452083341873)
                ·
                  refine ⟨4692415347264339062506405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6256553796352452083341873 4692415347264339062506405)
                  ·
                    refine ⟨879827877612063574219951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692415347264339062506405 879827877612063574219951)
                    ·
                      rfl

theorem cell22_2570188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2570188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570188 prefixEnd_2570188 := by exact prefixLift 2570188
  have htrace : WordTrace (prefixWord ++ tailWord_2570188) baseStart_2570188 baseEnd_2570188 := by
    simpa [prefixWord, tailWord_2570188, baseEnd_2570188] using wordTrace_append hprefix tailTrace_2570188
  have hstable : (prefixWord ++ tailWord_2570188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570188).length < 2 ^ (prefixWord ++ tailWord_2570188).sum := by decide
  have hdescent : baseEnd_2570188 < baseStart_2570188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570207 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 2, 3]
def baseStart_2570207 : Nat := 118140960795 + 2570207 * 2 ^ 59
def prefixEnd_2570207 : Nat := 4983230072969 + 3 ^ 40 * 2570207 * 2
def baseEnd_2570207 : Nat := 879834381700353857994893

theorem tailTrace_2570207 : CollatzResearch.WordTrace tailWord_2570207 prefixEnd_2570207 879834381700353857994893 := by
  unfold tailWord_2570207
  simp only [CollatzResearch.WordTrace]
  refine ⟨93743150599586470253604875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62495433733057646835736583 93743150599586470253604875)
  ·
    refine ⟨140614725899379705380407313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93743150599586470253604875 140614725899379705380407313)
    ·
      refine ⟨105461044424534779035305485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140614725899379705380407313 105461044424534779035305485)
      ·
        refine ⟨39547891659200542138239557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105461044424534779035305485 39547891659200542138239557)
        ·
          refine ⟨7415229686100101650919917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39547891659200542138239557 7415229686100101650919917)
          ·
            refine ⟨2780711132287538119094969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7415229686100101650919917 2780711132287538119094969)
            ·
              refine ⟨2085533349215653589321227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780711132287538119094969 2085533349215653589321227)
              ·
                refine ⟨3128300023823480383981841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085533349215653589321227 3128300023823480383981841)
                ·
                  refine ⟨2346225017867610287986381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128300023823480383981841 2346225017867610287986381)
                  ·
                    refine ⟨879834381700353857994893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346225017867610287986381 879834381700353857994893)
                    ·
                      rfl

theorem cell22_2570207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_2570207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570207 prefixEnd_2570207 := by exact prefixLift 2570207
  have htrace : WordTrace (prefixWord ++ tailWord_2570207) baseStart_2570207 baseEnd_2570207 := by
    simpa [prefixWord, tailWord_2570207, baseEnd_2570207] using wordTrace_append hprefix tailTrace_2570207
  have hstable : (prefixWord ++ tailWord_2570207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570207).length < 2 ^ (prefixWord ++ tailWord_2570207).sum := by decide
  have hdescent : baseEnd_2570207 < baseStart_2570207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570218 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2570218 : Nat := 118140960795 + 2570218 * 2 ^ 59
def prefixEnd_2570218 : Nat := 4983230072969 + 3 ^ 40 * 2570218 * 2
def baseEnd_2570218 : Nat := 879838147225153495969859

theorem tailTrace_2570218 : CollatzResearch.WordTrace tailWord_2570218 prefixEnd_2570218 879838147225153495969859 := by
  unfold tailWord_2570218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435887950636654783063827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62495701201697746088170205 23435887950636654783063827)
  ·
    refine ⟨35153831925954982174595741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23435887950636654783063827 35153831925954982174595741)
    ·
      refine ⟨13182686972233118315473403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35153831925954982174595741 13182686972233118315473403)
      ·
        refine ⟨19774030458349677473210105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13182686972233118315473403 19774030458349677473210105)
        ·
          refine ⟨14830522843762258104907579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19774030458349677473210105 14830522843762258104907579)
          ·
            refine ⟨22245784265643387157361369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14830522843762258104907579 22245784265643387157361369)
            ·
              refine ⟨16684338199232540368021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22245784265643387157361369 16684338199232540368021027)
              ·
                refine ⟨25026507298848810552031541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16684338199232540368021027 25026507298848810552031541)
                ·
                  refine ⟨2346235059267075989252957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25026507298848810552031541 2346235059267075989252957)
                  ·
                    refine ⟨879838147225153495969859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346235059267075989252957 879838147225153495969859)
                    ·
                      rfl

theorem cell22_2570218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2570218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570218 prefixEnd_2570218 := by exact prefixLift 2570218
  have htrace : WordTrace (prefixWord ++ tailWord_2570218) baseStart_2570218 baseEnd_2570218 := by
    simpa [prefixWord, tailWord_2570218, baseEnd_2570218] using wordTrace_append hprefix tailTrace_2570218
  have hstable : (prefixWord ++ tailWord_2570218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570218).length < 2 ^ (prefixWord ++ tailWord_2570218).sum := by decide
  have hdescent : baseEnd_2570218 < baseStart_2570218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570248 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_2570248 : Nat := 118140960795 + 2570248 * 2 ^ 59
def prefixEnd_2570248 : Nat := 4983230072969 + 3 ^ 40 * 2570248 * 2
def baseEnd_2570248 : Nat := 293282805612747805906589

theorem tailTrace_2570248 : CollatzResearch.WordTrace tailWord_2570248 prefixEnd_2570248 293282805612747805906589 := by
  unfold tailWord_2570248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46872322996218967127923699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62496430661625289503898265 46872322996218967127923699)
  ·
    refine ⟨70308484494328450691885549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46872322996218967127923699 70308484494328450691885549)
    ·
      refine ⟨26365681685373169009457081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70308484494328450691885549 26365681685373169009457081)
      ·
        refine ⟨19774261264029876757092811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26365681685373169009457081 19774261264029876757092811)
        ·
          refine ⟨29661391896044815135639217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19774261264029876757092811 29661391896044815135639217)
          ·
            refine ⟨22246043922033611351729413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29661391896044815135639217 22246043922033611351729413)
            ·
              refine ⟨4171133235381302128449265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22246043922033611351729413 4171133235381302128449265)
              ·
                refine ⟨3128349926535976596336949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171133235381302128449265 3128349926535976596336949)
                ·
                  refine ⟨293282805612747805906589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128349926535976596336949 293282805612747805906589)
                  ·
                    rfl

theorem cell22_2570248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_2570248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570248 prefixEnd_2570248 := by exact prefixLift 2570248
  have htrace : WordTrace (prefixWord ++ tailWord_2570248) baseStart_2570248 baseEnd_2570248 := by
    simpa [prefixWord, tailWord_2570248, baseEnd_2570248] using wordTrace_append hprefix tailTrace_2570248
  have hstable : (prefixWord ++ tailWord_2570248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570248).length < 2 ^ (prefixWord ++ tailWord_2570248).sum := by decide
  have hdescent : baseEnd_2570248 < baseStart_2570248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570295 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 1, 4]
def baseStart_2570295 : Nat := 118140960795 + 2570295 * 2 ^ 59
def prefixEnd_2570295 : Nat := 4983230072969 + 3 ^ 40 * 2570295 * 2
def baseEnd_2570295 : Nat := 879864505898750961794623

theorem tailTrace_2570295 : CollatzResearch.WordTrace tailWord_2570295 prefixEnd_2570295 879864505898750961794623 := by
  unfold tailWord_2570295
  simp only [CollatzResearch.WordTrace]
  refine ⟨93746360223267661282808339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62497573482178440855205559 93746360223267661282808339)
  ·
    refine ⟨140619540334901491924212509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93746360223267661282808339 140619540334901491924212509)
    ·
      refine ⟨52732327625588059471579691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140619540334901491924212509 52732327625588059471579691)
      ·
        refine ⟨79098491438382089207369537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52732327625588059471579691 79098491438382089207369537)
        ·
          refine ⟨59323868578786566905527153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79098491438382089207369537 59323868578786566905527153)
          ·
            refine ⟨44492901434089925179145365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59323868578786566905527153 44492901434089925179145365)
            ·
              refine ⟨2085604754722965242772439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44492901434089925179145365 2085604754722965242772439)
              ·
                refine ⟨3128407132084447864158659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085604754722965242772439 3128407132084447864158659)
                ·
                  refine ⟨4692610698126671796237989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128407132084447864158659 4692610698126671796237989)
                  ·
                    refine ⟨879864505898750961794623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692610698126671796237989 879864505898750961794623)
                    ·
                      rfl

theorem cell22_2570295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_2570295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570295 prefixEnd_2570295 := by exact prefixLift 2570295
  have htrace : WordTrace (prefixWord ++ tailWord_2570295) baseStart_2570295 baseEnd_2570295 := by
    simpa [prefixWord, tailWord_2570295, baseEnd_2570295] using wordTrace_append hprefix tailTrace_2570295
  have hstable : (prefixWord ++ tailWord_2570295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570295).length < 2 ^ (prefixWord ++ tailWord_2570295).sum := by decide
  have hdescent : baseEnd_2570295 < baseStart_2570295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570321 : List Nat := [1, 2, 2, 1, 3, 1, 1, 11]
def baseStart_2570321 : Nat := 118140960795 + 2570321 * 2 ^ 59
def prefixEnd_2570321 : Nat := 4983230072969 + 3 ^ 40 * 2570321 * 2
def baseEnd_2570321 : Nat := 97763711803343951182727

theorem tailTrace_2570321 : CollatzResearch.WordTrace tailWord_2570321 prefixEnd_2570321 97763711803343951182727 := by
  unfold tailWord_2570321
  simp only [CollatzResearch.WordTrace]
  refine ⟨93747308521173467723254817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62498205680782311815503211 93747308521173467723254817)
  ·
    refine ⟨70310481390880100792441113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93747308521173467723254817 70310481390880100792441113)
    ·
      refine ⟨52732861043160075594330835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70310481390880100792441113 52732861043160075594330835)
      ·
        refine ⟨79099291564740113391496253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52732861043160075594330835 79099291564740113391496253)
        ·
          refine ⟨29662234336777542521811095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79099291564740113391496253 29662234336777542521811095)
          ·
            refine ⟨44493351505166313782716643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29662234336777542521811095 44493351505166313782716643)
            ·
              refine ⟨66740027257749470674074965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44493351505166313782716643 66740027257749470674074965)
              ·
                refine ⟨97763711803343951182727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66740027257749470674074965 97763711803343951182727)
                ·
                  rfl

theorem cell22_2570321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 11].length) (baseStart_2570321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570321 prefixEnd_2570321 := by exact prefixLift 2570321
  have htrace : WordTrace (prefixWord ++ tailWord_2570321) baseStart_2570321 baseEnd_2570321 := by
    simpa [prefixWord, tailWord_2570321, baseEnd_2570321] using wordTrace_append hprefix tailTrace_2570321
  have hstable : (prefixWord ++ tailWord_2570321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570321).length < 2 ^ (prefixWord ++ tailWord_2570321).sum := by decide
  have hdescent : baseEnd_2570321 < baseStart_2570321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570325 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2570325 : Nat := 118140960795 + 2570325 * 2 ^ 59
def prefixEnd_2570325 : Nat := 4983230072969 + 3 ^ 40 * 2570325 * 2
def baseEnd_2570325 : Nat := 879874775511840883544531

theorem tailTrace_2570325 : CollatzResearch.WordTrace tailWord_2570325 prefixEnd_2570325 879874775511840883544531 := by
  unfold tailWord_2570325
  simp only [CollatzResearch.WordTrace]
  refine ⟨93747454413158976406400429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62498302942105984270933619 93747454413158976406400429)
  ·
    refine ⟨35155295404934616152400161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93747454413158976406400429 35155295404934616152400161)
    ·
      refine ⟨26366471553700962114300121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35155295404934616152400161 26366471553700962114300121)
      ·
        refine ⟨19774853665275721585725091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26366471553700962114300121 19774853665275721585725091)
        ·
          refine ⟨29662280497913582378587637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19774853665275721585725091 29662280497913582378587637)
          ·
            refine ⟨2780838796679398347992591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29662280497913582378587637 2780838796679398347992591)
            ·
              refine ⟨4171258195019097521988887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780838796679398347992591 4171258195019097521988887)
              ·
                refine ⟨6256887292528646282983331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171258195019097521988887 6256887292528646282983331)
                ·
                  refine ⟨9385330938792969424474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6256887292528646282983331 9385330938792969424474997)
                  ·
                    refine ⟨879874775511840883544531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9385330938792969424474997 879874775511840883544531)
                    ·
                      rfl

theorem cell22_2570325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2570325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570325 prefixEnd_2570325 := by exact prefixLift 2570325
  have htrace : WordTrace (prefixWord ++ tailWord_2570325) baseStart_2570325 baseEnd_2570325 := by
    simpa [prefixWord, tailWord_2570325, baseEnd_2570325] using wordTrace_append hprefix tailTrace_2570325
  have hstable : (prefixWord ++ tailWord_2570325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570325).length < 2 ^ (prefixWord ++ tailWord_2570325).sum := by decide
  have hdescent : baseEnd_2570325 < baseStart_2570325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570417 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 5]
def baseStart_2570417 : Nat := 118140960795 + 2570417 * 2 ^ 59
def prefixEnd_2570417 : Nat := 4983230072969 + 3 ^ 40 * 2570417 * 2
def baseEnd_2570417 : Nat := 293302089663994436748083

theorem tailTrace_2570417 : CollatzResearch.WordTrace tailWord_2570417 prefixEnd_2570417 293302089663994436748083 := by
  unfold tailWord_2570417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93750809928825676118749505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62500539952550450745833003 93750809928825676118749505)
  ·
    refine ⟨70313107446619257089062129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93750809928825676118749505 70313107446619257089062129)
    ·
      refine ⟨52734830584964442816796597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70313107446619257089062129 52734830584964442816796597)
      ·
        refine ⟨4943890367340416514074681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52734830584964442816796597 4943890367340416514074681)
        ·
          refine ⟨3707917775505312385556011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943890367340416514074681 3707917775505312385556011)
          ·
            refine ⟨5561876663257968578334017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707917775505312385556011 5561876663257968578334017)
            ·
              refine ⟨4171407497443476433750513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5561876663257968578334017 4171407497443476433750513)
              ·
                refine ⟨3128555623082607325312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171407497443476433750513 3128555623082607325312885)
                ·
                  refine ⟨293302089663994436748083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128555623082607325312885 293302089663994436748083)
                  ·
                    rfl

theorem cell22_2570417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_2570417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570417 prefixEnd_2570417 := by exact prefixLift 2570417
  have htrace : WordTrace (prefixWord ++ tailWord_2570417) baseStart_2570417 baseEnd_2570417 := by
    simpa [prefixWord, tailWord_2570417, baseEnd_2570417] using wordTrace_append hprefix tailTrace_2570417
  have hstable : (prefixWord ++ tailWord_2570417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570417).length < 2 ^ (prefixWord ++ tailWord_2570417).sum := by decide
  have hdescent : baseEnd_2570417 < baseStart_2570417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570421 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2570421 : Nat := 118140960795 + 2570421 * 2 ^ 59
def prefixEnd_2570421 : Nat := 4983230072969 + 3 ^ 40 * 2570421 * 2
def baseEnd_2570421 : Nat := 879907638273728633144237

theorem tailTrace_2570421 : CollatzResearch.WordTrace tailWord_2570421 prefixEnd_2570421 879907638273728633144237 := by
  unfold tailWord_2570421
  simp only [CollatzResearch.WordTrace]
  refine ⟨93750955820811184801895117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62500637213874123201263411 93750955820811184801895117)
  ·
    refine ⟨35156608432804194300710669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93750955820811184801895117 35156608432804194300710669)
    ·
      refine ⟨13183728162301572862766501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35156608432804194300710669 13183728162301572862766501)
      ·
        refine ⟨2471949030431544911768719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13183728162301572862766501 2471949030431544911768719)
        ·
          refine ⟨3707923545647317367653079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471949030431544911768719 3707923545647317367653079)
          ·
            refine ⟨5561885318470976051479619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707923545647317367653079 5561885318470976051479619)
            ·
              refine ⟨8342827977706464077219429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561885318470976051479619 8342827977706464077219429)
              ·
                refine ⟨1564280245819962014478643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8342827977706464077219429 1564280245819962014478643)
                ·
                  refine ⟨2346420368729943021717965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564280245819962014478643 2346420368729943021717965)
                  ·
                    refine ⟨879907638273728633144237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346420368729943021717965 879907638273728633144237)
                    ·
                      rfl

theorem cell22_2570421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2570421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570421 prefixEnd_2570421 := by exact prefixLift 2570421
  have htrace : WordTrace (prefixWord ++ tailWord_2570421) baseStart_2570421 baseEnd_2570421 := by
    simpa [prefixWord, tailWord_2570421, baseEnd_2570421] using wordTrace_append hprefix tailTrace_2570421
  have hstable : (prefixWord ++ tailWord_2570421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570421).length < 2 ^ (prefixWord ++ tailWord_2570421).sum := by decide
  have hdescent : baseEnd_2570421 < baseStart_2570421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570434 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2570434 : Nat := 118140960795 + 2570434 * 2 ^ 59
def prefixEnd_2570434 : Nat := 4983230072969 + 3 ^ 40 * 2570434 * 2
def baseEnd_2570434 : Nat := 293304029479800310856399

theorem tailTrace_2570434 : CollatzResearch.WordTrace tailWord_2570434 prefixEnd_2570434 293304029479800310856399 := by
  unfold tailWord_2570434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23437857492441022005529589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62500953313176058681412237 23437857492441022005529589)
  ·
    refine ⟨2197299139916345813018399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23437857492441022005529589 2197299139916345813018399)
    ·
      refine ⟨3295948709874518719527599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197299139916345813018399 3295948709874518719527599)
      ·
        refine ⟨4943923064811778079291399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295948709874518719527599 4943923064811778079291399)
        ·
          refine ⟨7415884597217667118937099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943923064811778079291399 7415884597217667118937099)
          ·
            refine ⟨11123826895826500678405649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415884597217667118937099 11123826895826500678405649)
            ·
              refine ⟨8342870171869875508804237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11123826895826500678405649 8342870171869875508804237)
              ·
                refine ⟨3128576314451203315801589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8342870171869875508804237 3128576314451203315801589)
                ·
                  refine ⟨293304029479800310856399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128576314451203315801589 293304029479800310856399)
                  ·
                    rfl

theorem cell22_2570434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2570434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570434 prefixEnd_2570434 := by exact prefixLift 2570434
  have htrace : WordTrace (prefixWord ++ tailWord_2570434) baseStart_2570434 baseEnd_2570434 := by
    simpa [prefixWord, tailWord_2570434, baseEnd_2570434] using wordTrace_append hprefix tailTrace_2570434
  have hstable : (prefixWord ++ tailWord_2570434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570434).length < 2 ^ (prefixWord ++ tailWord_2570434).sum := by decide
  have hdescent : baseEnd_2570434 < baseStart_2570434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570552 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_2570552 : Nat := 118140960795 + 2570552 * 2 ^ 59
def prefixEnd_2570552 : Nat := 4983230072969 + 3 ^ 40 * 2570552 * 2
def baseEnd_2570552 : Nat := 293317494083629319372945

theorem tailTrace_2570552 : CollatzResearch.WordTrace tailWord_2570552 prefixEnd_2570552 293317494083629319372945 := by
  unfold tailWord_2570552
  simp only [CollatzResearch.WordTrace]
  refine ⟨46877866891668297087456955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62503822522224396116609273 46877866891668297087456955)
  ·
    refine ⟨70316800337502445631185433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46877866891668297087456955 70316800337502445631185433)
    ·
      refine ⟨52737600253126834223389075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70316800337502445631185433 52737600253126834223389075)
      ·
        refine ⟨79106400379690251335083613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52737600253126834223389075 79106400379690251335083613)
        ·
          refine ⟨29664900142383844250656355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79106400379690251335083613 29664900142383844250656355)
          ·
            refine ⟨44497350213575766375984533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29664900142383844250656355 44497350213575766375984533)
            ·
              refine ⟨2085813291261364048874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44497350213575766375984533 2085813291261364048874275)
              ·
                refine ⟨3128719936892046073311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085813291261364048874275 3128719936892046073311413)
                ·
                  refine ⟨293317494083629319372945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128719936892046073311413 293317494083629319372945)
                  ·
                    rfl

theorem cell22_2570552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_2570552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570552 prefixEnd_2570552 := by exact prefixLift 2570552
  have htrace : WordTrace (prefixWord ++ tailWord_2570552) baseStart_2570552 baseEnd_2570552 := by
    simpa [prefixWord, tailWord_2570552, baseEnd_2570552] using wordTrace_append hprefix tailTrace_2570552
  have hstable : (prefixWord ++ tailWord_2570552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570552).length < 2 ^ (prefixWord ++ tailWord_2570552).sum := by decide
  have hdescent : baseEnd_2570552 < baseStart_2570552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570595 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_2570595 : Nat := 118140960795 + 2570595 * 2 ^ 59
def prefixEnd_2570595 : Nat := 4983230072969 + 3 ^ 40 * 2570595 * 2
def baseEnd_2570595 : Nat := 879967202029650179293703

theorem tailTrace_2570595 : CollatzResearch.WordTrace tailWord_2570595 prefixEnd_2570595 879967202029650179293703 := by
  unfold tailWord_2570595
  simp only [CollatzResearch.WordTrace]
  refine ⟨93757302122180812518729239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62504868081453875012486159 93757302122180812518729239)
  ·
    refine ⟨140635953183271218778093859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93757302122180812518729239 140635953183271218778093859)
    ·
      refine ⟨210953929774906828167140789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140635953183271218778093859 210953929774906828167140789)
      ·
        refine ⟨19776930916397515140669449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210953929774906828167140789 19776930916397515140669449)
        ·
          refine ⟨14832698187298136355502087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19776930916397515140669449 14832698187298136355502087)
          ·
            refine ⟨22249047280947204533253131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14832698187298136355502087 22249047280947204533253131)
            ·
              refine ⟨33373570921420806799879697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22249047280947204533253131 33373570921420806799879697)
              ·
                refine ⟨25030178191065605099909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33373570921420806799879697 25030178191065605099909773)
                ·
                  refine ⟨9386316821649601912466165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25030178191065605099909773 9386316821649601912466165)
                  ·
                    refine ⟨879967202029650179293703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9386316821649601912466165 879967202029650179293703)
                    ·
                      rfl

theorem cell22_2570595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_2570595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570595 prefixEnd_2570595 := by exact prefixLift 2570595
  have htrace : WordTrace (prefixWord ++ tailWord_2570595) baseStart_2570595 baseEnd_2570595 := by
    simpa [prefixWord, tailWord_2570595, baseEnd_2570595] using wordTrace_append hprefix tailTrace_2570595
  have hstable : (prefixWord ++ tailWord_2570595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570595).length < 2 ^ (prefixWord ++ tailWord_2570595).sum := by decide
  have hdescent : baseEnd_2570595 < baseStart_2570595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570627 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_2570627 : Nat := 118140960795 + 2570627 * 2 ^ 59
def prefixEnd_2570627 : Nat := 4983230072969 + 3 ^ 40 * 2570627 * 2
def baseEnd_2570627 : Nat := 879978156283612762493605

theorem tailTrace_2570627 : CollatzResearch.WordTrace tailWord_2570627 prefixEnd_2570627 879978156283612762493605 := by
  unfold tailWord_2570627
  simp only [CollatzResearch.WordTrace]
  refine ⟨93758469258064881983894135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62505646172043254655929423 93758469258064881983894135)
  ·
    refine ⟨140637703887097322975841203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93758469258064881983894135 140637703887097322975841203)
    ·
      refine ⟨210956555830645984463761805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140637703887097322975841203 210956555830645984463761805)
      ·
        refine ⟨79108708436492244173910677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210956555830645984463761805 79108708436492244173910677)
        ·
          refine ⟨3708220707960573945652063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79108708436492244173910677 3708220707960573945652063)
          ·
            refine ⟨5562331061940860918478095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708220707960573945652063 5562331061940860918478095)
            ·
              refine ⟨8343496592911291377717143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562331061940860918478095 8343496592911291377717143)
              ·
                refine ⟨12515244889366937066575715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343496592911291377717143 12515244889366937066575715)
                ·
                  refine ⟨18772867334050405599863573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12515244889366937066575715 18772867334050405599863573)
                  ·
                    refine ⟨879978156283612762493605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18772867334050405599863573 879978156283612762493605)
                    ·
                      rfl

theorem cell22_2570627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_2570627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570627 prefixEnd_2570627 := by exact prefixLift 2570627
  have htrace : WordTrace (prefixWord ++ tailWord_2570627) baseStart_2570627 baseEnd_2570627 := by
    simpa [prefixWord, tailWord_2570627, baseEnd_2570627] using wordTrace_append hprefix tailTrace_2570627
  have hstable : (prefixWord ++ tailWord_2570627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570627).length < 2 ^ (prefixWord ++ tailWord_2570627).sum := by decide
  have hdescent : baseEnd_2570627 < baseStart_2570627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570676 : List Nat := [2, 5, 2, 2, 1, 1, 1, 8]
def baseStart_2570676 : Nat := 118140960795 + 2570676 * 2 ^ 59
def prefixEnd_2570676 : Nat := 4983230072969 + 3 ^ 40 * 2570676 * 2
def baseEnd_2570676 : Nat := 97777214442776996446495

theorem tailTrace_2570676 : CollatzResearch.WordTrace tailWord_2570676 prefixEnd_2570676 97777214442776996446495 := by
  unfold tailWord_2570676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46880128217443681676213941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62506837623258242234951921 46880128217443681676213941)
  ·
    refine ⟨4395012020385345157145057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46880128217443681676213941 4395012020385345157145057)
    ·
      refine ⟨3296259015289008867858793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395012020385345157145057 3296259015289008867858793)
      ·
        refine ⟨2472194261466756650894095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296259015289008867858793 2472194261466756650894095)
        ·
          refine ⟨3708291392200134976341143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472194261466756650894095 3708291392200134976341143)
          ·
            refine ⟨5562437088300202464511715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708291392200134976341143 5562437088300202464511715)
            ·
              refine ⟨8343655632450303696767573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562437088300202464511715 8343655632450303696767573)
              ·
                refine ⟨97777214442776996446495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8343655632450303696767573 97777214442776996446495)
                ·
                  rfl

theorem cell22_2570676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_2570676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570676 prefixEnd_2570676 := by exact prefixLift 2570676
  have htrace : WordTrace (prefixWord ++ tailWord_2570676) baseStart_2570676 baseEnd_2570676 := by
    simpa [prefixWord, tailWord_2570676, baseEnd_2570676] using wordTrace_append hprefix tailTrace_2570676
  have hstable : (prefixWord ++ tailWord_2570676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570676).length < 2 ^ (prefixWord ++ tailWord_2570676).sum := by decide
  have hdescent : baseEnd_2570676 < baseStart_2570676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570734 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2570734 : Nat := 118140960795 + 2570734 * 2 ^ 59
def prefixEnd_2570734 : Nat := 4983230072969 + 3 ^ 40 * 2570734 * 2
def baseEnd_2570734 : Nat := 880014784570300150068277

theorem tailTrace_2570734 : CollatzResearch.WordTrace tailWord_2570734 prefixEnd_2570734 880014784570300150068277 := by
  unfold tailWord_2570734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720296483584654907254907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62508247912451492838692837 11720296483584654907254907)
  ·
    refine ⟨17580444725376982360882361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11720296483584654907254907 17580444725376982360882361)
    ·
      refine ⟨13185333544032736770661771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17580444725376982360882361 13185333544032736770661771)
      ·
        refine ⟨19778000316049105155992657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13185333544032736770661771 19778000316049105155992657)
        ·
          refine ⟨14833500237036828866994493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19778000316049105155992657 14833500237036828866994493)
          ·
            refine ⟨5562562588888810825122935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14833500237036828866994493 5562562588888810825122935)
            ·
              refine ⟨8343843883333216237684403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562562588888810825122935 8343843883333216237684403)
              ·
                refine ⟨12515765824999824356526605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343843883333216237684403 12515765824999824356526605)
                ·
                  refine ⟨4693412184374934133697477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12515765824999824356526605 4693412184374934133697477)
                  ·
                    refine ⟨880014784570300150068277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693412184374934133697477 880014784570300150068277)
                    ·
                      rfl

theorem cell22_2570734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2570734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570734 prefixEnd_2570734 := by exact prefixLift 2570734
  have htrace : WordTrace (prefixWord ++ tailWord_2570734) baseStart_2570734 baseEnd_2570734 := by
    simpa [prefixWord, tailWord_2570734, baseEnd_2570734] using wordTrace_append hprefix tailTrace_2570734
  have hstable : (prefixWord ++ tailWord_2570734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570734).length < 2 ^ (prefixWord ++ tailWord_2570734).sum := by decide
  have hdescent : baseEnd_2570734 < baseStart_2570734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570749 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 4]
def baseStart_2570749 : Nat := 118140960795 + 2570749 * 2 ^ 59
def prefixEnd_2570749 : Nat := 4983230072969 + 3 ^ 40 * 2570749 * 2
def baseEnd_2570749 : Nat := 293339973125615036981077

theorem tailTrace_2570749 : CollatzResearch.WordTrace tailWord_2570749 prefixEnd_2570749 293339973125615036981077 := by
  unfold tailWord_2570749
  simp only [CollatzResearch.WordTrace]
  refine ⟨93762918963622896819835301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62508612642415264546556867 93762918963622896819835301)
  ·
    refine ⟨17580547305679293153719119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93762918963622896819835301 17580547305679293153719119)
    ·
      refine ⟨26370820958518939730578679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17580547305679293153719119 26370820958518939730578679)
      ·
        refine ⟨39556231437778409595868019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26370820958518939730578679 39556231437778409595868019)
        ·
          refine ⟨59334347156667614393802029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39556231437778409595868019 59334347156667614393802029)
          ·
            refine ⟨22250380183750355397675761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59334347156667614393802029 22250380183750355397675761)
            ·
              refine ⟨16687785137812766548256821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22250380183750355397675761 16687785137812766548256821)
              ·
                refine ⟨1564479856669946863899077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16687785137812766548256821 1564479856669946863899077)
                ·
                  refine ⟨293339973125615036981077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564479856669946863899077 293339973125615036981077)
                  ·
                    rfl

theorem cell22_2570749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_2570749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570749 prefixEnd_2570749 := by exact prefixLift 2570749
  have htrace : WordTrace (prefixWord ++ tailWord_2570749) baseStart_2570749 baseEnd_2570749 := by
    simpa [prefixWord, tailWord_2570749, baseEnd_2570749] using wordTrace_append hprefix tailTrace_2570749
  have hstable : (prefixWord ++ tailWord_2570749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570749).length < 2 ^ (prefixWord ++ tailWord_2570749).sum := by decide
  have hdescent : baseEnd_2570749 < baseStart_2570749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570766 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_2570766 : Nat := 118140960795 + 2570766 * 2 ^ 59
def prefixEnd_2570766 : Nat := 4983230072969 + 3 ^ 40 * 2570766 * 2
def baseEnd_2570766 : Nat := 293341912941420911089393

theorem tailTrace_2570766 : CollatzResearch.WordTrace tailWord_2570766 prefixEnd_2570766 293341912941420911089393 := by
  unfold tailWord_2570766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720442375570163590400519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62509026003040872482136101 11720442375570163590400519)
  ·
    refine ⟨17580663563355245385600779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11720442375570163590400519 17580663563355245385600779)
    ·
      refine ⟨26370995345032868078401169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17580663563355245385600779 26370995345032868078401169)
      ·
        refine ⟨19778246508774651058800877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26370995345032868078401169 19778246508774651058800877)
        ·
          refine ⟨7416842440790494147050329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19778246508774651058800877 7416842440790494147050329)
          ·
            refine ⟨5562631830592870610287747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7416842440790494147050329 5562631830592870610287747)
            ·
              refine ⟨8343947745889305915431621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562631830592870610287747 8343947745889305915431621)
              ·
                refine ⟨1564490202354244859143429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8343947745889305915431621 1564490202354244859143429)
                ·
                  refine ⟨293341912941420911089393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564490202354244859143429 293341912941420911089393)
                  ·
                    rfl

theorem cell22_2570766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_2570766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570766 prefixEnd_2570766 := by exact prefixLift 2570766
  have htrace : WordTrace (prefixWord ++ tailWord_2570766) baseStart_2570766 baseEnd_2570766 := by
    simpa [prefixWord, tailWord_2570766, baseEnd_2570766] using wordTrace_append hprefix tailTrace_2570766
  have hstable : (prefixWord ++ tailWord_2570766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570766).length < 2 ^ (prefixWord ++ tailWord_2570766).sum := by decide
  have hdescent : baseEnd_2570766 < baseStart_2570766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570781 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2570781 : Nat := 118140960795 + 2570781 * 2 ^ 59
def prefixEnd_2570781 : Nat := 4983230072969 + 3 ^ 40 * 2570781 * 2
def baseEnd_2570781 : Nat := 880030873630807694143133

theorem tailTrace_2570781 : CollatzResearch.WordTrace tailWord_2570781 prefixEnd_2570781 880030873630807694143133 := by
  unfold tailWord_2570781
  simp only [CollatzResearch.WordTrace]
  refine ⟨93764086099506966285000197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62509390733004644190000131 93764086099506966285000197)
  ·
    refine ⟨17580766143657556178437537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93764086099506966285000197 17580766143657556178437537)
    ·
      refine ⟨13185574607743167133828153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17580766143657556178437537 13185574607743167133828153)
      ·
        refine ⟨9889180955807375350371115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13185574607743167133828153 9889180955807375350371115)
        ·
          refine ⟨14833771433711063025556673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889180955807375350371115 14833771433711063025556673)
          ·
            refine ⟨11125328575283297269167505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14833771433711063025556673 11125328575283297269167505)
            ·
              refine ⟨8343996431462472951875629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11125328575283297269167505 8343996431462472951875629)
              ·
                refine ⟨3128998661798427356953361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8343996431462472951875629 3128998661798427356953361)
                ·
                  refine ⟨2346748996348820517715021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128998661798427356953361 2346748996348820517715021)
                  ·
                    refine ⟨880030873630807694143133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346748996348820517715021 880030873630807694143133)
                    ·
                      rfl

theorem cell22_2570781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2570781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570781 prefixEnd_2570781 := by exact prefixLift 2570781
  have htrace : WordTrace (prefixWord ++ tailWord_2570781) baseStart_2570781 baseEnd_2570781 := by
    simpa [prefixWord, tailWord_2570781, baseEnd_2570781] using wordTrace_append hprefix tailTrace_2570781
  have hstable : (prefixWord ++ tailWord_2570781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570781).length < 2 ^ (prefixWord ++ tailWord_2570781).sum := by decide
  have hdescent : baseEnd_2570781 < baseStart_2570781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570809 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_2570809 : Nat := 118140960795 + 2570809 * 2 ^ 59
def prefixEnd_2570809 : Nat := 4983230072969 + 3 ^ 40 * 2570809 * 2
def baseEnd_2570809 : Nat := 880040458603024954443047

theorem tailTrace_2570809 : CollatzResearch.WordTrace tailWord_2570809 prefixEnd_2570809 880040458603024954443047 := by
  unfold tailWord_2570809
  simp only [CollatzResearch.WordTrace]
  refine ⟨93765107343405527067019481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62510071562270351378012987 93765107343405527067019481)
  ·
    refine ⟨70323830507554145300264611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93765107343405527067019481 70323830507554145300264611)
    ·
      refine ⟨105485745761331217950396917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70323830507554145300264611 105485745761331217950396917)
      ·
        refine ⟨9889288665124801682849711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105485745761331217950396917 9889288665124801682849711)
        ·
          refine ⟨14833932997687202524274567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889288665124801682849711 14833932997687202524274567)
          ·
            refine ⟨22250899496530803786411851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833932997687202524274567 22250899496530803786411851)
            ·
              refine ⟨33376349244796205679617777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22250899496530803786411851 33376349244796205679617777)
              ·
                refine ⟨25032261933597154259713333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33376349244796205679617777 25032261933597154259713333)
                ·
                  refine ⟨2346774556274733211848125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25032261933597154259713333 2346774556274733211848125)
                  ·
                    refine ⟨880040458603024954443047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346774556274733211848125 880040458603024954443047)
                    ·
                      rfl

theorem cell22_2570809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_2570809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570809 prefixEnd_2570809 := by exact prefixLift 2570809
  have htrace : WordTrace (prefixWord ++ tailWord_2570809) baseStart_2570809 baseEnd_2570809 := by
    simpa [prefixWord, tailWord_2570809, baseEnd_2570809] using wordTrace_append hprefix tailTrace_2570809
  have hstable : (prefixWord ++ tailWord_2570809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570809).length < 2 ^ (prefixWord ++ tailWord_2570809).sum := by decide
  have hdescent : baseEnd_2570809 < baseStart_2570809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570826 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2570826 : Nat := 118140960795 + 2570826 * 2 ^ 59
def prefixEnd_2570826 : Nat := 4983230072969 + 3 ^ 40 * 2570826 * 2
def baseEnd_2570826 : Nat := 880046278050442576767995

theorem tailTrace_2570826 : CollatzResearch.WordTrace tailWord_2570826 prefixEnd_2570826 880046278050442576767995 := by
  unfold tailWord_2570826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441431846085984742597083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62510484922895959313592221 23441431846085984742597083)
  ·
    refine ⟨35162147769128977113895625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23441431846085984742597083 35162147769128977113895625)
    ·
      refine ⟨26371610826846732835421719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35162147769128977113895625 26371610826846732835421719)
      ·
        refine ⟨39557416240270099253132579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26371610826846732835421719 39557416240270099253132579)
        ·
          refine ⟨59336124360405148879698869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39557416240270099253132579 59336124360405148879698869)
          ·
            refine ⟨5562761658787982707471769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59336124360405148879698869 5562761658787982707471769)
            ·
              refine ⟨4172071244090987030603827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5562761658787982707471769 4172071244090987030603827)
              ·
                refine ⟨6258106866136480545905741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172071244090987030603827 6258106866136480545905741)
                ·
                  refine ⟨2346790074801180204714653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6258106866136480545905741 2346790074801180204714653)
                  ·
                    refine ⟨880046278050442576767995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346790074801180204714653 880046278050442576767995)
                    ·
                      rfl

theorem cell22_2570826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2570826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570826 prefixEnd_2570826 := by exact prefixLift 2570826
  have htrace : WordTrace (prefixWord ++ tailWord_2570826) baseStart_2570826 baseEnd_2570826 := by
    simpa [prefixWord, tailWord_2570826, baseEnd_2570826] using wordTrace_append hprefix tailTrace_2570826
  have hstable : (prefixWord ++ tailWord_2570826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570826).length < 2 ^ (prefixWord ++ tailWord_2570826).sum := by decide
  have hdescent : baseEnd_2570826 < baseStart_2570826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570890 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_2570890 : Nat := 118140960795 + 2570890 * 2 ^ 59
def prefixEnd_2570890 : Nat := 4983230072969 + 3 ^ 40 * 2570890 * 2
def baseEnd_2570890 : Nat := 293356062186122581055933

theorem tailTrace_2570890 : CollatzResearch.WordTrace tailWord_2570890 prefixEnd_2570890 293356062186122581055933 := by
  unfold tailWord_2570890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23442015414028019475179531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62512041104074718600478749 23442015414028019475179531)
  ·
    refine ⟨35163023121042029212769297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23442015414028019475179531 35163023121042029212769297)
    ·
      refine ⟨26372267340781521909576973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35163023121042029212769297 26372267340781521909576973)
      ·
        refine ⟨9889600252793070716091365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26372267340781521909576973 9889600252793070716091365)
        ·
          refine ⟨1854300047398700759267131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9889600252793070716091365 1854300047398700759267131)
          ·
            refine ⟨2781450071098051138900697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854300047398700759267131 2781450071098051138900697)
            ·
              refine ⟨2086087553323538354175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781450071098051138900697 2086087553323538354175523)
              ·
                refine ⟨3129131329985307531263285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086087553323538354175523 3129131329985307531263285)
                ·
                  refine ⟨293356062186122581055933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129131329985307531263285 293356062186122581055933)
                  ·
                    rfl

theorem cell22_2570890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_2570890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570890 prefixEnd_2570890 := by exact prefixLift 2570890
  have htrace : WordTrace (prefixWord ++ tailWord_2570890) baseStart_2570890 baseEnd_2570890 := by
    simpa [prefixWord, tailWord_2570890, baseEnd_2570890] using wordTrace_append hprefix tailTrace_2570890
  have hstable : (prefixWord ++ tailWord_2570890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570890).length < 2 ^ (prefixWord ++ tailWord_2570890).sum := by decide
  have hdescent : baseEnd_2570890 < baseStart_2570890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570929 : List Nat := [1, 2, 2, 6, 11]
def baseStart_2570929 : Nat := 118140960795 + 2570929 * 2 ^ 59
def prefixEnd_2570929 : Nat := 4983230072969 + 3 ^ 40 * 2570929 * 2
def baseEnd_2570929 : Nat := 3621734720392529388653

theorem tailTrace_2570929 : CollatzResearch.WordTrace tailWord_2570929 prefixEnd_2570929 3621734720392529388653 := by
  unfold tailWord_2570929
  simp only [CollatzResearch.WordTrace]
  refine ⟨93769484102970787561387841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62512989401980525040925227 93769484102970787561387841)
  ·
    refine ⟨70327113077228090671040881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93769484102970787561387841 70327113077228090671040881)
    ·
      refine ⟨52745334807921068003280661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70327113077228090671040881 52745334807921068003280661)
      ·
        refine ⟨2472437569121300062653781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52745334807921068003280661 2472437569121300062653781)
        ·
          refine ⟨3621734720392529388653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2472437569121300062653781 3621734720392529388653)
          ·
            rfl

theorem cell22_2570929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 11].length) (baseStart_2570929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570929 prefixEnd_2570929 := by exact prefixLift 2570929
  have htrace : WordTrace (prefixWord ++ tailWord_2570929) baseStart_2570929 baseEnd_2570929 := by
    simpa [prefixWord, tailWord_2570929, baseEnd_2570929] using wordTrace_append hprefix tailTrace_2570929
  have hstable : (prefixWord ++ tailWord_2570929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570929).length < 2 ^ (prefixWord ++ tailWord_2570929).sum := by decide
  have hdescent : baseEnd_2570929 < baseStart_2570929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570933 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2570933 : Nat := 118140960795 + 2570933 * 2 ^ 59
def prefixEnd_2570933 : Nat := 4983230072969 + 3 ^ 40 * 2570933 * 2
def baseEnd_2570933 : Nat := 880082906337129964342667

theorem tailTrace_2570933 : CollatzResearch.WordTrace tailWord_2570933 prefixEnd_2570933 880082906337129964342667 := by
  unfold tailWord_2570933
  simp only [CollatzResearch.WordTrace]
  refine ⟨93769629994956296244533453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62513086663304197496355635 93769629994956296244533453)
  ·
    refine ⟨35163611248108611091700045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93769629994956296244533453 35163611248108611091700045)
    ·
      refine ⟨13186354218040729159387517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35163611248108611091700045 13186354218040729159387517)
      ·
        refine ⟨4944882831765273434770319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13186354218040729159387517 4944882831765273434770319)
        ·
          refine ⟨7417324247647910152155479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944882831765273434770319 7417324247647910152155479)
          ·
            refine ⟨11125986371471865228233219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7417324247647910152155479 11125986371471865228233219)
            ·
              refine ⟨16688979557207797842349829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11125986371471865228233219 16688979557207797842349829)
              ·
                refine ⟨3129183666976462095440593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16688979557207797842349829 3129183666976462095440593)
                ·
                  refine ⟨2346887750232346571580445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129183666976462095440593 2346887750232346571580445)
                  ·
                    refine ⟨880082906337129964342667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346887750232346571580445 880082906337129964342667)
                    ·
                      rfl

theorem cell22_2570933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2570933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570933 prefixEnd_2570933 := by exact prefixLift 2570933
  have htrace : WordTrace (prefixWord ++ tailWord_2570933) baseStart_2570933 baseEnd_2570933 := by
    simpa [prefixWord, tailWord_2570933, baseEnd_2570933] using wordTrace_append hprefix tailTrace_2570933
  have hstable : (prefixWord ++ tailWord_2570933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570933).length < 2 ^ (prefixWord ++ tailWord_2570933).sum := by decide
  have hdescent : baseEnd_2570933 < baseStart_2570933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570935 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 4]
def baseStart_2570935 : Nat := 118140960795 + 2570935 * 2 ^ 59
def prefixEnd_2570935 : Nat := 4983230072969 + 3 ^ 40 * 2570935 * 2
def baseEnd_2570935 : Nat := 293361196992667541930887

theorem tailTrace_2570935 : CollatzResearch.WordTrace tailWord_2570935 prefixEnd_2570935 293361196992667541930887 := by
  unfold tailWord_2570935
  simp only [CollatzResearch.WordTrace]
  refine ⟨93769702940949050586106259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62513135293966033724070839 93769702940949050586106259)
  ·
    refine ⟨140654554411423575879159389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93769702940949050586106259 140654554411423575879159389)
    ·
      refine ⟨52745457904283840954684771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140654554411423575879159389 52745457904283840954684771)
      ·
        refine ⟨79118186856425761432027157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52745457904283840954684771 79118186856425761432027157)
        ·
          refine ⟨3708665008894957567126273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79118186856425761432027157 3708665008894957567126273)
          ·
            refine ⟨2781498756671218175344705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3708665008894957567126273 2781498756671218175344705)
            ·
              refine ⟨2086124067503413631508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781498756671218175344705 2086124067503413631508529)
              ·
                refine ⟨1564593050627560223631397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086124067503413631508529 1564593050627560223631397)
                ·
                  refine ⟨293361196992667541930887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564593050627560223631397 293361196992667541930887)
                  ·
                    rfl

theorem cell22_2570935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 4].length) (baseStart_2570935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570935 prefixEnd_2570935 := by exact prefixLift 2570935
  have htrace : WordTrace (prefixWord ++ tailWord_2570935) baseStart_2570935 baseEnd_2570935 := by
    simpa [prefixWord, tailWord_2570935, baseEnd_2570935] using wordTrace_append hprefix tailTrace_2570935
  have hstable : (prefixWord ++ tailWord_2570935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570935).length < 2 ^ (prefixWord ++ tailWord_2570935).sum := by decide
  have hdescent : baseEnd_2570935 < baseStart_2570935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570961 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2570961 : Nat := 118140960795 + 2570961 * 2 ^ 59
def prefixEnd_2570961 : Nat := 4983230072969 + 3 ^ 40 * 2570961 * 2
def baseEnd_2570961 : Nat := 880092491309347224642581

theorem tailTrace_2570961 : CollatzResearch.WordTrace tailWord_2570961 prefixEnd_2570961 880092491309347224642581 := by
  unfold tailWord_2570961
  simp only [CollatzResearch.WordTrace]
  refine ⟨93770651238854857026552737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62513767492569904684368491 93770651238854857026552737)
  ·
    refine ⟨70327988429141142769914553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93770651238854857026552737 70327988429141142769914553)
    ·
      refine ⟨52745991321855857077435915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70327988429141142769914553 52745991321855857077435915)
      ·
        refine ⟨79118986982783785616153873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52745991321855857077435915 79118986982783785616153873)
        ·
          refine ⟨59339240237087839212115405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79118986982783785616153873 59339240237087839212115405)
          ·
            refine ⟨22252215088907939704543277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59339240237087839212115405 22252215088907939704543277)
            ·
              refine ⟨8344580658340477389203729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22252215088907939704543277 8344580658340477389203729)
              ·
                refine ⟨6258435493755358041902797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344580658340477389203729 6258435493755358041902797)
                ·
                  refine ⟨2346913310158259265713549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6258435493755358041902797 2346913310158259265713549)
                  ·
                    refine ⟨880092491309347224642581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346913310158259265713549 880092491309347224642581)
                    ·
                      rfl

theorem cell22_2570961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2570961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570961 prefixEnd_2570961 := by exact prefixLift 2570961
  have htrace : WordTrace (prefixWord ++ tailWord_2570961) baseStart_2570961 baseEnd_2570961 := by
    simpa [prefixWord, tailWord_2570961, baseEnd_2570961] using wordTrace_append hprefix tailTrace_2570961
  have hstable : (prefixWord ++ tailWord_2570961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570961).length < 2 ^ (prefixWord ++ tailWord_2570961).sum := by decide
  have hdescent : baseEnd_2570961 < baseStart_2570961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570965 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2570965 : Nat := 118140960795 + 2570965 * 2 ^ 59
def prefixEnd_2570965 : Nat := 4983230072969 + 3 ^ 40 * 2570965 * 2
def baseEnd_2570965 : Nat := 880093860591092547542569

theorem tailTrace_2570965 : CollatzResearch.WordTrace tailWord_2570965 prefixEnd_2570965 880093860591092547542569 := by
  unfold tailWord_2570965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93770797130840365709698349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62513864753893577139798899 93770797130840365709698349)
  ·
    refine ⟨35164048924065137141136881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93770797130840365709698349 35164048924065137141136881)
    ·
      refine ⟨26373036693048852855852661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35164048924065137141136881 26373036693048852855852661)
      ·
        refine ⟨2472472189973329955236187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26373036693048852855852661 2472472189973329955236187)
        ·
          refine ⟨3708708284959994932854281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472472189973329955236187 3708708284959994932854281)
          ·
            refine ⟨2781531213719996199640711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3708708284959994932854281 2781531213719996199640711)
            ·
              refine ⟨4172296820579994299461067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781531213719996199640711 4172296820579994299461067)
              ·
                refine ⟨6258445230869991449191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172296820579994299461067 6258445230869991449191601)
                ·
                  refine ⟨4693833923152493586893701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258445230869991449191601 4693833923152493586893701)
                  ·
                    refine ⟨880093860591092547542569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693833923152493586893701 880093860591092547542569)
                    ·
                      rfl

theorem cell22_2570965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2570965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570965 prefixEnd_2570965 := by exact prefixLift 2570965
  have htrace : WordTrace (prefixWord ++ tailWord_2570965) baseStart_2570965 baseEnd_2570965 := by
    simpa [prefixWord, tailWord_2570965, baseEnd_2570965] using wordTrace_append hprefix tailTrace_2570965
  have hstable : (prefixWord ++ tailWord_2570965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570965).length < 2 ^ (prefixWord ++ tailWord_2570965).sum := by decide
  have hdescent : baseEnd_2570965 < baseStart_2570965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570991 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 5]
def baseStart_2570991 : Nat := 118140960795 + 2570991 * 2 ^ 59
def prefixEnd_2570991 : Nat := 4983230072969 + 3 ^ 40 * 2570991 * 2
def baseEnd_2570991 : Nat := 293367586974145715464163

theorem tailTrace_2570991 : CollatzResearch.WordTrace tailWord_2570991 prefixEnd_2570991 293367586974145715464163 := by
  unfold tailWord_2570991
  simp only [CollatzResearch.WordTrace]
  refine ⟨93771745428746172150144827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62514496952497448100096551 93771745428746172150144827)
  ·
    refine ⟨140657618143119258225217241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93771745428746172150144827 140657618143119258225217241)
    ·
      refine ⟨105493213607339443668912931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140657618143119258225217241 105493213607339443668912931)
      ·
        refine ⟨158239820411009165503369397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105493213607339443668912931 158239820411009165503369397)
        ·
          refine ⟨14834983163532109265940881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158239820411009165503369397 14834983163532109265940881)
          ·
            refine ⟨11126237372649081949455661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14834983163532109265940881 11126237372649081949455661)
            ·
              refine ⟨4172339014743405731045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11126237372649081949455661 4172339014743405731045873)
              ·
                refine ⟨3129254261057554298284405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172339014743405731045873 3129254261057554298284405)
                ·
                  refine ⟨293367586974145715464163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129254261057554298284405 293367586974145715464163)
                  ·
                    rfl

theorem cell22_2570991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 5].length) (baseStart_2570991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2570991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2570991 prefixEnd_2570991 := by exact prefixLift 2570991
  have htrace : WordTrace (prefixWord ++ tailWord_2570991) baseStart_2570991 baseEnd_2570991 := by
    simpa [prefixWord, tailWord_2570991, baseEnd_2570991] using wordTrace_append hprefix tailTrace_2570991
  have hstable : (prefixWord ++ tailWord_2570991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570991).length < 2 ^ (prefixWord ++ tailWord_2570991).sum := by decide
  have hdescent : baseEnd_2570991 < baseStart_2570991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571085 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2571085 : Nat := 118140960795 + 2571085 * 2 ^ 59
def prefixEnd_2571085 : Nat := 4983230072969 + 3 ^ 40 * 2571085 * 2
def baseEnd_2571085 : Nat := 880134939043452234542201

theorem tailTrace_2571085 : CollatzResearch.WordTrace tailWord_2571085 prefixEnd_2571085 880134939043452234542201 := by
  unfold tailWord_2571085
  simp only [CollatzResearch.WordTrace]
  refine ⟨93775173890405626204066709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62516782593603750802711139 93775173890405626204066709)
  ·
    refine ⟨4395711276112763728315627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93775173890405626204066709 4395711276112763728315627)
    ·
      refine ⟨6593566914169145592473441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395711276112763728315627 6593566914169145592473441)
      ·
        refine ⟨4945175185626859194355081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6593566914169145592473441 4945175185626859194355081)
        ·
          refine ⟨3708881389220144395766311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4945175185626859194355081 3708881389220144395766311)
          ·
            refine ⟨5563322083830216593649467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708881389220144395766311 5563322083830216593649467)
            ·
              refine ⟨8344983125745324890474201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563322083830216593649467 8344983125745324890474201)
              ·
                refine ⟨6258737344308993667855651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344983125745324890474201 6258737344308993667855651)
                ·
                  refine ⟨9388106016463490501783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258737344308993667855651 9388106016463490501783477)
                  ·
                    refine ⟨880134939043452234542201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9388106016463490501783477 880134939043452234542201)
                    ·
                      rfl

theorem cell22_2571085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2571085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571085 prefixEnd_2571085 := by exact prefixLift 2571085
  have htrace : WordTrace (prefixWord ++ tailWord_2571085) baseStart_2571085 baseEnd_2571085 := by
    simpa [prefixWord, tailWord_2571085, baseEnd_2571085] using wordTrace_append hprefix tailTrace_2571085
  have hstable : (prefixWord ++ tailWord_2571085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571085).length < 2 ^ (prefixWord ++ tailWord_2571085).sum := by decide
  have hdescent : baseEnd_2571085 < baseStart_2571085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571111 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2571111 : Nat := 118140960795 + 2571111 * 2 ^ 59
def prefixEnd_2571111 : Nat := 4983230072969 + 3 ^ 40 * 2571111 * 2
def baseEnd_2571111 : Nat := 880143839374796833392121

theorem tailTrace_2571111 : CollatzResearch.WordTrace tailWord_2571111 prefixEnd_2571111 880143839374796833392121 := by
  unfold tailWord_2571111
  simp only [CollatzResearch.WordTrace]
  refine ⟨93776122188311432644513187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62517414792207621763008791 93776122188311432644513187)
  ·
    refine ⟨140664183282467148966769781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93776122188311432644513187 140664183282467148966769781)
    ·
      refine ⟨13187267182731295215634667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140664183282467148966769781 13187267182731295215634667)
      ·
        refine ⟨19780900774096942823452001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13187267182731295215634667 19780900774096942823452001)
        ·
          refine ⟨14835675580572707117589001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19780900774096942823452001 14835675580572707117589001)
          ·
            refine ⟨11126756685429530338191751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14835675580572707117589001 11126756685429530338191751)
            ·
              refine ⟨16690135028144295507287627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126756685429530338191751 16690135028144295507287627)
              ·
                refine ⟨25035202542216443260931441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16690135028144295507287627 25035202542216443260931441)
                ·
                  refine ⟨18776401906662332445698581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25035202542216443260931441 18776401906662332445698581)
                  ·
                    refine ⟨880143839374796833392121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18776401906662332445698581 880143839374796833392121)
                    ·
                      rfl

theorem cell22_2571111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2571111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571111 prefixEnd_2571111 := by exact prefixLift 2571111
  have htrace : WordTrace (prefixWord ++ tailWord_2571111) baseStart_2571111 baseEnd_2571111 := by
    simpa [prefixWord, tailWord_2571111, baseEnd_2571111] using wordTrace_append hprefix tailTrace_2571111
  have hstable : (prefixWord ++ tailWord_2571111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571111).length < 2 ^ (prefixWord ++ tailWord_2571111).sum := by decide
  have hdescent : baseEnd_2571111 < baseStart_2571111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571134 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2571134 : Nat := 118140960795 + 2571134 * 2 ^ 59
def prefixEnd_2571134 : Nat := 4983230072969 + 3 ^ 40 * 2571134 * 2
def baseEnd_2571134 : Nat := 880151712744832440067051

theorem tailTrace_2571134 : CollatzResearch.WordTrace tailWord_2571134 prefixEnd_2571134 880151712744832440067051 := by
  unfold tailWord_2571134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11722120133403513446575057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62517974044818738381733637 11722120133403513446575057)
  ·
    refine ⟨8791590100052635084931293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11722120133403513446575057 8791590100052635084931293)
    ·
      refine ⟨3296846287519738156849235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8791590100052635084931293 3296846287519738156849235)
      ·
        refine ⟨4945269431279607235273853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296846287519738156849235 4945269431279607235273853)
        ·
          refine ⟨1854476036729852713227695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4945269431279607235273853 1854476036729852713227695)
          ·
            refine ⟨2781714055094779069841543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854476036729852713227695 2781714055094779069841543)
            ·
              refine ⟨4172571082642168604762315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781714055094779069841543 4172571082642168604762315)
              ·
                refine ⟨6258856623963252907143473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172571082642168604762315 6258856623963252907143473)
                ·
                  refine ⟨4694142467972439680357605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258856623963252907143473 4694142467972439680357605)
                  ·
                    refine ⟨880151712744832440067051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694142467972439680357605 880151712744832440067051)
                    ·
                      rfl

theorem cell22_2571134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2571134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571134 prefixEnd_2571134 := by exact prefixLift 2571134
  have htrace : WordTrace (prefixWord ++ tailWord_2571134) baseStart_2571134 baseEnd_2571134 := by
    simpa [prefixWord, tailWord_2571134, baseEnd_2571134] using wordTrace_append hprefix tailTrace_2571134
  have hstable : (prefixWord ++ tailWord_2571134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571134).length < 2 ^ (prefixWord ++ tailWord_2571134).sum := by decide
  have hdescent : baseEnd_2571134 < baseStart_2571134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571171 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 6]
def baseStart_2571171 : Nat := 118140960795 + 2571171 * 2 ^ 59
def prefixEnd_2571171 : Nat := 4983230072969 + 3 ^ 40 * 2571171 * 2
def baseEnd_2571171 : Nat := 293388126200325558963979

theorem tailTrace_2571171 : CollatzResearch.WordTrace tailWord_2571171 prefixEnd_2571171 293388126200325558963979 := by
  unfold tailWord_2571171
  simp only [CollatzResearch.WordTrace]
  refine ⟨93778310568094062891697367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62518873712062708594464911 93778310568094062891697367)
  ·
    refine ⟨140667465852141094337546051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93778310568094062891697367 140667465852141094337546051)
    ·
      refine ⟨211001198778211641506319077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140667465852141094337546051 211001198778211641506319077)
      ·
        refine ⟨39562724770914682782434827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211001198778211641506319077 39562724770914682782434827)
        ·
          refine ⟨59344087156372024173652241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39562724770914682782434827 59344087156372024173652241)
          ·
            refine ⟨44508065367279018130239181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59344087156372024173652241 44508065367279018130239181)
            ·
              refine ⟨16690524512729631798839693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44508065367279018130239181 16690524512729631798839693)
              ·
                refine ⟨6258946692273611924564885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16690524512729631798839693 6258946692273611924564885)
                ·
                  refine ⟨293388126200325558963979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6258946692273611924564885 293388126200325558963979)
                  ·
                    rfl

theorem cell22_2571171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_2571171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571171 prefixEnd_2571171 := by exact prefixLift 2571171
  have htrace : WordTrace (prefixWord ++ tailWord_2571171) baseStart_2571171 baseEnd_2571171 := by
    simpa [prefixWord, tailWord_2571171, baseEnd_2571171] using wordTrace_append hprefix tailTrace_2571171
  have hstable : (prefixWord ++ tailWord_2571171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571171).length < 2 ^ (prefixWord ++ tailWord_2571171).sum := by decide
  have hdescent : baseEnd_2571171 < baseStart_2571171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571220 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2571220 : Nat := 118140960795 + 2571220 * 2 ^ 59
def prefixEnd_2571220 : Nat := 4983230072969 + 3 ^ 40 * 2571220 * 2
def baseEnd_2571220 : Nat := 880181152302356882416787

theorem tailTrace_2571220 : CollatzResearch.WordTrace tailWord_2571220 prefixEnd_2571220 880181152302356882416787 := by
  unfold tailWord_2571220
  simp only [CollatzResearch.WordTrace]
  refine ⟨46890048872458272130115557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62520065163277696173487409 46890048872458272130115557)
  ·
    refine ⟨8791884163585926024396667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46890048872458272130115557 8791884163585926024396667)
    ·
      refine ⟨13187826245378889036595001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791884163585926024396667 13187826245378889036595001)
      ·
        refine ⟨9890869684034166777446251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187826245378889036595001 9890869684034166777446251)
        ·
          refine ⟨14836304526051250166169377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890869684034166777446251 14836304526051250166169377)
          ·
            refine ⟨11127228394538437624627033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14836304526051250166169377 11127228394538437624627033)
            ·
              refine ⟨8345421295903828218470275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11127228394538437624627033 8345421295903828218470275)
              ·
                refine ⟨12518131943855742327705413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345421295903828218470275 12518131943855742327705413)
                ·
                  refine ⟨2347149739472951686444765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12518131943855742327705413 2347149739472951686444765)
                  ·
                    refine ⟨880181152302356882416787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347149739472951686444765 880181152302356882416787)
                    ·
                      rfl

theorem cell22_2571220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2571220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571220 prefixEnd_2571220 := by exact prefixLift 2571220
  have htrace : WordTrace (prefixWord ++ tailWord_2571220) baseStart_2571220 baseEnd_2571220 := by
    simpa [prefixWord, tailWord_2571220, baseEnd_2571220] using wordTrace_append hprefix tailTrace_2571220
  have hstable : (prefixWord ++ tailWord_2571220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571220).length < 2 ^ (prefixWord ++ tailWord_2571220).sum := by decide
  have hdescent : baseEnd_2571220 < baseStart_2571220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571222 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2571222 : Nat := 118140960795 + 2571222 * 2 ^ 59
def prefixEnd_2571222 : Nat := 4983230072969 + 3 ^ 40 * 2571222 * 2
def baseEnd_2571222 : Nat := 293393945647743181288927

theorem tailTrace_2571222 : CollatzResearch.WordTrace tailWord_2571222 prefixEnd_2571222 293393945647743181288927 := by
  unfold tailWord_2571222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861260668181831162612745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62520113793939532401202613 5861260668181831162612745)
  ·
    refine ⟨4395945501136373371959559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5861260668181831162612745 4395945501136373371959559)
    ·
      refine ⟨6593918251704560057939339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395945501136373371959559 6593918251704560057939339)
      ·
        refine ⟨9890877377556840086909009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593918251704560057939339 9890877377556840086909009)
        ·
          refine ⟨7418158033167630065181757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9890877377556840086909009 7418158033167630065181757)
          ·
            refine ⟨2781809262437861274443159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7418158033167630065181757 2781809262437861274443159)
            ·
              refine ⟨4172713893656791911664739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781809262437861274443159 4172713893656791911664739)
              ·
                refine ⟨6259070840485187867497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172713893656791911664739 6259070840485187867497109)
                ·
                  refine ⟨293393945647743181288927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6259070840485187867497109 293393945647743181288927)
                  ·
                    rfl

theorem cell22_2571222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2571222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571222 prefixEnd_2571222 := by exact prefixLift 2571222
  have htrace : WordTrace (prefixWord ++ tailWord_2571222) baseStart_2571222 baseEnd_2571222 := by
    simpa [prefixWord, tailWord_2571222, baseEnd_2571222] using wordTrace_append hprefix tailTrace_2571222
  have hstable : (prefixWord ++ tailWord_2571222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571222).length < 2 ^ (prefixWord ++ tailWord_2571222).sum := by decide
  have hdescent : baseEnd_2571222 < baseStart_2571222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571248 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_2571248 : Nat := 118140960795 + 2571248 * 2 ^ 59
def prefixEnd_2571248 : Nat := 4983230072969 + 3 ^ 40 * 2571248 * 2
def baseEnd_2571248 : Nat := 880190737274574142716701

theorem tailTrace_2571248 : CollatzResearch.WordTrace tailWord_2571248 prefixEnd_2571248 880190737274574142716701 := by
  unfold tailWord_2571248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46890559494407552521125199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62520745992543403361500265 46890559494407552521125199)
  ·
    refine ⟨70335839241611328781687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46890559494407552521125199 70335839241611328781687799)
    ·
      refine ⟨105503758862416993172531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70335839241611328781687799 105503758862416993172531699)
      ·
        refine ⟨158255638293625489758797549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105503758862416993172531699 158255638293625489758797549)
        ·
          refine ⟨59345864360109558659549081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158255638293625489758797549 59345864360109558659549081)
          ·
            refine ⟨44509398270082168994661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59345864360109558659549081 44509398270082168994661811)
            ·
              refine ⟨66764097405123253491992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44509398270082168994661811 66764097405123253491992717)
              ·
                refine ⟨25036536526921220059497269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66764097405123253491992717 25036536526921220059497269)
                ·
                  refine ⟨2347175299398864380577869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25036536526921220059497269 2347175299398864380577869)
                  ·
                    refine ⟨880190737274574142716701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347175299398864380577869 880190737274574142716701)
                    ·
                      rfl

theorem cell22_2571248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_2571248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571248 prefixEnd_2571248 := by exact prefixLift 2571248
  have htrace : WordTrace (prefixWord ++ tailWord_2571248) baseStart_2571248 baseEnd_2571248 := by
    simpa [prefixWord, tailWord_2571248, baseEnd_2571248] using wordTrace_append hprefix tailTrace_2571248
  have hstable : (prefixWord ++ tailWord_2571248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571248).length < 2 ^ (prefixWord ++ tailWord_2571248).sum := by decide
  have hdescent : baseEnd_2571248 < baseStart_2571248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571308 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_2571308 : Nat := 118140960795 + 2571308 * 2 ^ 59
def prefixEnd_2571308 : Nat := 4983230072969 + 3 ^ 40 * 2571308 * 2
def baseEnd_2571308 : Nat := 880211276500753986216517

theorem tailTrace_2571308 : CollatzResearch.WordTrace tailWord_2571308 prefixEnd_2571308 880211276500753986216517 := by
  unfold tailWord_2571308
  simp only [CollatzResearch.WordTrace]
  refine ⟨46891653684298867644717289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62522204912398490192956385 46891653684298867644717289)
  ·
    refine ⟨35168740263224150733537967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46891653684298867644717289 35168740263224150733537967)
    ·
      refine ⟨52753110394836226100306951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35168740263224150733537967 52753110394836226100306951)
      ·
        refine ⟨79129665592254339150460427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52753110394836226100306951 79129665592254339150460427)
        ·
          refine ⟨118694498388381508725690641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79129665592254339150460427 118694498388381508725690641)
          ·
            refine ⟨89020873791286131544267981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118694498388381508725690641 89020873791286131544267981)
            ·
              refine ⟨33382827671732299329100493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89020873791286131544267981 33382827671732299329100493)
              ·
                refine ⟨12518560376899612248412685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33382827671732299329100493 12518560376899612248412685)
                ·
                  refine ⟨4694460141337354593154757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12518560376899612248412685 4694460141337354593154757)
                  ·
                    refine ⟨880211276500753986216517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694460141337354593154757 880211276500753986216517)
                    ·
                      rfl

theorem cell22_2571308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_2571308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571308 prefixEnd_2571308 := by exact prefixLift 2571308
  have htrace : WordTrace (prefixWord ++ tailWord_2571308) baseStart_2571308 baseEnd_2571308 := by
    simpa [prefixWord, tailWord_2571308, baseEnd_2571308] using wordTrace_append hprefix tailTrace_2571308
  have hstable : (prefixWord ++ tailWord_2571308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571308).length < 2 ^ (prefixWord ++ tailWord_2571308).sum := by decide
  have hdescent : baseEnd_2571308 < baseStart_2571308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571316 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2571316 : Nat := 118140960795 + 2571316 * 2 ^ 59
def prefixEnd_2571316 : Nat := 4983230072969 + 3 ^ 40 * 2571316 * 2
def baseEnd_2571316 : Nat := 880214015064244632016493

theorem tailTrace_2571316 : CollatzResearch.WordTrace tailWord_2571316 prefixEnd_2571316 880214015064244632016493 := by
  unfold tailWord_2571316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46891799576284376327862901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62522399435045835103817201 46891799576284376327862901)
  ·
    refine ⟨4396106210276660280737147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46891799576284376327862901 4396106210276660280737147)
    ·
      refine ⟨6594159315414990421105721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396106210276660280737147 6594159315414990421105721)
      ·
        refine ⟨4945619486561242815829291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594159315414990421105721 4945619486561242815829291)
        ·
          refine ⟨7418429229841864223743937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945619486561242815829291 7418429229841864223743937)
          ·
            refine ⟨5563821922381398167807953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418429229841864223743937 5563821922381398167807953)
            ·
              refine ⟨4172866441786048625855965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5563821922381398167807953 4172866441786048625855965)
              ·
                refine ⟨1564824915669768234695987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172866441786048625855965 1564824915669768234695987)
                ·
                  refine ⟨2347237373504652352043981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564824915669768234695987 2347237373504652352043981)
                  ·
                    refine ⟨880214015064244632016493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347237373504652352043981 880214015064244632016493)
                    ·
                      rfl

theorem cell22_2571316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2571316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571316 prefixEnd_2571316 := by exact prefixLift 2571316
  have htrace : WordTrace (prefixWord ++ tailWord_2571316) baseStart_2571316 baseEnd_2571316 := by
    simpa [prefixWord, tailWord_2571316, baseEnd_2571316] using wordTrace_append hprefix tailTrace_2571316
  have hstable : (prefixWord ++ tailWord_2571316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571316).length < 2 ^ (prefixWord ++ tailWord_2571316).sum := by decide
  have hdescent : baseEnd_2571316 < baseStart_2571316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571329 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 5]
def baseStart_2571329 : Nat := 118140960795 + 2571329 * 2 ^ 59
def prefixEnd_2571329 : Nat := 4983230072969 + 3 ^ 40 * 2571329 * 2
def baseEnd_2571329 : Nat := 293406155076638977147151

theorem tailTrace_2571329 : CollatzResearch.WordTrace tailWord_2571329 prefixEnd_2571329 293406155076638977147151 := by
  unfold tailWord_2571329
  simp only [CollatzResearch.WordTrace]
  refine ⟨93784073301521655875949041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62522715534347770583966027 93784073301521655875949041)
  ·
    refine ⟨70338054976141241906961781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93784073301521655875949041 70338054976141241906961781)
    ·
      refine ⟨6594192654013241428777667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70338054976141241906961781 6594192654013241428777667)
      ·
        refine ⟨9891288981019862143166501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594192654013241428777667 9891288981019862143166501)
        ·
          refine ⟨1854616683941224151843719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9891288981019862143166501 1854616683941224151843719)
          ·
            refine ⟨2781925025911836227765579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854616683941224151843719 2781925025911836227765579)
            ·
              refine ⟨4172887538867754341648369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781925025911836227765579 4172887538867754341648369)
              ·
                refine ⟨3129665654150815756236277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172887538867754341648369 3129665654150815756236277)
                ·
                  refine ⟨293406155076638977147151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129665654150815756236277 293406155076638977147151)
                  ·
                    rfl

theorem cell22_2571329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_2571329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571329 prefixEnd_2571329 := by exact prefixLift 2571329
  have htrace : WordTrace (prefixWord ++ tailWord_2571329) baseStart_2571329 baseEnd_2571329 := by
    simpa [prefixWord, tailWord_2571329, baseEnd_2571329] using wordTrace_append hprefix tailTrace_2571329
  have hstable : (prefixWord ++ tailWord_2571329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571329).length < 2 ^ (prefixWord ++ tailWord_2571329).sum := by decide
  have hdescent : baseEnd_2571329 < baseStart_2571329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571338 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2571338 : Nat := 118140960795 + 2571338 * 2 ^ 59
def prefixEnd_2571338 : Nat := 4983230072969 + 3 ^ 40 * 2571338 * 2
def baseEnd_2571338 : Nat := 880221546113843907966425

theorem tailTrace_2571338 : CollatzResearch.WordTrace tailWord_2571338 prefixEnd_2571338 880221546113843907966425 := by
  unfold tailWord_2571338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446100389622262603256667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62522934372326033608684445 23446100389622262603256667)
  ·
    refine ⟨35169150584433393904885001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23446100389622262603256667 35169150584433393904885001)
    ·
      refine ⟨26376862938325045428663751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35169150584433393904885001 26376862938325045428663751)
      ·
        refine ⟨39565294407487568142995627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26376862938325045428663751 39565294407487568142995627)
        ·
          refine ⟨59347941611231352214493441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39565294407487568142995627 59347941611231352214493441)
          ·
            refine ⟨44510956208423514160870081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59347941611231352214493441 44510956208423514160870081)
            ·
              refine ⟨33383217156317635620652561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44510956208423514160870081 33383217156317635620652561)
              ·
                refine ⟨25037412867238226715489421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33383217156317635620652561 25037412867238226715489421)
                ·
                  refine ⟨9389029825214335018308533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25037412867238226715489421 9389029825214335018308533)
                  ·
                    refine ⟨880221546113843907966425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9389029825214335018308533 880221546113843907966425)
                    ·
                      rfl

theorem cell22_2571338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2571338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571338 prefixEnd_2571338 := by exact prefixLift 2571338
  have htrace : WordTrace (prefixWord ++ tailWord_2571338) baseStart_2571338 baseEnd_2571338 := by
    simpa [prefixWord, tailWord_2571338, baseEnd_2571338] using wordTrace_append hprefix tailTrace_2571338
  have hstable : (prefixWord ++ tailWord_2571338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571338).length < 2 ^ (prefixWord ++ tailWord_2571338).sum := by decide
  have hdescent : baseEnd_2571338 < baseStart_2571338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_2571353 : Nat := 118140960795 + 2571353 * 2 ^ 59
def prefixEnd_2571353 : Nat := 4983230072969 + 3 ^ 40 * 2571353 * 2
def baseEnd_2571353 : Nat := 880226680920388868841379

theorem tailTrace_2571353 : CollatzResearch.WordTrace tailWord_2571353 prefixEnd_2571353 880226680920388868841379 := by
  unfold tailWord_2571353
  simp only [CollatzResearch.WordTrace]
  refine ⟨93784948653434707974822713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62523299102289805316548475 93784948653434707974822713)
  ·
    refine ⟨70338711490076030981117035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93784948653434707974822713 70338711490076030981117035)
    ·
      refine ⟨105508067235114046471675553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70338711490076030981117035 105508067235114046471675553)
      ·
        refine ⟨79131050426335534853756665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105508067235114046471675553 79131050426335534853756665)
        ·
          refine ⟨59348287819751651140317499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79131050426335534853756665 59348287819751651140317499)
          ·
            refine ⟨89022431729627476710476249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59348287819751651140317499 89022431729627476710476249)
            ·
              refine ⟨66766823797220607532857187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89022431729627476710476249 66766823797220607532857187)
              ·
                refine ⟨100150235695830911299285781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66766823797220607532857187 100150235695830911299285781)
                ·
                  refine ⟨4694542298242073967154021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100150235695830911299285781 4694542298242073967154021)
                  ·
                    refine ⟨880226680920388868841379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694542298242073967154021 880226680920388868841379)
                    ·
                      rfl

theorem cell22_2571353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_2571353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571353 prefixEnd_2571353 := by exact prefixLift 2571353
  have htrace : WordTrace (prefixWord ++ tailWord_2571353) baseStart_2571353 baseEnd_2571353 := by
    simpa [prefixWord, tailWord_2571353, baseEnd_2571353] using wordTrace_append hprefix tailTrace_2571353
  have hstable : (prefixWord ++ tailWord_2571353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571353).length < 2 ^ (prefixWord ++ tailWord_2571353).sum := by decide
  have hdescent : baseEnd_2571353 < baseStart_2571353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571370 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2571370 : Nat := 118140960795 + 2571370 * 2 ^ 59
def prefixEnd_2571370 : Nat := 4983230072969 + 3 ^ 40 * 2571370 * 2
def baseEnd_2571370 : Nat := 880232500367806491166327

theorem tailTrace_2571370 : CollatzResearch.WordTrace tailWord_2571370 prefixEnd_2571370 880232500367806491166327 := by
  unfold tailWord_2571370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446392173593279969547891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62523712462915413252127709 23446392173593279969547891)
  ·
    refine ⟨35169588260389919954321837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23446392173593279969547891 35169588260389919954321837)
    ·
      refine ⟨13188595597646219982870689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35169588260389919954321837 13188595597646219982870689)
      ·
        refine ⟨9891446698234664987153017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13188595597646219982870689 9891446698234664987153017)
        ·
          refine ⟨7418585023675998740364763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9891446698234664987153017 7418585023675998740364763)
          ·
            refine ⟨11127877535513998110547145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418585023675998740364763 11127877535513998110547145)
            ·
              refine ⟨8345908151635498582910359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11127877535513998110547145 8345908151635498582910359)
              ·
                refine ⟨12518862227453247874365539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345908151635498582910359 12518862227453247874365539)
                ·
                  refine ⟨18778293341179871811548309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12518862227453247874365539 18778293341179871811548309)
                  ·
                    refine ⟨880232500367806491166327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18778293341179871811548309 880232500367806491166327)
                    ·
                      rfl

theorem cell22_2571370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2571370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571370 prefixEnd_2571370 := by exact prefixLift 2571370
  have htrace : WordTrace (prefixWord ++ tailWord_2571370) baseStart_2571370 baseEnd_2571370 := by
    simpa [prefixWord, tailWord_2571370, baseEnd_2571370] using wordTrace_append hprefix tailTrace_2571370
  have hstable : (prefixWord ++ tailWord_2571370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571370).length < 2 ^ (prefixWord ++ tailWord_2571370).sum := by decide
  have hdescent : baseEnd_2571370 < baseStart_2571370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571374 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_2571374 : Nat := 118140960795 + 2571374 * 2 ^ 59
def prefixEnd_2571374 : Nat := 4983230072969 + 3 ^ 40 * 2571374 * 2
def baseEnd_2571374 : Nat := 293411289883183938022105

theorem tailTrace_2571374 : CollatzResearch.WordTrace tailWord_2571374 prefixEnd_2571374 293411289883183938022105 := by
  unfold tailWord_2571374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723214323294828570167147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62523809724239085707558117 11723214323294828570167147)
  ·
    refine ⟨17584821484942242855250721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11723214323294828570167147 17584821484942242855250721)
    ·
      refine ⟨13188616113706682141438041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17584821484942242855250721 13188616113706682141438041)
      ·
        refine ⟨9891462085280011606078531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13188616113706682141438041 9891462085280011606078531)
        ·
          refine ⟨14837193127920017409117797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891462085280011606078531 14837193127920017409117797)
          ·
            refine ⟨2781973711485003264209587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14837193127920017409117797 2781973711485003264209587)
            ·
              refine ⟨4172960567227504896314381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781973711485003264209587 4172960567227504896314381)
              ·
                refine ⟨1564860212710314336117893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172960567227504896314381 1564860212710314336117893)
                ·
                  refine ⟨293411289883183938022105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564860212710314336117893 293411289883183938022105)
                  ·
                    rfl

theorem cell22_2571374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_2571374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571374 prefixEnd_2571374 := by exact prefixLift 2571374
  have htrace : WordTrace (prefixWord ++ tailWord_2571374) baseStart_2571374 baseEnd_2571374 := by
    simpa [prefixWord, tailWord_2571374, baseEnd_2571374] using wordTrace_append hprefix tailTrace_2571374
  have hstable : (prefixWord ++ tailWord_2571374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571374).length < 2 ^ (prefixWord ++ tailWord_2571374).sum := by decide
  have hdescent : baseEnd_2571374 < baseStart_2571374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571385 : List Nat := [1, 2, 1, 3, 5, 2, 8]
def baseStart_2571385 : Nat := 118140960795 + 2571385 * 2 ^ 59
def prefixEnd_2571385 : Nat := 4983230072969 + 3 ^ 40 * 2571385 * 2
def baseEnd_2571385 : Nat := 32601393895346350075603

theorem tailTrace_2571385 : CollatzResearch.WordTrace tailWord_2571385 prefixEnd_2571385 32601393895346350075603 := by
  unfold tailWord_2571385
  simp only [CollatzResearch.WordTrace]
  refine ⟨93786115789318777439987609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62524077192879184959991739 93786115789318777439987609)
  ·
    refine ⟨70339586841989083079990707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93786115789318777439987609 70339586841989083079990707)
    ·
      refine ⟨105509380262983624619986061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70339586841989083079990707 105509380262983624619986061)
      ·
        refine ⟨39566017598618859232494773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105509380262983624619986061 39566017598618859232494773)
        ·
          refine ⟨3709314149870518053046385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39566017598618859232494773 3709314149870518053046385)
          ·
            refine ⟨2781985612402888539784789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3709314149870518053046385 2781985612402888539784789)
            ·
              refine ⟨32601393895346350075603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2781985612402888539784789 32601393895346350075603)
              ·
                rfl

theorem cell22_2571385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 8].length) (baseStart_2571385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571385 prefixEnd_2571385 := by exact prefixLift 2571385
  have htrace : WordTrace (prefixWord ++ tailWord_2571385) baseStart_2571385 baseEnd_2571385 := by
    simpa [prefixWord, tailWord_2571385, baseEnd_2571385] using wordTrace_append hprefix tailTrace_2571385
  have hstable : (prefixWord ++ tailWord_2571385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571385).length < 2 ^ (prefixWord ++ tailWord_2571385).sum := by decide
  have hdescent : baseEnd_2571385 < baseStart_2571385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571406 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2571406 : Nat := 118140960795 + 2571406 * 2 ^ 59
def prefixEnd_2571406 : Nat := 4983230072969 + 3 ^ 40 * 2571406 * 2
def baseEnd_2571406 : Nat := 880244823903514397266217

theorem tailTrace_2571406 : CollatzResearch.WordTrace tailWord_2571406 prefixEnd_2571406 880244823903514397266217 := by
  unfold tailWord_2571406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723360215280337253312759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62524587814828465351001381 11723360215280337253312759)
  ·
    refine ⟨17585040322920505879969139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11723360215280337253312759 17585040322920505879969139)
    ·
      refine ⟨26377560484380758819953709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17585040322920505879969139 26377560484380758819953709)
      ·
        refine ⟨9891585181642784557482641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26377560484380758819953709 9891585181642784557482641)
        ·
          refine ⟨7418688886232088418111981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9891585181642784557482641 7418688886232088418111981)
          ·
            refine ⟨2782008332337033156791993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7418688886232088418111981 2782008332337033156791993)
            ·
              refine ⟨2086506249252774867593995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782008332337033156791993 2086506249252774867593995)
              ·
                refine ⟨3129759373879162301390993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086506249252774867593995 3129759373879162301390993)
                ·
                  refine ⟨2347319530409371726043245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129759373879162301390993 2347319530409371726043245)
                  ·
                    refine ⟨880244823903514397266217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347319530409371726043245 880244823903514397266217)
                    ·
                      rfl

theorem cell22_2571406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2571406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571406 prefixEnd_2571406 := by exact prefixLift 2571406
  have htrace : WordTrace (prefixWord ++ tailWord_2571406) baseStart_2571406 baseEnd_2571406 := by
    simpa [prefixWord, tailWord_2571406, baseEnd_2571406] using wordTrace_append hprefix tailTrace_2571406
  have hstable : (prefixWord ++ tailWord_2571406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571406).length < 2 ^ (prefixWord ++ tailWord_2571406).sum := by decide
  have hdescent : baseEnd_2571406 < baseStart_2571406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571413 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 9]
def baseStart_2571413 : Nat := 118140960795 + 2571413 * 2 ^ 59
def prefixEnd_2571413 : Nat := 4983230072969 + 3 ^ 40 * 2571413 * 2
def baseEnd_2571413 : Nat := 293415740048856237447065

theorem tailTrace_2571413 : CollatzResearch.WordTrace tailWord_2571413 prefixEnd_2571413 293415740048856237447065 := by
  unfold tailWord_2571413
  simp only [CollatzResearch.WordTrace]
  refine ⟨93787137033217338222006893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62524758022144892148004595 93787137033217338222006893)
  ·
    refine ⟨35170176387456501833252585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93787137033217338222006893 35170176387456501833252585)
    ·
      refine ⟨26377632290592376374939439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35170176387456501833252585 26377632290592376374939439)
      ·
        refine ⟨39566448435888564562409159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26377632290592376374939439 39566448435888564562409159)
        ·
          refine ⟨59349672653832846843613739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39566448435888564562409159 59349672653832846843613739)
          ·
            refine ⟨89024508980749270265420609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59349672653832846843613739 89024508980749270265420609)
            ·
              refine ⟨66768381735561952699065457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89024508980749270265420609 66768381735561952699065457)
              ·
                refine ⟨50076286301671464524299093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66768381735561952699065457 50076286301671464524299093)
                ·
                  refine ⟨293415740048856237447065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50076286301671464524299093 293415740048856237447065)
                  ·
                    rfl

theorem cell22_2571413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_2571413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571413 prefixEnd_2571413 := by exact prefixLift 2571413
  have htrace : WordTrace (prefixWord ++ tailWord_2571413) baseStart_2571413 baseEnd_2571413 := by
    simpa [prefixWord, tailWord_2571413, baseEnd_2571413] using wordTrace_append hprefix tailTrace_2571413
  have hstable : (prefixWord ++ tailWord_2571413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571413).length < 2 ^ (prefixWord ++ tailWord_2571413).sum := by decide
  have hdescent : baseEnd_2571413 < baseStart_2571413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571477 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2571477 : Nat := 118140960795 + 2571477 * 2 ^ 59
def prefixEnd_2571477 : Nat := 4983230072969 + 3 ^ 40 * 2571477 * 2
def baseEnd_2571477 : Nat := 880269128654493878740999

theorem tailTrace_2571477 : CollatzResearch.WordTrace tailWord_2571477 prefixEnd_2571477 880269128654493878740999 := by
  unfold tailWord_2571477
  simp only [CollatzResearch.WordTrace]
  refine ⟨93789471304985477152336685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62526314203323651434891123 93789471304985477152336685)
  ·
    refine ⟨35171051739369553932126257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93789471304985477152336685 35171051739369553932126257)
    ·
      refine ⟨26378288804527165449094693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35171051739369553932126257 26378288804527165449094693)
      ·
        refine ⟨4945929150848843521705255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26378288804527165449094693 4945929150848843521705255)
        ·
          refine ⟨7418893726273265282557883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945929150848843521705255 7418893726273265282557883)
          ·
            refine ⟨11128340589409897923836825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418893726273265282557883 11128340589409897923836825)
            ·
              refine ⟨8346255442057423442877619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11128340589409897923836825 8346255442057423442877619)
              ·
                refine ⟨12519383163086135164316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346255442057423442877619 12519383163086135164316429)
                ·
                  refine ⟨4694768686157300686618661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519383163086135164316429 4694768686157300686618661)
                  ·
                    refine ⟨880269128654493878740999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694768686157300686618661 880269128654493878740999)
                    ·
                      rfl

theorem cell22_2571477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2571477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571477 prefixEnd_2571477 := by exact prefixLift 2571477
  have htrace : WordTrace (prefixWord ++ tailWord_2571477) baseStart_2571477 baseEnd_2571477 := by
    simpa [prefixWord, tailWord_2571477, baseEnd_2571477] using wordTrace_append hprefix tailTrace_2571477
  have hstable : (prefixWord ++ tailWord_2571477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571477).length < 2 ^ (prefixWord ++ tailWord_2571477).sum := by decide
  have hdescent : baseEnd_2571477 < baseStart_2571477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571492 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_2571492 : Nat := 118140960795 + 2571492 * 2 ^ 59
def prefixEnd_2571492 : Nat := 4983230072969 + 3 ^ 40 * 2571492 * 2
def baseEnd_2571492 : Nat := 293424754487012946538651

theorem tailTrace_2571492 : CollatzResearch.WordTrace tailWord_2571492 prefixEnd_2571492 293424754487012946538651 := by
  unfold tailWord_2571492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46895009199965567357066365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62526678933287423142755153 46895009199965567357066365)
  ·
    refine ⟨17585628449987087758899887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46895009199965567357066365 17585628449987087758899887)
    ·
      refine ⟨26378442674980631638349831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17585628449987087758899887 26378442674980631638349831)
      ·
        refine ⟨39567664012470947457524747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26378442674980631638349831 39567664012470947457524747)
        ·
          refine ⟨59351496018706421186287121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39567664012470947457524747 59351496018706421186287121)
          ·
            refine ⟨44513622014029815889715341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59351496018706421186287121 44513622014029815889715341)
            ·
              refine ⟨16692608255261180958643253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44513622014029815889715341 16692608255261180958643253)
              ·
                refine ⟨1564932023930735714872805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16692608255261180958643253 1564932023930735714872805)
                ·
                  refine ⟨293424754487012946538651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564932023930735714872805 293424754487012946538651)
                  ·
                    rfl

theorem cell22_2571492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_2571492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571492 prefixEnd_2571492 := by exact prefixLift 2571492
  have htrace : WordTrace (prefixWord ++ tailWord_2571492) baseStart_2571492 baseEnd_2571492 := by
    simpa [prefixWord, tailWord_2571492, baseEnd_2571492] using wordTrace_append hprefix tailTrace_2571492
  have hstable : (prefixWord ++ tailWord_2571492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571492).length < 2 ^ (prefixWord ++ tailWord_2571492).sum := by decide
  have hdescent : baseEnd_2571492 < baseStart_2571492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571505 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_2571505 : Nat := 118140960795 + 2571505 * 2 ^ 59
def prefixEnd_2571505 : Nat := 4983230072969 + 3 ^ 40 * 2571505 * 2
def baseEnd_2571505 : Nat := 880278713626711139040913

theorem tailTrace_2571505 : CollatzResearch.WordTrace tailWord_2571505 prefixEnd_2571505 880278713626711139040913 := by
  unfold tailWord_2571505
  simp only [CollatzResearch.WordTrace]
  refine ⟨93790492548884037934355969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62526995032589358622903979 93790492548884037934355969)
  ·
    refine ⟨70342869411663028450766977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93790492548884037934355969 70342869411663028450766977)
    ·
      refine ⟨52757152058747271338075233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70342869411663028450766977 52757152058747271338075233)
      ·
        refine ⟨39567864044060453503556425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52757152058747271338075233 39567864044060453503556425)
        ·
          refine ⟨29675898033045340127667319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39567864044060453503556425 29675898033045340127667319)
          ·
            refine ⟨44513847049568010191500979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29675898033045340127667319 44513847049568010191500979)
            ·
              refine ⟨66770770574352015287251469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44513847049568010191500979 66770770574352015287251469)
              ·
                refine ⟨25039038965382005732719301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66770770574352015287251469 25039038965382005732719301)
                ·
                  refine ⟨4694819806009126074884869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25039038965382005732719301 4694819806009126074884869)
                  ·
                    refine ⟨880278713626711139040913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694819806009126074884869 880278713626711139040913)
                    ·
                      rfl

theorem cell22_2571505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_2571505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571505 prefixEnd_2571505 := by exact prefixLift 2571505
  have htrace : WordTrace (prefixWord ++ tailWord_2571505) baseStart_2571505 baseEnd_2571505 := by
    simpa [prefixWord, tailWord_2571505, baseEnd_2571505] using wordTrace_append hprefix tailTrace_2571505
  have hstable : (prefixWord ++ tailWord_2571505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571505).length < 2 ^ (prefixWord ++ tailWord_2571505).sum := by decide
  have hdescent : baseEnd_2571505 < baseStart_2571505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571507 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 4, 3]
def baseStart_2571507 : Nat := 118140960795 + 2571507 * 2 ^ 59
def prefixEnd_2571507 : Nat := 4983230072969 + 3 ^ 40 * 2571507 * 2
def baseEnd_2571507 : Nat := 880279398267583800490907

theorem tailTrace_2571507 : CollatzResearch.WordTrace tailWord_2571507 prefixEnd_2571507 880279398267583800490907 := by
  unfold tailWord_2571507
  simp only [CollatzResearch.WordTrace]
  refine ⟨93790565494876792275928775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62527043663251194850619183 93790565494876792275928775)
  ·
    refine ⟨140685848242315188413893163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93790565494876792275928775 140685848242315188413893163)
    ·
      refine ⟨211028772363472782620839745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140685848242315188413893163 211028772363472782620839745)
      ·
        refine ⟨158271579272604586965629809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211028772363472782620839745 158271579272604586965629809)
        ·
          refine ⟨118703684454453440224222357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158271579272604586965629809 118703684454453440224222357)
          ·
            refine ⟨5564235208802505010510423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118703684454453440224222357 5564235208802505010510423)
            ·
              refine ⟨8346352813203757515765635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564235208802505010510423 8346352813203757515765635)
              ·
                refine ⟨12519529219805636273648453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346352813203757515765635 12519529219805636273648453)
                ·
                  refine ⟨2347411728713556801309085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12519529219805636273648453 2347411728713556801309085)
                  ·
                    refine ⟨880279398267583800490907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347411728713556801309085 880279398267583800490907)
                    ·
                      rfl

theorem cell22_2571507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 3].length) (baseStart_2571507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571507 prefixEnd_2571507 := by exact prefixLift 2571507
  have htrace : WordTrace (prefixWord ++ tailWord_2571507) baseStart_2571507 baseEnd_2571507 := by
    simpa [prefixWord, tailWord_2571507, baseEnd_2571507] using wordTrace_append hprefix tailTrace_2571507
  have hstable : (prefixWord ++ tailWord_2571507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571507).length < 2 ^ (prefixWord ++ tailWord_2571507).sum := by decide
  have hdescent : baseEnd_2571507 < baseStart_2571507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571524 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2571524 : Nat := 118140960795 + 2571524 * 2 ^ 59
def prefixEnd_2571524 : Nat := 4983230072969 + 3 ^ 40 * 2571524 * 2
def baseEnd_2571524 : Nat := 880285217715001422815855

theorem tailTrace_2571524 : CollatzResearch.WordTrace tailWord_2571524 prefixEnd_2571524 880285217715001422815855 := by
  unfold tailWord_2571524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46895592767907602089648813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62527457023876802786198417 46895592767907602089648813)
  ·
    refine ⟨17585847287965350783618305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46895592767907602089648813 17585847287965350783618305)
    ·
      refine ⟨13189385465974013087713729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17585847287965350783618305 13189385465974013087713729)
      ·
        refine ⟨9892039099480509815785297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13189385465974013087713729 9892039099480509815785297)
        ·
          refine ⟨7419029324610382361838973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892039099480509815785297 7419029324610382361838973)
          ·
            refine ⟨2782135996728893385689615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7419029324610382361838973 2782135996728893385689615)
            ·
              refine ⟨4173203995093340078534423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782135996728893385689615 4173203995093340078534423)
              ·
                refine ⟨6259805992640010117801635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173203995093340078534423 6259805992640010117801635)
                ·
                  refine ⟨9389708988960015176702453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259805992640010117801635 9389708988960015176702453)
                  ·
                    refine ⟨880285217715001422815855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9389708988960015176702453 880285217715001422815855)
                    ·
                      rfl

theorem cell22_2571524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2571524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571524 prefixEnd_2571524 := by exact prefixLift 2571524
  have htrace : WordTrace (prefixWord ++ tailWord_2571524) baseStart_2571524 baseEnd_2571524 := by
    simpa [prefixWord, tailWord_2571524, baseEnd_2571524] using wordTrace_append hprefix tailTrace_2571524
  have hstable : (prefixWord ++ tailWord_2571524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571524).length < 2 ^ (prefixWord ++ tailWord_2571524).sum := by decide
  have hdescent : baseEnd_2571524 < baseStart_2571524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571554 : List Nat := [3, 3, 1, 1, 5, 1, 8]
def baseStart_2571554 : Nat := 118140960795 + 2571554 * 2 ^ 59
def prefixEnd_2571554 : Nat := 4983230072969 + 3 ^ 40 * 2571554 * 2
def baseEnd_2571554 : Nat := 32603536567707086835769

theorem tailTrace_2571554 : CollatzResearch.WordTrace tailWord_2571554 prefixEnd_2571554 32603536567707086835769 := by
  unfold tailWord_2571554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23448069931426629825722429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62528186483804346201926477 23448069931426629825722429)
  ·
    refine ⟨8793026224284986184645911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23448069931426629825722429 8793026224284986184645911)
    ·
      refine ⟨13189539336427479276968867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793026224284986184645911 13189539336427479276968867)
      ·
        refine ⟨19784309004641218915453301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13189539336427479276968867 19784309004641218915453301)
        ·
          refine ⟨1854778969185114273323747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19784309004641218915453301 1854778969185114273323747)
          ·
            refine ⟨2782168453777671409985621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854778969185114273323747 2782168453777671409985621)
            ·
              refine ⟨32603536567707086835769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2782168453777671409985621 32603536567707086835769)
              ·
                rfl

theorem cell22_2571554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 8].length) (baseStart_2571554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571554 prefixEnd_2571554 := by exact prefixLift 2571554
  have htrace : WordTrace (prefixWord ++ tailWord_2571554) baseStart_2571554 baseEnd_2571554 := by
    simpa [prefixWord, tailWord_2571554, baseEnd_2571554] using wordTrace_append hprefix tailTrace_2571554
  have hstable : (prefixWord ++ tailWord_2571554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571554).length < 2 ^ (prefixWord ++ tailWord_2571554).sum := by decide
  have hdescent : baseEnd_2571554 < baseStart_2571554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571569 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_2571569 : Nat := 118140960795 + 2571569 * 2 ^ 59
def prefixEnd_2571569 : Nat := 4983230072969 + 3 ^ 40 * 2571569 * 2
def baseEnd_2571569 : Nat := 880300622134636305440717

theorem tailTrace_2571569 : CollatzResearch.WordTrace tailWord_2571569 prefixEnd_2571569 880300622134636305440717 := by
  unfold tailWord_2571569
  simp only [CollatzResearch.WordTrace]
  refine ⟨93792826820652176864685761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62528551213768117909790507 93792826820652176864685761)
  ·
    refine ⟨70344620115489132648514321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93792826820652176864685761 70344620115489132648514321)
    ·
      refine ⟨52758465086616849486385741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70344620115489132648514321 52758465086616849486385741)
      ·
        refine ⟨19784424407481318557394653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52758465086616849486385741 19784424407481318557394653)
        ·
          refine ⟨7419159152805494459022995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19784424407481318557394653 7419159152805494459022995)
          ·
            refine ⟨11128738729208241688534493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419159152805494459022995 11128738729208241688534493)
            ·
              refine ⟨4173277023453090633200435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11128738729208241688534493 4173277023453090633200435)
              ·
                refine ⟨6259915535179635949800653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173277023453090633200435 6259915535179635949800653)
                ·
                  refine ⟨2347468325692363481175245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6259915535179635949800653 2347468325692363481175245)
                  ·
                    refine ⟨880300622134636305440717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347468325692363481175245 880300622134636305440717)
                    ·
                      rfl

theorem cell22_2571569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_2571569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571569 prefixEnd_2571569 := by exact prefixLift 2571569
  have htrace : WordTrace (prefixWord ++ tailWord_2571569) baseStart_2571569 baseEnd_2571569 := by
    simpa [prefixWord, tailWord_2571569, baseEnd_2571569] using wordTrace_append hprefix tailTrace_2571569
  have hstable : (prefixWord ++ tailWord_2571569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571569).length < 2 ^ (prefixWord ++ tailWord_2571569).sum := by decide
  have hdescent : baseEnd_2571569 < baseStart_2571569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571704 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_2571704 : Nat := 118140960795 + 2571704 * 2 ^ 59
def prefixEnd_2571704 : Nat := 4983230072969 + 3 ^ 40 * 2571704 * 2
def baseEnd_2571704 : Nat := 880346835393540953315303

theorem tailTrace_2571704 : CollatzResearch.WordTrace tailWord_2571704 prefixEnd_2571704 880346835393540953315303 := by
  unfold tailWord_2571704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46898875337581547460425083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62531833783442063280566777 46898875337581547460425083)
  ·
    refine ⟨70348313006372321190637625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46898875337581547460425083 70348313006372321190637625)
    ·
      refine ⟨52761234754779240892978219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70348313006372321190637625 52761234754779240892978219)
      ·
        refine ⟨79141852132168861339467329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52761234754779240892978219 79141852132168861339467329)
        ·
          refine ⟨59356389099126646004600497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79141852132168861339467329 59356389099126646004600497)
          ·
            refine ⟨44517291824344984503450373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59356389099126646004600497 44517291824344984503450373)
            ·
              refine ⟨8346992217064684594396945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44517291824344984503450373 8346992217064684594396945)
              ·
                refine ⟨6260244162798513445797709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8346992217064684594396945 6260244162798513445797709)
                ·
                  refine ⟨2347591561049442542174141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6260244162798513445797709 2347591561049442542174141)
                  ·
                    refine ⟨880346835393540953315303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347591561049442542174141 880346835393540953315303)
                    ·
                      rfl

theorem cell22_2571704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_2571704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571704 prefixEnd_2571704 := by exact prefixLift 2571704
  have htrace : WordTrace (prefixWord ++ tailWord_2571704) baseStart_2571704 baseEnd_2571704 := by
    simpa [prefixWord, tailWord_2571704, baseEnd_2571704] using wordTrace_append hprefix tailTrace_2571704
  have hstable : (prefixWord ++ tailWord_2571704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571704).length < 2 ^ (prefixWord ++ tailWord_2571704).sum := by decide
  have hdescent : baseEnd_2571704 < baseStart_2571704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571751 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 5]
def baseStart_2571751 : Nat := 118140960795 + 2571751 * 2 ^ 59
def prefixEnd_2571751 : Nat := 4983230072969 + 3 ^ 40 * 2571751 * 2
def baseEnd_2571751 : Nat := 293454308151349499130053

theorem tailTrace_2571751 : CollatzResearch.WordTrace tailWord_2571751 prefixEnd_2571751 293454308151349499130053 := by
  unfold tailWord_2571751
  simp only [CollatzResearch.WordTrace]
  refine ⟨93799464905992821947811107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62532976603995214631874071 93799464905992821947811107)
  ·
    refine ⟨140699197358989232921716661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93799464905992821947811107 140699197358989232921716661)
    ·
      refine ⟨13190549752405240586410937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140699197358989232921716661 13190549752405240586410937)
      ·
        refine ⟨9892912314303930439808203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13190549752405240586410937 9892912314303930439808203)
        ·
          refine ⟨14839368471455895659712305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9892912314303930439808203 14839368471455895659712305)
          ·
            refine ⟨11129526353591921744784229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14839368471455895659712305 11129526353591921744784229)
            ·
              refine ⟨2086786191298485327147043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11129526353591921744784229 2086786191298485327147043)
              ·
                refine ⟨3130179286947727990720565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086786191298485327147043 3130179286947727990720565)
                ·
                  refine ⟨293454308151349499130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130179286947727990720565 293454308151349499130053)
                  ·
                    rfl

theorem cell22_2571751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 5].length) (baseStart_2571751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571751 prefixEnd_2571751 := by exact prefixLift 2571751
  have htrace : WordTrace (prefixWord ++ tailWord_2571751) baseStart_2571751 baseEnd_2571751 := by
    simpa [prefixWord, tailWord_2571751, baseEnd_2571751] using wordTrace_append hprefix tailTrace_2571751
  have hstable : (prefixWord ++ tailWord_2571751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571751).length < 2 ^ (prefixWord ++ tailWord_2571751).sum := by decide
  have hdescent : baseEnd_2571751 < baseStart_2571751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571811 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_2571811 : Nat := 118140960795 + 2571811 * 2 ^ 59
def prefixEnd_2571811 : Nat := 4983230072969 + 3 ^ 40 * 2571811 * 2
def baseEnd_2571811 : Nat := 880383463680228340889975

theorem tailTrace_2571811 : CollatzResearch.WordTrace tailWord_2571811 prefixEnd_2571811 880383463680228340889975 := by
  unfold tailWord_2571811
  simp only [CollatzResearch.WordTrace]
  refine ⟨93801653285775452194995287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62534435523850301463330191 93801653285775452194995287)
  ·
    refine ⟨140702479928663178292492931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93801653285775452194995287 140702479928663178292492931)
    ·
      refine ⟨211053719892994767438739397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140702479928663178292492931 211053719892994767438739397)
      ·
        refine ⟨39572572479936518894763637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211053719892994767438739397 39572572479936518894763637)
        ·
          refine ⟨3709928669994048646384091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39572572479936518894763637 3709928669994048646384091)
          ·
            refine ⟨5564893004991072969576137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709928669994048646384091 5564893004991072969576137)
            ·
              refine ⟨4173669753743304727182103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5564893004991072969576137 4173669753743304727182103)
              ·
                refine ⟨6260504630614957090773155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173669753743304727182103 6260504630614957090773155)
                ·
                  refine ⟨9390756945922435636159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260504630614957090773155 9390756945922435636159733)
                  ·
                    refine ⟨880383463680228340889975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9390756945922435636159733 880383463680228340889975)
                    ·
                      rfl

theorem cell22_2571811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_2571811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571811 prefixEnd_2571811 := by exact prefixLift 2571811
  have htrace : WordTrace (prefixWord ++ tailWord_2571811) baseStart_2571811 baseEnd_2571811 := by
    simpa [prefixWord, tailWord_2571811, baseEnd_2571811] using wordTrace_append hprefix tailTrace_2571811
  have hstable : (prefixWord ++ tailWord_2571811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571811).length < 2 ^ (prefixWord ++ tailWord_2571811).sum := by decide
  have hdescent : baseEnd_2571811 < baseStart_2571811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571830 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2571830 : Nat := 118140960795 + 2571830 * 2 ^ 59
def prefixEnd_2571830 : Nat := 4983230072969 + 3 ^ 40 * 2571830 * 2
def baseEnd_2571830 : Nat := 293463322589506208221639

theorem tailTrace_2571830 : CollatzResearch.WordTrace tailWord_2571830 prefixEnd_2571830 293463322589506208221639 := by
  unfold tailWord_2571830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862646642044163652496059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62534897515137745626624629 5862646642044163652496059)
  ·
    refine ⟨8793969963066245478744089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862646642044163652496059 8793969963066245478744089)
    ·
      refine ⟨6595477472299684109058067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8793969963066245478744089 6595477472299684109058067)
      ·
        refine ⟨9893216208449526163587101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595477472299684109058067 9893216208449526163587101)
        ·
          refine ⟨3709956078168572311345163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9893216208449526163587101 3709956078168572311345163)
          ·
            refine ⟨5564934117252858467017745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709956078168572311345163 5564934117252858467017745)
            ·
              refine ⟨4173700587939643850263309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5564934117252858467017745 4173700587939643850263309)
              ·
                refine ⟨1565137720477366443848741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4173700587939643850263309 1565137720477366443848741)
                ·
                  refine ⟨293463322589506208221639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565137720477366443848741 293463322589506208221639)
                  ·
                    rfl

theorem cell22_2571830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2571830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571830 prefixEnd_2571830 := by exact prefixLift 2571830
  have htrace : WordTrace (prefixWord ++ tailWord_2571830) baseStart_2571830 baseEnd_2571830 := by
    simpa [prefixWord, tailWord_2571830, baseEnd_2571830] using wordTrace_append hprefix tailTrace_2571830
  have hstable : (prefixWord ++ tailWord_2571830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571830).length < 2 ^ (prefixWord ++ tailWord_2571830).sum := by decide
  have hdescent : baseEnd_2571830 < baseStart_2571830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571856 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_2571856 : Nat := 118140960795 + 2571856 * 2 ^ 59
def prefixEnd_2571856 : Nat := 4983230072969 + 3 ^ 40 * 2571856 * 2
def baseEnd_2571856 : Nat := 880398868099863223514837

theorem tailTrace_2571856 : CollatzResearch.WordTrace tailWord_2571856 prefixEnd_2571856 880398868099863223514837 := by
  unfold tailWord_2571856
  simp only [CollatzResearch.WordTrace]
  refine ⟨46901647285306212440191711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62535529713741616586922281 46901647285306212440191711)
  ·
    refine ⟨70352470927959318660287567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46901647285306212440191711 70352470927959318660287567)
    ·
      refine ⟨105528706391938977990431351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70352470927959318660287567 105528706391938977990431351)
      ·
        refine ⟨158293059587908466985647027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105528706391938977990431351 158293059587908466985647027)
        ·
          refine ⟨237439589381862700478470541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158293059587908466985647027 237439589381862700478470541)
          ·
            refine ⟨89039846018198512679426453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237439589381862700478470541 89039846018198512679426453)
            ·
              refine ⟨4173742782103055281848115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89039846018198512679426453 4173742782103055281848115)
              ·
                refine ⟨6260614173154582922772173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173742782103055281848115 6260614173154582922772173)
                ·
                  refine ⟨2347730314932968596039565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6260614173154582922772173 2347730314932968596039565)
                  ·
                    refine ⟨880398868099863223514837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347730314932968596039565 880398868099863223514837)
                    ·
                      rfl

theorem cell22_2571856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_2571856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571856 prefixEnd_2571856 := by exact prefixLift 2571856
  have htrace : WordTrace (prefixWord ++ tailWord_2571856) baseStart_2571856 baseEnd_2571856 := by
    simpa [prefixWord, tailWord_2571856, baseEnd_2571856] using wordTrace_append hprefix tailTrace_2571856
  have hstable : (prefixWord ++ tailWord_2571856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571856).length < 2 ^ (prefixWord ++ tailWord_2571856).sum := by decide
  have hdescent : baseEnd_2571856 < baseStart_2571856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571862 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2571862 : Nat := 118140960795 + 2571862 * 2 ^ 59
def prefixEnd_2571862 : Nat := 4983230072969 + 3 ^ 40 * 2571862 * 2
def baseEnd_2571862 : Nat := 880400922022481207864819

theorem tailTrace_2571862 : CollatzResearch.WordTrace tailWord_2571862 prefixEnd_2571862 880400922022481207864819 := by
  unfold tailWord_2571862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862719588036917994068865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62535675605727125270067893 5862719588036917994068865)
  ·
    refine ⟨4397039691027688495551649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5862719588036917994068865 4397039691027688495551649)
    ·
      refine ⟨3297779768270766371663737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397039691027688495551649 3297779768270766371663737)
      ·
        refine ⟨2473334826203074778747803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3297779768270766371663737 2473334826203074778747803)
        ·
          refine ⟨3710002239304612168121705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473334826203074778747803 3710002239304612168121705)
          ·
            refine ⟨2782501679478459126091279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710002239304612168121705 2782501679478459126091279)
            ·
              refine ⟨4173752519217688689136919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782501679478459126091279 4173752519217688689136919)
              ·
                refine ⟨6260628778826533033705379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173752519217688689136919 6260628778826533033705379)
                ·
                  refine ⟨9390943168239799550558069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6260628778826533033705379 9390943168239799550558069)
                  ·
                    refine ⟨880400922022481207864819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9390943168239799550558069 880400922022481207864819)
                    ·
                      rfl

theorem cell22_2571862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2571862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571862 prefixEnd_2571862 := by exact prefixLift 2571862
  have htrace : WordTrace (prefixWord ++ tailWord_2571862) baseStart_2571862 baseEnd_2571862 := by
    simpa [prefixWord, tailWord_2571862, baseEnd_2571862] using wordTrace_append hprefix tailTrace_2571862
  have hstable : (prefixWord ++ tailWord_2571862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571862).length < 2 ^ (prefixWord ++ tailWord_2571862).sum := by decide
  have hdescent : baseEnd_2571862 < baseStart_2571862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571890 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_2571890 : Nat := 118140960795 + 2571890 * 2 ^ 59
def prefixEnd_2571890 : Nat := 4983230072969 + 3 ^ 40 * 2571890 * 2
def baseEnd_2571890 : Nat := 880410506994698468164733

theorem tailTrace_2571890 : CollatzResearch.WordTrace tailWord_2571890 prefixEnd_2571890 880410506994698468164733 := by
  unfold tailWord_2571890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451133663122312171780281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62536356434992832458080749 23451133663122312171780281)
  ·
    refine ⟨17588350247341734128835211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23451133663122312171780281 17588350247341734128835211)
    ·
      refine ⟨26382525371012601193252817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17588350247341734128835211 26382525371012601193252817)
      ·
        refine ⟨19786894028259450894939613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26382525371012601193252817 19786894028259450894939613)
        ·
          refine ⟨7420085260597294085602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19786894028259450894939613 7420085260597294085602355)
          ·
            refine ⟨11130127890895941128403533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420085260597294085602355 11130127890895941128403533)
            ·
              refine ⟨4173797959085977923151325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11130127890895941128403533 4173797959085977923151325)
              ·
                refine ⟨1565174234657241721181747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4173797959085977923151325 1565174234657241721181747)
                ·
                  refine ⟨2347761351985862581772621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565174234657241721181747 2347761351985862581772621)
                  ·
                    refine ⟨880410506994698468164733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347761351985862581772621 880410506994698468164733)
                    ·
                      rfl

theorem cell22_2571890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_2571890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571890 prefixEnd_2571890 := by exact prefixLift 2571890
  have htrace : WordTrace (prefixWord ++ tailWord_2571890) baseStart_2571890 baseEnd_2571890 := by
    simpa [prefixWord, tailWord_2571890, baseEnd_2571890] using wordTrace_append hprefix tailTrace_2571890
  have hstable : (prefixWord ++ tailWord_2571890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571890).length < 2 ^ (prefixWord ++ tailWord_2571890).sum := by decide
  have hdescent : baseEnd_2571890 < baseStart_2571890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571959 : List Nat := [1, 1, 3, 1, 5, 11]
def baseStart_2571959 : Nat := 118140960795 + 2571959 * 2 ^ 59
def prefixEnd_2571959 : Nat := 4983230072969 + 3 ^ 40 * 2571959 * 2
def baseEnd_2571959 : Nat := 10869557124750682570241

theorem tailTrace_2571959 : CollatzResearch.WordTrace tailWord_2571959 prefixEnd_2571959 10869557124750682570241 := by
  unfold tailWord_2571959
  simp only [CollatzResearch.WordTrace]
  refine ⟨93807051289239273471382931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62538034192826182314255287 93807051289239273471382931)
  ·
    refine ⟨140710576933858910207074397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93807051289239273471382931 140710576933858910207074397)
    ·
      refine ⟨52766466350197091327652899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140710576933858910207074397 52766466350197091327652899)
      ·
        refine ⟨79149699525295636991479349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52766466350197091327652899 79149699525295636991479349)
        ·
          refine ⟨7420284330496465967951189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79149699525295636991479349 7420284330496465967951189)
          ·
            refine ⟨10869557124750682570241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7420284330496465967951189 10869557124750682570241)
            ·
              rfl

theorem cell22_2571959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 11].length) (baseStart_2571959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571959 prefixEnd_2571959 := by exact prefixLift 2571959
  have htrace : WordTrace (prefixWord ++ tailWord_2571959) baseStart_2571959 baseEnd_2571959 := by
    simpa [prefixWord, tailWord_2571959, baseEnd_2571959] using wordTrace_append hprefix tailTrace_2571959
  have hstable : (prefixWord ++ tailWord_2571959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571959).length < 2 ^ (prefixWord ++ tailWord_2571959).sum := by decide
  have hdescent : baseEnd_2571959 < baseStart_2571959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571961 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_2571961 : Nat := 118140960795 + 2571961 * 2 ^ 59
def prefixEnd_2571961 : Nat := 4983230072969 + 3 ^ 40 * 2571961 * 2
def baseEnd_2571961 : Nat := 880434811745677949639515

theorem tailTrace_2571961 : CollatzResearch.WordTrace tailWord_2571961 prefixEnd_2571961 880434811745677949639515 := by
  unfold tailWord_2571961
  simp only [CollatzResearch.WordTrace]
  refine ⟨93807124235232027812955737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62538082823488018541970491 93807124235232027812955737)
  ·
    refine ⟨70355343176424020859716803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93807124235232027812955737 70355343176424020859716803)
    ·
      refine ⟨105533014764636031289575205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70355343176424020859716803 105533014764636031289575205)
      ·
        refine ⟨19787440268369255866795351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105533014764636031289575205 19787440268369255866795351)
        ·
          refine ⟨29681160402553883800193027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19787440268369255866795351 29681160402553883800193027)
          ·
            refine ⟨44521740603830825700289541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29681160402553883800193027 44521740603830825700289541)
            ·
              refine ⟨8347826363218279818804289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44521740603830825700289541 8347826363218279818804289)
              ·
                refine ⟨6260869772413709864103217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8347826363218279818804289 6260869772413709864103217)
                ·
                  refine ⟨4695652329310282398077413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6260869772413709864103217 4695652329310282398077413)
                  ·
                    refine ⟨880434811745677949639515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695652329310282398077413 880434811745677949639515)
                    ·
                      rfl

theorem cell22_2571961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_2571961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2571961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2571961 prefixEnd_2571961 := by exact prefixLift 2571961
  have htrace : WordTrace (prefixWord ++ tailWord_2571961) baseStart_2571961 baseEnd_2571961 := by
    simpa [prefixWord, tailWord_2571961, baseEnd_2571961] using wordTrace_append hprefix tailTrace_2571961
  have hstable : (prefixWord ++ tailWord_2571961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571961).length < 2 ^ (prefixWord ++ tailWord_2571961).sum := by decide
  have hdescent : baseEnd_2571961 < baseStart_2571961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572089 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 5]
def baseStart_2572089 : Nat := 118140960795 + 2572089 * 2 ^ 59
def prefixEnd_2572089 : Nat := 4983230072969 + 3 ^ 40 * 2572089 * 2
def baseEnd_2572089 : Nat := 293492876253842760813041

theorem tailTrace_2572089 : CollatzResearch.WordTrace tailWord_2572089 prefixEnd_2572089 293492876253842760813041 := by
  unfold tailWord_2572089
  simp only [CollatzResearch.WordTrace]
  refine ⟨93811792778768305673615321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62541195185845537115743547 93811792778768305673615321)
  ·
    refine ⟨70358844584076229255211491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93811792778768305673615321 70358844584076229255211491)
    ·
      refine ⟨105538266876114343882817237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70358844584076229255211491 105538266876114343882817237)
      ·
        refine ⟨2473553129908929934753529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 105538266876114343882817237 2473553129908929934753529)
        ·
          refine ⟨1855164847431697451065147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2473553129908929934753529 1855164847431697451065147)
          ·
            refine ⟨2782747271147546176597721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855164847431697451065147 2782747271147546176597721)
            ·
              refine ⟨2087060453360659632448291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782747271147546176597721 2087060453360659632448291)
              ·
                refine ⟨3130590680040989448672437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087060453360659632448291 3130590680040989448672437)
                ·
                  refine ⟨293492876253842760813041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130590680040989448672437 293492876253842760813041)
                  ·
                    rfl

theorem cell22_2572089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_2572089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572089 prefixEnd_2572089 := by exact prefixLift 2572089
  have htrace : WordTrace (prefixWord ++ tailWord_2572089) baseStart_2572089 baseEnd_2572089 := by
    simpa [prefixWord, tailWord_2572089, baseEnd_2572089] using wordTrace_append hprefix tailTrace_2572089
  have hstable : (prefixWord ++ tailWord_2572089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572089).length < 2 ^ (prefixWord ++ tailWord_2572089).sum := by decide
  have hdescent : baseEnd_2572089 < baseStart_2572089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572102 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2572102 : Nat := 118140960795 + 2572102 * 2 ^ 59
def prefixEnd_2572102 : Nat := 4983230072969 + 3 ^ 40 * 2572102 * 2
def baseEnd_2572102 : Nat := 880483078927200581864083

theorem tailTrace_2572102 : CollatzResearch.WordTrace tailWord_2572102 prefixEnd_2572102 880483078927200581864083 := by
  unfold tailWord_2572102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931633341491287777932455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62541511285147472595892373 2931633341491287777932455)
  ·
    refine ⟨4397450012236931666898683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931633341491287777932455 4397450012236931666898683)
    ·
      refine ⟨6596175018355397500348025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397450012236931666898683 6596175018355397500348025)
      ·
        refine ⟨4947131263766548125261019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6596175018355397500348025 4947131263766548125261019)
        ·
          refine ⟨7420696895649822187891529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947131263766548125261019 7420696895649822187891529)
          ·
            refine ⟨5565522671737366640918647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7420696895649822187891529 5565522671737366640918647)
            ·
              refine ⟨8348284007606049961377971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5565522671737366640918647 8348284007606049961377971)
              ·
                refine ⟨12522426011409074942066957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348284007606049961377971 12522426011409074942066957)
                ·
                  refine ⟨4695909754278403103275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12522426011409074942066957 4695909754278403103275109)
                  ·
                    refine ⟨880483078927200581864083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695909754278403103275109 880483078927200581864083)
                    ·
                      rfl

theorem cell22_2572102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2572102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572102 prefixEnd_2572102 := by exact prefixLift 2572102
  have htrace : WordTrace (prefixWord ++ tailWord_2572102) baseStart_2572102 baseEnd_2572102 := by
    simpa [prefixWord, tailWord_2572102, baseEnd_2572102] using wordTrace_append hprefix tailTrace_2572102
  have hstable : (prefixWord ++ tailWord_2572102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572102).length < 2 ^ (prefixWord ++ tailWord_2572102).sum := by decide
  have hdescent : baseEnd_2572102 < baseStart_2572102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572113 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2572113 : Nat := 118140960795 + 2572113 * 2 ^ 59
def prefixEnd_2572113 : Nat := 4983230072969 + 3 ^ 40 * 2572113 * 2
def baseEnd_2572113 : Nat := 880486844452000219839049

theorem tailTrace_2572113 : CollatzResearch.WordTrace tailWord_2572113 prefixEnd_2572113 880486844452000219839049 := by
  unfold tailWord_2572113
  simp only [CollatzResearch.WordTrace]
  refine ⟨93812668130681357772488993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62541778753787571848325995 93812668130681357772488993)
  ·
    refine ⟨70359501098011018329366745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93812668130681357772488993 70359501098011018329366745)
    ·
      refine ⟨52769625823508263747025059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70359501098011018329366745 52769625823508263747025059)
      ·
        refine ⟨79154438735262395620537589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52769625823508263747025059 79154438735262395620537589)
        ·
          refine ⟨7420728631430849589425399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79154438735262395620537589 7420728631430849589425399)
          ·
            refine ⟨11131092947146274384138099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420728631430849589425399 11131092947146274384138099)
            ·
              refine ⟨16696639420719411576207149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131092947146274384138099 16696639420719411576207149)
              ·
                refine ⟨6261239782769779341077681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16696639420719411576207149 6261239782769779341077681)
                ·
                  refine ⟨4695929837077334505808261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6261239782769779341077681 4695929837077334505808261)
                  ·
                    refine ⟨880486844452000219839049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695929837077334505808261 880486844452000219839049)
                    ·
                      rfl

theorem cell22_2572113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2572113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572113 prefixEnd_2572113 := by exact prefixLift 2572113
  have htrace : WordTrace (prefixWord ++ tailWord_2572113) baseStart_2572113 baseEnd_2572113 := by
    simpa [prefixWord, tailWord_2572113, baseEnd_2572113] using wordTrace_append hprefix tailTrace_2572113
  have hstable : (prefixWord ++ tailWord_2572113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572113).length < 2 ^ (prefixWord ++ tailWord_2572113).sum := by decide
  have hdescent : baseEnd_2572113 < baseStart_2572113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572130 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2572130 : Nat := 118140960795 + 2572130 * 2 ^ 59
def prefixEnd_2572130 : Nat := 4983230072969 + 3 ^ 40 * 2572130 * 2
def baseEnd_2572130 : Nat := 880492663899417842163997

theorem tailTrace_2572130 : CollatzResearch.WordTrace tailWord_2572130 prefixEnd_2572130 880492663899417842163997 := by
  unfold tailWord_2572130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23453322042904942418964461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62542192114413179783905229 23453322042904942418964461)
  ·
    refine ⟨8794995766089353407111673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23453322042904942418964461 8794995766089353407111673)
    ·
      refine ⟨6596246824567015055333755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8794995766089353407111673 6596246824567015055333755)
      ·
        refine ⟨9894370236850522583000633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596246824567015055333755 9894370236850522583000633)
        ·
          refine ⟨7420777677637891937250475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9894370236850522583000633 7420777677637891937250475)
          ·
            refine ⟨11131166516456837905875713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420777677637891937250475 11131166516456837905875713)
            ·
              refine ⟨8348374887342628429406785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11131166516456837905875713 8348374887342628429406785)
              ·
                refine ⟨6261281165506971322055089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8348374887342628429406785 6261281165506971322055089)
                ·
                  refine ⟨4695960874130228491541317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6261281165506971322055089 4695960874130228491541317)
                  ·
                    refine ⟨880492663899417842163997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4695960874130228491541317 880492663899417842163997)
                    ·
                      rfl

theorem cell22_2572130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2572130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572130 prefixEnd_2572130 := by exact prefixLift 2572130
  have htrace : WordTrace (prefixWord ++ tailWord_2572130) baseStart_2572130 baseEnd_2572130 := by
    simpa [prefixWord, tailWord_2572130, baseEnd_2572130] using wordTrace_append hprefix tailTrace_2572130
  have hstable : (prefixWord ++ tailWord_2572130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572130).length < 2 ^ (prefixWord ++ tailWord_2572130).sum := by decide
  have hdescent : baseEnd_2572130 < baseStart_2572130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572132 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2572132 : Nat := 118140960795 + 2572132 * 2 ^ 59
def prefixEnd_2572132 : Nat := 4983230072969 + 3 ^ 40 * 2572132 * 2
def baseEnd_2572132 : Nat := 880493348540290503613991

theorem tailTrace_2572132 : CollatzResearch.WordTrace tailWord_2572132 prefixEnd_2572132 880493348540290503613991 := by
  unfold tailWord_2572132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46906680558806262008715325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62542240745075016011620433 46906680558806262008715325)
  ·
    refine ⟨17590005209552348253268247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46906680558806262008715325 17590005209552348253268247)
    ·
      refine ⟨26385007814328522379902371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17590005209552348253268247 26385007814328522379902371)
      ·
        refine ⟨39577511721492783569853557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385007814328522379902371 39577511721492783569853557)
        ·
          refine ⟨3710391723889948459673771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39577511721492783569853557 3710391723889948459673771)
          ·
            refine ⟨5565587585834922689510657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710391723889948459673771 5565587585834922689510657)
            ·
              refine ⟨4174190689376192017132993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5565587585834922689510657 4174190689376192017132993)
              ·
                refine ⟨3130643017032144012849745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174190689376192017132993 3130643017032144012849745)
                ·
                  refine ⟨2347982262774108009637309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3130643017032144012849745 2347982262774108009637309)
                  ·
                    refine ⟨880493348540290503613991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347982262774108009637309 880493348540290503613991)
                    ·
                      rfl

theorem cell22_2572132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2572132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572132 prefixEnd_2572132 := by exact prefixLift 2572132
  have htrace : WordTrace (prefixWord ++ tailWord_2572132) baseStart_2572132 baseEnd_2572132 := by
    simpa [prefixWord, tailWord_2572132, baseEnd_2572132] using wordTrace_append hprefix tailTrace_2572132
  have hstable : (prefixWord ++ tailWord_2572132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572132).length < 2 ^ (prefixWord ++ tailWord_2572132).sum := by decide
  have hdescent : baseEnd_2572132 < baseStart_2572132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572156 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_2572156 : Nat := 118140960795 + 2572156 * 2 ^ 59
def prefixEnd_2572156 : Nat := 4983230072969 + 3 ^ 40 * 2572156 * 2
def baseEnd_2572156 : Nat := 293500521410254147004639

theorem tailTrace_2572156 : CollatzResearch.WordTrace tailWord_2572156 prefixEnd_2572156 293500521410254147004639 := by
  unfold tailWord_2572156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46907118234762788058152161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62542824313017050744202881 46907118234762788058152161)
  ·
    refine ⟨35180338676072091043614121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46907118234762788058152161 35180338676072091043614121)
    ·
      refine ⟨26385254007054068282710591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35180338676072091043614121 26385254007054068282710591)
      ·
        refine ⟨39577881010581102424065887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385254007054068282710591 39577881010581102424065887)
        ·
          refine ⟨59366821515871653636098831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39577881010581102424065887 59366821515871653636098831)
          ·
            refine ⟨89050232273807480454148247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59366821515871653636098831 89050232273807480454148247)
            ·
              refine ⟨133575348410711220681222371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89050232273807480454148247 133575348410711220681222371)
              ·
                refine ⟨200363022616066831021833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133575348410711220681222371 200363022616066831021833557)
                ·
                  refine ⟨293500521410254147004639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 200363022616066831021833557 293500521410254147004639)
                  ·
                    rfl

theorem cell22_2572156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_2572156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572156 prefixEnd_2572156 := by exact prefixLift 2572156
  have htrace : WordTrace (prefixWord ++ tailWord_2572156) baseStart_2572156 baseEnd_2572156 := by
    simpa [prefixWord, tailWord_2572156, baseEnd_2572156] using wordTrace_append hprefix tailTrace_2572156
  have hstable : (prefixWord ++ tailWord_2572156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572156).length < 2 ^ (prefixWord ++ tailWord_2572156).sum := by decide
  have hdescent : baseEnd_2572156 < baseStart_2572156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572171 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_2572171 : Nat := 118140960795 + 2572171 * 2 ^ 59
def prefixEnd_2572171 : Nat := 4983230072969 + 3 ^ 40 * 2572171 * 2
def baseEnd_2572171 : Nat := 880506699037307401888871

theorem tailTrace_2572171 : CollatzResearch.WordTrace tailWord_2572171 prefixEnd_2572171 880506699037307401888871 := by
  unfold tailWord_2572171
  simp only [CollatzResearch.WordTrace]
  refine ⟨93814783564471233678100367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62543189042980822452066911 93814783564471233678100367)
  ·
    refine ⟨140722175346706850517150551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93814783564471233678100367 140722175346706850517150551)
    ·
      refine ⟨211083263020060275775725827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140722175346706850517150551 211083263020060275775725827)
      ·
        refine ⟨316624894530090413663588741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211083263020060275775725827 316624894530090413663588741)
        ·
          refine ⟨59367167724391952561922889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316624894530090413663588741 59367167724391952561922889)
          ·
            refine ⟨44525375793293964421442167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59367167724391952561922889 44525375793293964421442167)
            ·
              refine ⟨66788063689940946632163251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44525375793293964421442167 66788063689940946632163251)
              ·
                refine ⟨100182095534911419948244877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66788063689940946632163251 100182095534911419948244877)
                ·
                  refine ⟨37568285825591782480591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100182095534911419948244877 37568285825591782480591829)
                  ·
                    refine ⟨880506699037307401888871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37568285825591782480591829 880506699037307401888871)
                    ·
                      rfl

theorem cell22_2572171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_2572171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572171 prefixEnd_2572171 := by exact prefixLift 2572171
  have htrace : WordTrace (prefixWord ++ tailWord_2572171) baseStart_2572171 baseEnd_2572171 := by
    simpa [prefixWord, tailWord_2572171, baseEnd_2572171] using wordTrace_append hprefix tailTrace_2572171
  have hstable : (prefixWord ++ tailWord_2572171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572171).length < 2 ^ (prefixWord ++ tailWord_2572171).sum := by decide
  have hdescent : baseEnd_2572171 < baseStart_2572171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572325 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 5]
def baseStart_2572325 : Nat := 118140960795 + 2572325 * 2 ^ 59
def prefixEnd_2572325 : Nat := 4983230072969 + 3 ^ 40 * 2572325 * 2
def baseEnd_2572325 : Nat := 293519805461500777846133

theorem tailTrace_2572325 : CollatzResearch.WordTrace tailWord_2572325 prefixEnd_2572325 293519805461500777846133 := by
  unfold tailWord_2572325
  simp only [CollatzResearch.WordTrace]
  refine ⟨93820400405913317979206429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62546933603942211986137619 93820400405913317979206429)
  ·
    refine ⟨35182650152217494242202411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93820400405913317979206429 35182650152217494242202411)
    ·
      refine ⟨52773975228326241363303617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35182650152217494242202411 52773975228326241363303617)
      ·
        refine ⟨39580481421244681022477713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52773975228326241363303617 39580481421244681022477713)
        ·
          refine ⟨29685361065933510766858285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39580481421244681022477713 29685361065933510766858285)
          ·
            refine ⟨11132010399725066537571857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29685361065933510766858285 11132010399725066537571857)
            ·
              refine ⟨8349007799793799903178893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132010399725066537571857 8349007799793799903178893)
              ·
                refine ⟨3130877924922674963692085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8349007799793799903178893 3130877924922674963692085)
                ·
                  refine ⟨293519805461500777846133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3130877924922674963692085 293519805461500777846133)
                  ·
                    rfl

theorem cell22_2572325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_2572325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572325 prefixEnd_2572325 := by exact prefixLift 2572325
  have htrace : WordTrace (prefixWord ++ tailWord_2572325) baseStart_2572325 baseEnd_2572325 := by
    simpa [prefixWord, tailWord_2572325, baseEnd_2572325] using wordTrace_append hprefix tailTrace_2572325
  have hstable : (prefixWord ++ tailWord_2572325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572325).length < 2 ^ (prefixWord ++ tailWord_2572325).sum := by decide
  have hdescent : baseEnd_2572325 < baseStart_2572325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_2572368 : Nat := 118140960795 + 2572368 * 2 ^ 59
def prefixEnd_2572368 : Nat := 4983230072969 + 3 ^ 40 * 2572368 * 2
def baseEnd_2572368 : Nat := 880574136163264554713267

theorem tailTrace_2572368 : CollatzResearch.WordTrace tailWord_2572368 prefixEnd_2572368 880574136163264554713267 := by
  unfold tailWord_2572368
  simp only [CollatzResearch.WordTrace]
  refine ⟨46910984372378768161510879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62547979163171690882014505 46910984372378768161510879)
  ·
    refine ⟨70366476558568152242266319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46910984372378768161510879 70366476558568152242266319)
    ·
      refine ⟨105549714837852228363399479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70366476558568152242266319 105549714837852228363399479)
      ·
        refine ⟨158324572256778342545099219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105549714837852228363399479 158324572256778342545099219)
        ·
          refine ⟨237486858385167513817648829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158324572256778342545099219 237486858385167513817648829)
          ·
            refine ⟨89057571894437817681618311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237486858385167513817648829 89057571894437817681618311)
            ·
              refine ⟨133586357841656726522427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89057571894437817681618311 133586357841656726522427467)
              ·
                refine ⟨200379536762485089783641201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133586357841656726522427467 200379536762485089783641201)
                ·
                  refine ⟨150284652571863817337730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200379536762485089783641201 150284652571863817337730901)
                  ·
                    refine ⟨880574136163264554713267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150284652571863817337730901 880574136163264554713267)
                    ·
                      rfl

theorem cell22_2572368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_2572368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572368 prefixEnd_2572368 := by exact prefixLift 2572368
  have htrace : WordTrace (prefixWord ++ tailWord_2572368) baseStart_2572368 baseEnd_2572368 := by
    simpa [prefixWord, tailWord_2572368, baseEnd_2572368] using wordTrace_append hprefix tailTrace_2572368
  have hstable : (prefixWord ++ tailWord_2572368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572368).length < 2 ^ (prefixWord ++ tailWord_2572368).sum := by decide
  have hdescent : baseEnd_2572368 < baseStart_2572368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572374 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2572374 : Nat := 118140960795 + 2572374 * 2 ^ 59
def prefixEnd_2572374 : Nat := 4983230072969 + 3 ^ 40 * 2572374 * 2
def baseEnd_2572374 : Nat := 880576190085882539063249

theorem tailTrace_2572374 : CollatzResearch.WordTrace tailWord_2572374 prefixEnd_2572374 880576190085882539063249 := by
  unfold tailWord_2572374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863886723920987459233761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62548125055157199565160117 5863886723920987459233761)
  ·
    refine ⟨4397915042940740594425321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5863886723920987459233761 4397915042940740594425321)
    ·
      refine ⟨3298436282205555445818991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397915042940740594425321 3298436282205555445818991)
      ·
        refine ⟨4947654423308333168728487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298436282205555445818991 4947654423308333168728487)
        ·
          refine ⟨7421481634962499753092731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947654423308333168728487 7421481634962499753092731)
          ·
            refine ⟨11132222452443749629639097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421481634962499753092731 11132222452443749629639097)
            ·
              refine ⟨8349166839332812222229323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132222452443749629639097 8349166839332812222229323)
              ·
                refine ⟨12523750258999218333343985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8349166839332812222229323 12523750258999218333343985)
                ·
                  refine ⟨9392812694249413750007989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12523750258999218333343985 9392812694249413750007989)
                  ·
                    refine ⟨880576190085882539063249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9392812694249413750007989 880576190085882539063249)
                    ·
                      rfl

theorem cell22_2572374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2572374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572374 prefixEnd_2572374 := by exact prefixLift 2572374
  have htrace : WordTrace (prefixWord ++ tailWord_2572374) baseStart_2572374 baseEnd_2572374 := by
    simpa [prefixWord, tailWord_2572374, baseEnd_2572374] using wordTrace_append hprefix tailTrace_2572374
  have hstable : (prefixWord ++ tailWord_2572374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572374).length < 2 ^ (prefixWord ++ tailWord_2572374).sum := by decide
  have hdescent : baseEnd_2572374 < baseStart_2572374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572400 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_2572400 : Nat := 118140960795 + 2572400 * 2 ^ 59
def prefixEnd_2572400 : Nat := 4983230072969 + 3 ^ 40 * 2572400 * 2
def baseEnd_2572400 : Nat := 880585090417227137913169

theorem tailTrace_2572400 : CollatzResearch.WordTrace tailWord_2572400 prefixEnd_2572400 880585090417227137913169 := by
  unfold tailWord_2572400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46911567940320802894093327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62548757253761070525457769 46911567940320802894093327)
  ·
    refine ⟨70367351910481204341139991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46911567940320802894093327 70367351910481204341139991)
    ·
      refine ⟨105551027865721806511709987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70367351910481204341139991 105551027865721806511709987)
      ·
        refine ⟨158326541798582709767564981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105551027865721806511709987 158326541798582709767564981)
        ·
          refine ⟨14843113293617129040709217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158326541798582709767564981 14843113293617129040709217)
          ·
            refine ⟨11132334970212846780531913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14843113293617129040709217 11132334970212846780531913)
            ·
              refine ⟨8349251227659635085398935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11132334970212846780531913 8349251227659635085398935)
              ·
                refine ⟨12523876841489452628098403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8349251227659635085398935 12523876841489452628098403)
                ·
                  refine ⟨18785815262234178942147605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12523876841489452628098403 18785815262234178942147605)
                  ·
                    refine ⟨880585090417227137913169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18785815262234178942147605 880585090417227137913169)
                    ·
                      rfl

theorem cell22_2572400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_2572400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572400 prefixEnd_2572400 := by exact prefixLift 2572400
  have htrace : WordTrace (prefixWord ++ tailWord_2572400) baseStart_2572400 baseEnd_2572400 := by
    simpa [prefixWord, tailWord_2572400, baseEnd_2572400] using wordTrace_append hprefix tailTrace_2572400
  have hstable : (prefixWord ++ tailWord_2572400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572400).length < 2 ^ (prefixWord ++ tailWord_2572400).sum := by decide
  have hdescent : baseEnd_2572400 < baseStart_2572400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572402 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2572402 : Nat := 118140960795 + 2572402 * 2 ^ 59
def prefixEnd_2572402 : Nat := 4983230072969 + 3 ^ 40 * 2572402 * 2
def baseEnd_2572402 : Nat := 880585775058099799363163

theorem tailTrace_2572402 : CollatzResearch.WordTrace tailWord_2572402 prefixEnd_2572402 880585775058099799363163 := by
  unfold tailWord_2572402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455802206658590032439865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62548805884422906753172973 23455802206658590032439865)
  ·
    refine ⟨17591851654993942524329899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23455802206658590032439865 17591851654993942524329899)
    ·
      refine ⟨26387777482490913786494849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17591851654993942524329899 26387777482490913786494849)
      ·
        refine ⟨19790833111868185339871137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26387777482490913786494849 19790833111868185339871137)
        ·
          refine ⟨14843124833901139004903353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19790833111868185339871137 14843124833901139004903353)
          ·
            refine ⟨11132343625425854253677515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14843124833901139004903353 11132343625425854253677515)
            ·
              refine ⟨16698515438138781380516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11132343625425854253677515 16698515438138781380516273)
              ·
                refine ⟨12523886578604086035387205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16698515438138781380516273 12523886578604086035387205)
                ·
                  refine ⟨2348228733488266131635101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12523886578604086035387205 2348228733488266131635101)
                  ·
                    refine ⟨880585775058099799363163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348228733488266131635101 880585775058099799363163)
                    ·
                      rfl

theorem cell22_2572402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2572402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572402 prefixEnd_2572402 := by exact prefixLift 2572402
  have htrace : WordTrace (prefixWord ++ tailWord_2572402) baseStart_2572402 baseEnd_2572402 := by
    simpa [prefixWord, tailWord_2572402, baseEnd_2572402] using wordTrace_append hprefix tailTrace_2572402
  have hstable : (prefixWord ++ tailWord_2572402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572402).length < 2 ^ (prefixWord ++ tailWord_2572402).sum := by decide
  have hdescent : baseEnd_2572402 < baseStart_2572402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572475 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_2572475 : Nat := 118140960795 + 2572475 * 2 ^ 59
def prefixEnd_2572475 : Nat := 4983230072969 + 3 ^ 40 * 2572475 * 2
def baseEnd_2572475 : Nat := 880610764449951942287939

theorem tailTrace_2572475 : CollatzResearch.WordTrace tailWord_2572475 prefixEnd_2572475 880610764449951942287939 := by
  unfold tailWord_2572475
  simp only [CollatzResearch.WordTrace]
  refine ⟨93825871355369893597166879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62550580903579929064777919 93825871355369893597166879)
  ·
    refine ⟨140738807033054840395750319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93825871355369893597166879 140738807033054840395750319)
    ·
      refine ⟨211108210549582260593625479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140738807033054840395750319 211108210549582260593625479)
      ·
        refine ⟨316662315824373390890438219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211108210549582260593625479 316662315824373390890438219)
        ·
          refine ⟨474993473736560086335657329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316662315824373390890438219 474993473736560086335657329)
          ·
            refine ⟨356245105302420064751742997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474993473736560086335657329 356245105302420064751742997)
            ·
              refine ⟨16698989311050940535237953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 356245105302420064751742997 16698989311050940535237953)
              ·
                refine ⟨12524241983288205401428465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16698989311050940535237953 12524241983288205401428465)
                ·
                  refine ⟨9393181487466154051071349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12524241983288205401428465 9393181487466154051071349)
                  ·
                    refine ⟨880610764449951942287939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9393181487466154051071349 880610764449951942287939)
                    ·
                      rfl

theorem cell22_2572475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_2572475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572475 prefixEnd_2572475 := by exact prefixLift 2572475
  have htrace : WordTrace (prefixWord ++ tailWord_2572475) baseStart_2572475 baseEnd_2572475 := by
    simpa [prefixWord, tailWord_2572475, baseEnd_2572475] using wordTrace_append hprefix tailTrace_2572475
  have hstable : (prefixWord ++ tailWord_2572475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572475).length < 2 ^ (prefixWord ++ tailWord_2572475).sum := by decide
  have hdescent : baseEnd_2572475 < baseStart_2572475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572505 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 8]
def baseStart_2572505 : Nat := 118140960795 + 2572505 * 2 ^ 59
def prefixEnd_2572505 : Nat := 4983230072969 + 3 ^ 40 * 2572505 * 2
def baseEnd_2572505 : Nat := 293540344687680621345949

theorem tailTrace_2572505 : CollatzResearch.WordTrace tailWord_2572505 prefixEnd_2572505 293540344687680621345949 := by
  unfold tailWord_2572505
  simp only [CollatzResearch.WordTrace]
  refine ⟨93826965545261208720758969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62551310363507472480505979 93826965545261208720758969)
  ·
    refine ⟨70370224158945906540569227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93826965545261208720758969 70370224158945906540569227)
    ·
      refine ⟨105555336238418859810853841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70370224158945906540569227 105555336238418859810853841)
      ·
        refine ⟨79166502178814144858140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105555336238418859810853841 79166502178814144858140381)
        ·
          refine ⟨29687438317055304321802643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79166502178814144858140381 29687438317055304321802643)
          ·
            refine ⟨44531157475582956482703965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29687438317055304321802643 44531157475582956482703965)
            ·
              refine ⟨16699184053343608681013987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44531157475582956482703965 16699184053343608681013987)
              ·
                refine ⟨25048776080015413021520981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699184053343608681013987 25048776080015413021520981)
                ·
                  refine ⟨293540344687680621345949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25048776080015413021520981 293540344687680621345949)
                  ·
                    rfl

theorem cell22_2572505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_2572505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572505 prefixEnd_2572505 := by exact prefixLift 2572505
  have htrace : WordTrace (prefixWord ++ tailWord_2572505) baseStart_2572505 baseEnd_2572505 := by
    simpa [prefixWord, tailWord_2572505, baseEnd_2572505] using wordTrace_append hprefix tailTrace_2572505
  have hstable : (prefixWord ++ tailWord_2572505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572505).length < 2 ^ (prefixWord ++ tailWord_2572505).sum := by decide
  have hdescent : baseEnd_2572505 < baseStart_2572505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572535 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2572535 : Nat := 118140960795 + 2572535 * 2 ^ 59
def prefixEnd_2572535 : Nat := 4983230072969 + 3 ^ 40 * 2572535 * 2
def baseEnd_2572535 : Nat := 880631303676131785787755

theorem tailTrace_2572535 : CollatzResearch.WordTrace tailWord_2572535 prefixEnd_2572535 880631303676131785787755 := by
  unfold tailWord_2572535
  simp only [CollatzResearch.WordTrace]
  refine ⟨93828059735152523844351059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62552039823435015896234039 93828059735152523844351059)
  ·
    refine ⟨140742089602728785766526589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93828059735152523844351059 140742089602728785766526589)
    ·
      refine ⟨52778283601023294662447471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140742089602728785766526589 52778283601023294662447471)
      ·
        refine ⟨79167425401534941993671207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52778283601023294662447471 79167425401534941993671207)
        ·
          refine ⟨118751138102302412990506811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79167425401534941993671207 118751138102302412990506811)
          ·
            refine ⟨178126707153453619485760217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118751138102302412990506811 178126707153453619485760217)
            ·
              refine ⟨133595030365090214614320163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178126707153453619485760217 133595030365090214614320163)
              ·
                refine ⟨200392545547635321921480245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133595030365090214614320163 200392545547635321921480245)
                ·
                  refine ⟨18786801145090811430138773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200392545547635321921480245 18786801145090811430138773)
                  ·
                    refine ⟨880631303676131785787755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18786801145090811430138773 880631303676131785787755)
                    ·
                      rfl

theorem cell22_2572535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2572535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572535 prefixEnd_2572535 := by exact prefixLift 2572535
  have htrace : WordTrace (prefixWord ++ tailWord_2572535) baseStart_2572535 baseEnd_2572535 := by
    simpa [prefixWord, tailWord_2572535, baseEnd_2572535] using wordTrace_append hprefix tailTrace_2572535
  have hstable : (prefixWord ++ tailWord_2572535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572535).length < 2 ^ (prefixWord ++ tailWord_2572535).sum := by decide
  have hdescent : baseEnd_2572535 < baseStart_2572535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572552 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_2572552 : Nat := 118140960795 + 2572552 * 2 ^ 59
def prefixEnd_2572552 : Nat := 4983230072969 + 3 ^ 40 * 2572552 * 2
def baseEnd_2572552 : Nat := 880637123123549408112703

theorem tailTrace_2572552 : CollatzResearch.WordTrace tailWord_2572552 prefixEnd_2572552 880637123123549408112703 := by
  unfold tailWord_2572552
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914339888045467873859955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62552453184060623831813273 46914339888045467873859955)
  ·
    refine ⟨70371509832068201810789933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46914339888045467873859955 70371509832068201810789933)
    ·
      refine ⟨26389316187025575679046225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70371509832068201810789933 26389316187025575679046225)
      ·
        refine ⟨19791987140269181759284669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26389316187025575679046225 19791987140269181759284669)
        ·
          refine ⟨7421995177600943159731751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19791987140269181759284669 7421995177600943159731751)
          ·
            refine ⟨11132992766401414739597627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421995177600943159731751 11132992766401414739597627)
            ·
              refine ⟨16699489149602122109396441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11132992766401414739597627 16699489149602122109396441)
              ·
                refine ⟨12524616862201591582047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16699489149602122109396441 12524616862201591582047331)
                ·
                  refine ⟨18786925293302387373070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12524616862201591582047331 18786925293302387373070997)
                  ·
                    refine ⟨880637123123549408112703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18786925293302387373070997 880637123123549408112703)
                    ·
                      rfl

theorem cell22_2572552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_2572552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572552 prefixEnd_2572552 := by exact prefixLift 2572552
  have htrace : WordTrace (prefixWord ++ tailWord_2572552) baseStart_2572552 baseEnd_2572552 := by
    simpa [prefixWord, tailWord_2572552, baseEnd_2572552] using wordTrace_append hprefix tailTrace_2572552
  have hstable : (prefixWord ++ tailWord_2572552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572552).length < 2 ^ (prefixWord ++ tailWord_2572552).sum := by decide
  have hdescent : baseEnd_2572552 < baseStart_2572552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572554 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2572554 : Nat := 118140960795 + 2572554 * 2 ^ 59
def prefixEnd_2572554 : Nat := 4983230072969 + 3 ^ 40 * 2572554 * 2
def baseEnd_2572554 : Nat := 880637807764422069562697

theorem tailTrace_2572554 : CollatzResearch.WordTrace tailWord_2572554 prefixEnd_2572554 880637807764422069562697 := by
  unfold tailWord_2572554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23457188180520922522323179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62552501814722460059528477 23457188180520922522323179)
  ·
    refine ⟨35185782270781383783484769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23457188180520922522323179 35185782270781383783484769)
    ·
      refine ⟨26389336703086037837613577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35185782270781383783484769 26389336703086037837613577)
      ·
        refine ⟨19792002527314528378210183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26389336703086037837613577 19792002527314528378210183)
        ·
          refine ⟨29688003790971792567315275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19792002527314528378210183 29688003790971792567315275)
          ·
            refine ⟨44532005686457688850972913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29688003790971792567315275 44532005686457688850972913)
            ·
              refine ⟨33399004264843266638229685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44532005686457688850972913 33399004264843266638229685)
              ·
                refine ⟨3131156649829056247334033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33399004264843266638229685 3131156649829056247334033)
                ·
                  refine ⟨2348367487371792185500525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131156649829056247334033 2348367487371792185500525)
                  ·
                    refine ⟨880637807764422069562697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348367487371792185500525 880637807764422069562697)
                    ·
                      rfl

theorem cell22_2572554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2572554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572554 prefixEnd_2572554 := by exact prefixLift 2572554
  have htrace : WordTrace (prefixWord ++ tailWord_2572554) baseStart_2572554 baseEnd_2572554 := by
    simpa [prefixWord, tailWord_2572554, baseEnd_2572554] using wordTrace_append hprefix tailTrace_2572554
  have hstable : (prefixWord ++ tailWord_2572554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572554).length < 2 ^ (prefixWord ++ tailWord_2572554).sum := by decide
  have hdescent : baseEnd_2572554 < baseStart_2572554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572567 : List Nat := [1, 1, 3, 4, 1, 3, 1, 8]
def baseStart_2572567 : Nat := 118140960795 + 2572567 * 2 ^ 59
def prefixEnd_2572567 : Nat := 4983230072969 + 3 ^ 40 * 2572567 * 2
def baseEnd_2572567 : Nat := 97849139770010485443073

theorem tailTrace_2572567 : CollatzResearch.WordTrace tailWord_2572567 prefixEnd_2572567 97849139770010485443073 := by
  unfold tailWord_2572567
  simp only [CollatzResearch.WordTrace]
  refine ⟨93829226871036593309515955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62552817914024395539677303 93829226871036593309515955)
  ·
    refine ⟨140743840306554889964273933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93829226871036593309515955 140743840306554889964273933)
    ·
      refine ⟨52778940114958083736602725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140743840306554889964273933 52778940114958083736602725)
      ·
        refine ⟨9896051271554640700613011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52778940114958083736602725 9896051271554640700613011)
        ·
          refine ⟨14844076907331961050919517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896051271554640700613011 14844076907331961050919517)
          ·
            refine ⟨5566528840249485394094819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14844076907331961050919517 5566528840249485394094819)
            ·
              refine ⟨8349793260374228091142229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566528840249485394094819 8349793260374228091142229)
              ·
                refine ⟨97849139770010485443073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8349793260374228091142229 97849139770010485443073)
                ·
                  rfl

theorem cell22_2572567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 8].length) (baseStart_2572567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572567 prefixEnd_2572567 := by exact prefixLift 2572567
  have htrace : WordTrace (prefixWord ++ tailWord_2572567) baseStart_2572567 baseEnd_2572567 := by
    simpa [prefixWord, tailWord_2572567, baseEnd_2572567] using wordTrace_append hprefix tailTrace_2572567
  have hstable : (prefixWord ++ tailWord_2572567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572567).length < 2 ^ (prefixWord ++ tailWord_2572567).sum := by decide
  have hdescent : baseEnd_2572567 < baseStart_2572567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572573 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2572573 : Nat := 118140960795 + 2572573 * 2 ^ 59
def prefixEnd_2572573 : Nat := 4983230072969 + 3 ^ 40 * 2572573 * 2
def baseEnd_2572573 : Nat := 293548103950904117779213

theorem tailTrace_2572573 : CollatzResearch.WordTrace tailWord_2572573 prefixEnd_2572573 293548103950904117779213 := by
  unfold tailWord_2572573
  simp only [CollatzResearch.WordTrace]
  refine ⟨93829445709014856334234373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62552963806009904222822915 93829445709014856334234373)
  ·
    refine ⟨17593021070440285562668945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93829445709014856334234373 17593021070440285562668945)
    ·
      refine ⟨13194765802830214172001709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17593021070440285562668945 13194765802830214172001709)
      ·
        refine ⟨4948037176061330314500641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13194765802830214172001709 4948037176061330314500641)
        ·
          refine ⟨3711027882045997735875481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948037176061330314500641 3711027882045997735875481)
          ·
            refine ⟨2783270911534498301906611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711027882045997735875481 2783270911534498301906611)
            ·
              refine ⟨4174906367301747452859917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783270911534498301906611 4174906367301747452859917)
              ·
                refine ⟨1565589887738155294822469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4174906367301747452859917 1565589887738155294822469)
                ·
                  refine ⟨293548103950904117779213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565589887738155294822469 293548103950904117779213)
                  ·
                    rfl

theorem cell22_2572573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2572573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572573 prefixEnd_2572573 := by exact prefixLift 2572573
  have htrace : WordTrace (prefixWord ++ tailWord_2572573) baseStart_2572573 baseEnd_2572573 := by
    simpa [prefixWord, tailWord_2572573, baseEnd_2572573] using wordTrace_append hprefix tailTrace_2572573
  have hstable : (prefixWord ++ tailWord_2572573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572573).length < 2 ^ (prefixWord ++ tailWord_2572573).sum := by decide
  have hdescent : baseEnd_2572573 < baseStart_2572573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572584 : List Nat := [2, 1, 5, 1, 3, 2, 8]
def baseStart_2572584 : Nat := 118140960795 + 2572584 * 2 ^ 59
def prefixEnd_2572584 : Nat := 4983230072969 + 3 ^ 40 * 2572584 * 2
def baseEnd_2572584 : Nat := 32616595458426370048615

theorem tailTrace_2572584 : CollatzResearch.WordTrace tailWord_2572584 prefixEnd_2572584 32616595458426370048615 := by
  unfold tailWord_2572584
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914923455987502606442403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62553231274650003475256537 46914923455987502606442403)
  ·
    refine ⟨70372385183981253909663605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46914923455987502606442403 70372385183981253909663605)
    ·
      refine ⟨6597411110998242554030963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70372385183981253909663605 6597411110998242554030963)
      ·
        refine ⟨9896116666497363831046445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6597411110998242554030963 9896116666497363831046445)
        ·
          refine ⟨3711043749936511436642417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9896116666497363831046445 3711043749936511436642417)
          ·
            refine ⟨2783282812452383577481813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711043749936511436642417 2783282812452383577481813)
            ·
              refine ⟨32616595458426370048615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2783282812452383577481813 32616595458426370048615)
              ·
                rfl

theorem cell22_2572584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 8].length) (baseStart_2572584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572584 prefixEnd_2572584 := by exact prefixLift 2572584
  have htrace : WordTrace (prefixWord ++ tailWord_2572584) baseStart_2572584 baseEnd_2572584 := by
    simpa [prefixWord, tailWord_2572584, baseEnd_2572584] using wordTrace_append hprefix tailTrace_2572584
  have hstable : (prefixWord ++ tailWord_2572584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572584).length < 2 ^ (prefixWord ++ tailWord_2572584).sum := by decide
  have hdescent : baseEnd_2572584 < baseStart_2572584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572586 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2572586 : Nat := 118140960795 + 2572586 * 2 ^ 59
def prefixEnd_2572586 : Nat := 4983230072969 + 3 ^ 40 * 2572586 * 2
def baseEnd_2572586 : Nat := 880648762018384652762599

theorem tailTrace_2572586 : CollatzResearch.WordTrace tailWord_2572586 prefixEnd_2572586 880648762018384652762599 := by
  unfold tailWord_2572586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23457479964491939888614403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62553279905311839702971741 23457479964491939888614403)
  ·
    refine ⟨35186219946737909832921605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23457479964491939888614403 35186219946737909832921605)
    ·
      refine ⟨6597416240013358093672801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35186219946737909832921605 6597416240013358093672801)
      ·
        refine ⟨4948062180010018570254601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6597416240013358093672801 4948062180010018570254601)
        ·
          refine ⟨3711046635007513927690951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948062180010018570254601 3711046635007513927690951)
          ·
            refine ⟨5566569952511270891536427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711046635007513927690951 5566569952511270891536427)
            ·
              refine ⟨8349854928766906337304641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566569952511270891536427 8349854928766906337304641)
              ·
                refine ⟨6262391196575179752978481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349854928766906337304641 6262391196575179752978481)
                ·
                  refine ⟨4696793397431384814733861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6262391196575179752978481 4696793397431384814733861)
                  ·
                    refine ⟨880648762018384652762599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4696793397431384814733861 880648762018384652762599)
                    ·
                      rfl

theorem cell22_2572586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2572586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572586 prefixEnd_2572586 := by exact prefixLift 2572586
  have htrace : WordTrace (prefixWord ++ tailWord_2572586) baseStart_2572586 baseEnd_2572586 := by
    simpa [prefixWord, tailWord_2572586, baseEnd_2572586] using wordTrace_append hprefix tailTrace_2572586
  have hstable : (prefixWord ++ tailWord_2572586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572586).length < 2 ^ (prefixWord ++ tailWord_2572586).sum := by decide
  have hdescent : baseEnd_2572586 < baseStart_2572586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572590 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_2572590 : Nat := 118140960795 + 2572590 * 2 ^ 59
def prefixEnd_2572590 : Nat := 4983230072969 + 3 ^ 40 * 2572590 * 2
def baseEnd_2572590 : Nat := 293550043766709991887529

theorem tailTrace_2572590 : CollatzResearch.WordTrace tailWord_2572590 prefixEnd_2572590 293550043766709991887529 := by
  unfold tailWord_2572590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728758218744158529700403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62553377166635512158402149 11728758218744158529700403)
  ·
    refine ⟨17593137328116237794550605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11728758218744158529700403 17593137328116237794550605)
    ·
      refine ⟨6597426498043589172956477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17593137328116237794550605 6597426498043589172956477)
      ·
        refine ⟨2474034936766345939858679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6597426498043589172956477 2474034936766345939858679)
        ·
          refine ⟨3711052405149518909788019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474034936766345939858679 3711052405149518909788019)
          ·
            refine ⟨5566578607724278364682029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711052405149518909788019 5566578607724278364682029)
            ·
              refine ⟨2087466977896604386755761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5566578607724278364682029 2087466977896604386755761)
              ·
                refine ⟨1565600233422453290066821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087466977896604386755761 1565600233422453290066821)
                ·
                  refine ⟨293550043766709991887529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565600233422453290066821 293550043766709991887529)
                  ·
                    rfl

theorem cell22_2572590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_2572590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572590 prefixEnd_2572590 := by exact prefixLift 2572590
  have htrace : WordTrace (prefixWord ++ tailWord_2572590) baseStart_2572590 baseEnd_2572590 := by
    simpa [prefixWord, tailWord_2572590, baseEnd_2572590] using wordTrace_append hprefix tailTrace_2572590
  have hstable : (prefixWord ++ tailWord_2572590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572590).length < 2 ^ (prefixWord ++ tailWord_2572590).sum := by decide
  have hdescent : baseEnd_2572590 < baseStart_2572590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572597 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2572597 : Nat := 118140960795 + 2572597 * 2 ^ 59
def prefixEnd_2572597 : Nat := 4983230072969 + 3 ^ 40 * 2572597 * 2
def baseEnd_2572597 : Nat := 880652527543184290737565

theorem tailTrace_2572597 : CollatzResearch.WordTrace tailWord_2572597 prefixEnd_2572597 880652527543184290737565 := by
  unfold tailWord_2572597
  simp only [CollatzResearch.WordTrace]
  refine ⟨93830321060927908433108045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62553547373951938955405363 93830321060927908433108045)
  ·
    refine ⟨35186370397847965662415517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93830321060927908433108045 35186370397847965662415517)
    ·
      refine ⟨13194888899192987123405819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35186370397847965662415517 13194888899192987123405819)
      ·
        refine ⟨19792333348789480685108729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194888899192987123405819 19792333348789480685108729)
        ·
          refine ⟨14844250011592110513831547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19792333348789480685108729 14844250011592110513831547)
          ·
            refine ⟨22266375017388165770747321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844250011592110513831547 22266375017388165770747321)
            ·
              refine ⟨16699781263041124328060491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22266375017388165770747321 16699781263041124328060491)
              ·
                refine ⟨25049671894561686492090737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699781263041124328060491 25049671894561686492090737)
                ·
                  refine ⟨18787253920921264869068053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25049671894561686492090737 18787253920921264869068053)
                  ·
                    refine ⟨880652527543184290737565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18787253920921264869068053 880652527543184290737565)
                    ·
                      rfl

theorem cell22_2572597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2572597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572597 prefixEnd_2572597 := by exact prefixLift 2572597
  have htrace : WordTrace (prefixWord ++ tailWord_2572597) baseStart_2572597 baseEnd_2572597 := by
    simpa [prefixWord, tailWord_2572597, baseEnd_2572597] using wordTrace_append hprefix tailTrace_2572597
  have hstable : (prefixWord ++ tailWord_2572597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572597).length < 2 ^ (prefixWord ++ tailWord_2572597).sum := by decide
  have hdescent : baseEnd_2572597 < baseStart_2572597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572650 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2572650 : Nat := 118140960795 + 2572650 * 2 ^ 59
def prefixEnd_2572650 : Nat := 4983230072969 + 3 ^ 40 * 2572650 * 2
def baseEnd_2572650 : Nat := 880670670526309819162403

theorem tailTrace_2572650 : CollatzResearch.WordTrace tailWord_2572650 prefixEnd_2572650 880670670526309819162403 := by
  unfold tailWord_2572650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23458063532433974621196851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62554836086490598989858269 23458063532433974621196851)
  ·
    refine ⟨35187095298650961931795277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23458063532433974621196851 35187095298650961931795277)
    ·
      refine ⟨13195160736994110724423229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35187095298650961931795277 13195160736994110724423229)
      ·
        refine ⟨4948185276372791521658711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13195160736994110724423229 4948185276372791521658711)
        ·
          refine ⟨7422277914559187282488067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948185276372791521658711 7422277914559187282488067)
          ·
            refine ⟨11133416871838780923732101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7422277914559187282488067 11133416871838780923732101)
            ·
              refine ⟨2087515663469771423199769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11133416871838780923732101 2087515663469771423199769)
              ·
                refine ⟨1565636747602328567399827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087515663469771423199769 1565636747602328567399827)
                ·
                  refine ⟨2348455121403492851099741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565636747602328567399827 2348455121403492851099741)
                  ·
                    refine ⟨880670670526309819162403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348455121403492851099741 880670670526309819162403)
                    ·
                      rfl

theorem cell22_2572650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2572650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572650 prefixEnd_2572650 := by exact prefixLift 2572650
  have htrace : WordTrace (prefixWord ++ tailWord_2572650) baseStart_2572650 baseEnd_2572650 := by
    simpa [prefixWord, tailWord_2572650, baseEnd_2572650] using wordTrace_append hprefix tailTrace_2572650
  have hstable : (prefixWord ++ tailWord_2572650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572650).length < 2 ^ (prefixWord ++ tailWord_2572650).sum := by decide
  have hdescent : baseEnd_2572650 < baseStart_2572650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572657 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 6]
def baseStart_2572657 : Nat := 118140960795 + 2572657 * 2 ^ 59
def prefixEnd_2572657 : Nat := 4983230072969 + 3 ^ 40 * 2572657 * 2
def baseEnd_2572657 : Nat := 293557688923121378079127

theorem tailTrace_2572657 : CollatzResearch.WordTrace tailWord_2572657 prefixEnd_2572657 293557688923121378079127 := by
  unfold tailWord_2572657
  simp only [CollatzResearch.WordTrace]
  refine ⟨93832509440710538680292225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62555006293807025786861483 93832509440710538680292225)
  ·
    refine ⟨70374382080532904010219169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93832509440710538680292225 70374382080532904010219169)
    ·
      refine ⟨52780786560399678007664377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70374382080532904010219169 52780786560399678007664377)
      ·
        refine ⟨39585589920299758505748283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52780786560399678007664377 39585589920299758505748283)
        ·
          refine ⟨59378384880449637758622425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39585589920299758505748283 59378384880449637758622425)
          ·
            refine ⟨44533788660337228318966819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59378384880449637758622425 44533788660337228318966819)
            ·
              refine ⟨66800682990505842478450229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44533788660337228318966819 66800682990505842478450229)
              ·
                refine ⟨6262564030359922732354709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66800682990505842478450229 6262564030359922732354709)
                ·
                  refine ⟨293557688923121378079127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6262564030359922732354709 293557688923121378079127)
                  ·
                    rfl

theorem cell22_2572657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_2572657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572657 prefixEnd_2572657 := by exact prefixLift 2572657
  have htrace : WordTrace (prefixWord ++ tailWord_2572657) baseStart_2572657 baseEnd_2572657 := by
    simpa [prefixWord, tailWord_2572657, baseEnd_2572657] using wordTrace_append hprefix tailTrace_2572657
  have hstable : (prefixWord ++ tailWord_2572657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572657).length < 2 ^ (prefixWord ++ tailWord_2572657).sum := by decide
  have hdescent : baseEnd_2572657 < baseStart_2572657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572706 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2572706 : Nat := 118140960795 + 2572706 * 2 ^ 59
def prefixEnd_2572706 : Nat := 4983230072969 + 3 ^ 40 * 2572706 * 2
def baseEnd_2572706 : Nat := 880689840470744339762231

theorem tailTrace_2572706 : CollatzResearch.WordTrace tailWord_2572706 prefixEnd_2572706 880689840470744339762231 := by
  unfold tailWord_2572706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23458574154383255012206493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62556197745022013365883981 23458574154383255012206493)
  ·
    refine ⟨8796965307893720629577435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23458574154383255012206493 8796965307893720629577435)
    ·
      refine ⟨13195447961840580944366153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796965307893720629577435 13195447961840580944366153)
      ·
        refine ⟨9896585971380435708274615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13195447961840580944366153 9896585971380435708274615)
        ·
          refine ⟨14844878957070653562411923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896585971380435708274615 14844878957070653562411923)
          ·
            refine ⟨22267318435605980343617885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14844878957070653562411923 22267318435605980343617885)
            ·
              refine ⟨8350244413352242628856707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22267318435605980343617885 8350244413352242628856707)
              ·
                refine ⟨12525366620028363943285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8350244413352242628856707 12525366620028363943285061)
                ·
                  refine ⟨2348506241255318239365949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12525366620028363943285061 2348506241255318239365949)
                  ·
                    refine ⟨880689840470744339762231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348506241255318239365949 880689840470744339762231)
                    ·
                      rfl

theorem cell22_2572706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2572706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572706 prefixEnd_2572706 := by exact prefixLift 2572706
  have htrace : WordTrace (prefixWord ++ tailWord_2572706) baseStart_2572706 baseEnd_2572706 := by
    simpa [prefixWord, tailWord_2572706, baseEnd_2572706] using wordTrace_append hprefix tailTrace_2572706
  have hstable : (prefixWord ++ tailWord_2572706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572706).length < 2 ^ (prefixWord ++ tailWord_2572706).sum := by decide
  have hdescent : baseEnd_2572706 < baseStart_2572706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572892 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2572892 : Nat := 118140960795 + 2572892 * 2 ^ 59
def prefixEnd_2572892 : Nat := 4983230072969 + 3 ^ 40 * 2572892 * 2
def baseEnd_2572892 : Nat := 880753512071901854611661

theorem tailTrace_2572892 : CollatzResearch.WordTrace tailWord_2572892 prefixEnd_2572892 880753512071901854611661 := by
  unfold tailWord_2572892
  simp only [CollatzResearch.WordTrace]
  refine ⟨46920540297429586907548465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62560720396572782543397953 46920540297429586907548465)
  ·
    refine ⟨35190405223072190180661349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46920540297429586907548465 35190405223072190180661349)
    ·
      refine ⟨6598200979326035658874003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35190405223072190180661349 6598200979326035658874003)
      ·
        refine ⟨9897301468989053488311005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598200979326035658874003 9897301468989053488311005)
        ·
          refine ⟨3711488050870895058116627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9897301468989053488311005 3711488050870895058116627)
          ·
            refine ⟨5567232076306342587174941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711488050870895058116627 5567232076306342587174941)
            ·
              refine ⟨2087712028614878470190603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5567232076306342587174941 2087712028614878470190603)
              ·
                refine ⟨3131568042922317705285905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087712028614878470190603 3131568042922317705285905)
                ·
                  refine ⟨2348676032191738278964429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131568042922317705285905 2348676032191738278964429)
                  ·
                    refine ⟨880753512071901854611661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348676032191738278964429 880753512071901854611661)
                    ·
                      rfl

theorem cell22_2572892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2572892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572892 prefixEnd_2572892 := by exact prefixLift 2572892
  have htrace : WordTrace (prefixWord ++ tailWord_2572892) baseStart_2572892 baseEnd_2572892 := by
    simpa [prefixWord, tailWord_2572892, baseEnd_2572892] using wordTrace_append hprefix tailTrace_2572892
  have hstable : (prefixWord ++ tailWord_2572892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572892).length < 2 ^ (prefixWord ++ tailWord_2572892).sum := by decide
  have hdescent : baseEnd_2572892 < baseStart_2572892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572978 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_2572978 : Nat := 118140960795 + 2572978 * 2 ^ 59
def prefixEnd_2572978 : Nat := 4983230072969 + 3 ^ 40 * 2572978 * 2
def baseEnd_2572978 : Nat := 293594317209808765653799

theorem tailTrace_2572978 : CollatzResearch.WordTrace tailWord_2572978 prefixEnd_2572978 293594317209808765653799 := by
  unfold tailWord_2572978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461054318136902625681897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62562811515031740335151725 23461054318136902625681897)
  ·
    refine ⟨17595790738602676969261423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23461054318136902625681897 17595790738602676969261423)
    ·
      refine ⟨26393686107904015453892135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595790738602676969261423 26393686107904015453892135)
      ·
        refine ⟨39590529161856023180838203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26393686107904015453892135 39590529161856023180838203)
        ·
          refine ⟨59385793742784034771257305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39590529161856023180838203 59385793742784034771257305)
          ·
            refine ⟨44539345307088026078442979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59385793742784034771257305 44539345307088026078442979)
            ·
              refine ⟨66809017960632039117664469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44539345307088026078442979 66809017960632039117664469)
              ·
                refine ⟨1565836358452313416820261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66809017960632039117664469 1565836358452313416820261)
                ·
                  refine ⟨293594317209808765653799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565836358452313416820261 293594317209808765653799)
                  ·
                    rfl

theorem cell22_2572978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_2572978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2572978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2572978 prefixEnd_2572978 := by exact prefixLift 2572978
  have htrace : WordTrace (prefixWord ++ tailWord_2572978) baseStart_2572978 baseEnd_2572978 := by
    simpa [prefixWord, tailWord_2572978, baseEnd_2572978] using wordTrace_append hprefix tailTrace_2572978
  have hstable : (prefixWord ++ tailWord_2572978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572978).length < 2 ^ (prefixWord ++ tailWord_2572978).sum := by decide
  have hdescent : baseEnd_2572978 < baseStart_2572978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573010 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2573010 : Nat := 118140960795 + 2573010 * 2 ^ 59
def prefixEnd_2573010 : Nat := 4983230072969 + 3 ^ 40 * 2573010 * 2
def baseEnd_2573010 : Nat := 880793905883388880161299

theorem tailTrace_2573010 : CollatzResearch.WordTrace tailWord_2573010 prefixEnd_2573010 880793905883388880161299 := by
  unfold tailWord_2573010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461346102107919991973121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62563589605621119978594989 23461346102107919991973121)
  ·
    refine ⟨17596009576580939993979841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23461346102107919991973121 17596009576580939993979841)
    ·
      refine ⟨13197007182435704995484881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17596009576580939993979841 13197007182435704995484881)
      ·
        refine ⟨9897755386826778746613661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13197007182435704995484881 9897755386826778746613661)
        ·
          refine ⟨3711658270060042029980123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9897755386826778746613661 3711658270060042029980123)
          ·
            refine ⟨5567487405090063044970185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711658270060042029980123 5567487405090063044970185)
            ·
              refine ⟨4175615553817547283727639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5567487405090063044970185 4175615553817547283727639)
              ·
                refine ⟨6263423330726320925591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175615553817547283727639 6263423330726320925591459)
                ·
                  refine ⟨9395134996089481388387189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6263423330726320925591459 9395134996089481388387189)
                  ·
                    refine ⟨880793905883388880161299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9395134996089481388387189 880793905883388880161299)
                    ·
                      rfl

theorem cell22_2573010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2573010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573010 prefixEnd_2573010 := by exact prefixLift 2573010
  have htrace : WordTrace (prefixWord ++ tailWord_2573010) baseStart_2573010 baseEnd_2573010 := by
    simpa [prefixWord, tailWord_2573010, baseEnd_2573010] using wordTrace_append hprefix tailTrace_2573010
  have hstable : (prefixWord ++ tailWord_2573010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573010).length < 2 ^ (prefixWord ++ tailWord_2573010).sum := by decide
  have hdescent : baseEnd_2573010 < baseStart_2573010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573023 : List Nat := [1, 1, 2, 3, 2, 4, 3, 6]
def baseStart_2573023 : Nat := 118140960795 + 2573023 * 2 ^ 59
def prefixEnd_2573023 : Nat := 4983230072969 + 3 ^ 40 * 2573023 * 2
def baseEnd_2573023 : Nat := 97866484005451242176251

theorem tailTrace_2573023 : CollatzResearch.WordTrace tailWord_2573023 prefixEnd_2573023 97866484005451242176251 := by
  unfold tailWord_2573023
  simp only [CollatzResearch.WordTrace]
  refine ⟨93845858557384583188115723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62563905704923055458743815 93845858557384583188115723)
  ·
    refine ⟨140768787836076874782173585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93845858557384583188115723 140768787836076874782173585)
    ·
      refine ⟨105576590877057656086630189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140768787836076874782173585 105576590877057656086630189)
      ·
        refine ⟨39591221578896621032486321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105576590877057656086630189 39591221578896621032486321)
        ·
          refine ⟨29693416184172465774364741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39591221578896621032486321 29693416184172465774364741)
          ·
            refine ⟨5567515534532337332693389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29693416184172465774364741 5567515534532337332693389)
            ·
              refine ⟨2087818325449626499760021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5567515534532337332693389 2087818325449626499760021)
              ·
                refine ⟨97866484005451242176251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2087818325449626499760021 97866484005451242176251)
                ·
                  rfl

theorem cell22_2573023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 6].length) (baseStart_2573023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573023 prefixEnd_2573023 := by exact prefixLift 2573023
  have htrace : WordTrace (prefixWord ++ tailWord_2573023) baseStart_2573023 baseEnd_2573023 := by
    simpa [prefixWord, tailWord_2573023, baseEnd_2573023] using wordTrace_append hprefix tailTrace_2573023
  have hstable : (prefixWord ++ tailWord_2573023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573023).length < 2 ^ (prefixWord ++ tailWord_2573023).sum := by decide
  have hdescent : baseEnd_2573023 < baseStart_2573023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573025 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2573025 : Nat := 118140960795 + 2573025 * 2 ^ 59
def prefixEnd_2573025 : Nat := 4983230072969 + 3 ^ 40 * 2573025 * 2
def baseEnd_2573025 : Nat := 880799040689933841036253

theorem tailTrace_2573025 : CollatzResearch.WordTrace tailWord_2573025 prefixEnd_2573025 880799040689933841036253 := by
  unfold tailWord_2573025
  simp only [CollatzResearch.WordTrace]
  refine ⟨93845931503377337529688529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62563954335584891686459019 93845931503377337529688529)
  ·
    refine ⟨70384448627533003147266397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93845931503377337529688529 70384448627533003147266397)
    ·
      refine ⟨26394168235324876180224899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70384448627533003147266397 26394168235324876180224899)
      ·
        refine ⟨39591252352987314270337349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26394168235324876180224899 39591252352987314270337349)
        ·
          refine ⟨7423359816185121425688253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39591252352987314270337349 7423359816185121425688253)
          ·
            refine ⟨2783759931069420534633095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7423359816185121425688253 2783759931069420534633095)
            ·
              refine ⟨4175639896604130801949643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783759931069420534633095 4175639896604130801949643)
              ·
                refine ⟨6263459844906196202924465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4175639896604130801949643 6263459844906196202924465)
                ·
                  refine ⟨4697594883679647152193349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263459844906196202924465 4697594883679647152193349)
                  ·
                    refine ⟨880799040689933841036253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4697594883679647152193349 880799040689933841036253)
                    ·
                      rfl

theorem cell22_2573025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2573025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573025 prefixEnd_2573025 := by exact prefixLift 2573025
  have htrace : WordTrace (prefixWord ++ tailWord_2573025) baseStart_2573025 baseEnd_2573025 := by
    simpa [prefixWord, tailWord_2573025, baseEnd_2573025] using wordTrace_append hprefix tailTrace_2573025
  have hstable : (prefixWord ++ tailWord_2573025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573025).length < 2 ^ (prefixWord ++ tailWord_2573025).sum := by decide
  have hdescent : baseEnd_2573025 < baseStart_2573025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573044 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2573044 : Nat := 118140960795 + 2573044 * 2 ^ 59
def prefixEnd_2573044 : Nat := 4983230072969 + 3 ^ 40 * 2573044 * 2
def baseEnd_2573044 : Nat := 880805544778224124811195

theorem tailTrace_2573044 : CollatzResearch.WordTrace tailWord_2573044 prefixEnd_2573044 880805544778224124811195 := by
  unfold tailWord_2573044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46923312245154251887315093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62564416326872335849753457 46923312245154251887315093)
  ·
    refine ⟨2199530261491605557217895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46923312245154251887315093 2199530261491605557217895)
    ·
      refine ⟨3299295392237408335826843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199530261491605557217895 3299295392237408335826843)
      ·
        refine ⟨4948943088356112503740265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299295392237408335826843 4948943088356112503740265)
        ·
          refine ⟨3711707316267084377805199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948943088356112503740265 3711707316267084377805199)
          ·
            refine ⟨5567560974400626566707799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711707316267084377805199 5567560974400626566707799)
            ·
              refine ⟨8351341461600939850061699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567560974400626566707799 8351341461600939850061699)
              ·
                refine ⟨12527012192401409775092549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8351341461600939850061699 12527012192401409775092549)
                ·
                  refine ⟨2348814786075264332829853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12527012192401409775092549 2348814786075264332829853)
                  ·
                    refine ⟨880805544778224124811195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348814786075264332829853 880805544778224124811195)
                    ·
                      rfl

theorem cell22_2573044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2573044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573044 prefixEnd_2573044 := by exact prefixLift 2573044
  have htrace : WordTrace (prefixWord ++ tailWord_2573044) baseStart_2573044 baseEnd_2573044 := by
    simpa [prefixWord, tailWord_2573044, baseEnd_2573044] using wordTrace_append hprefix tailTrace_2573044
  have hstable : (prefixWord ++ tailWord_2573044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573044).length < 2 ^ (prefixWord ++ tailWord_2573044).sum := by decide
  have hdescent : baseEnd_2573044 < baseStart_2573044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573074 : List Nat := [3, 2, 4, 1, 3, 1, 2, 6]
def baseStart_2573074 : Nat := 118140960795 + 2573074 * 2 ^ 59
def prefixEnd_2573074 : Nat := 4983230072969 + 3 ^ 40 * 2573074 * 2
def baseEnd_2573074 : Nat := 97868423821257116284567

theorem tailTrace_2573074 : CollatzResearch.WordTrace tailWord_2573074 prefixEnd_2573074 97868423821257116284567 := by
  unfold tailWord_2573074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461929670049954724555569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62565145786799879265481517 23461929670049954724555569)
  ·
    refine ⟨17596447252537466043416677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23461929670049954724555569 17596447252537466043416677)
    ·
      refine ⟨3299333859850774883140627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17596447252537466043416677 3299333859850774883140627)
      ·
        refine ⟨4949000789776162324710941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299333859850774883140627 4949000789776162324710941)
        ·
          refine ⟨1855875296166060871766603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4949000789776162324710941 1855875296166060871766603)
          ·
            refine ⟨2783812944249091307649905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855875296166060871766603 2783812944249091307649905)
            ·
              refine ⟨2087859708186818480737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2783812944249091307649905 2087859708186818480737429)
              ·
                refine ⟨97868423821257116284567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2087859708186818480737429 97868423821257116284567)
                ·
                  rfl

theorem cell22_2573074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_2573074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573074 prefixEnd_2573074 := by exact prefixLift 2573074
  have htrace : WordTrace (prefixWord ++ tailWord_2573074) baseStart_2573074 baseEnd_2573074 := by
    simpa [prefixWord, tailWord_2573074, baseEnd_2573074] using wordTrace_append hprefix tailTrace_2573074
  have hstable : (prefixWord ++ tailWord_2573074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573074).length < 2 ^ (prefixWord ++ tailWord_2573074).sum := by decide
  have hdescent : baseEnd_2573074 < baseStart_2573074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573128 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_2573128 : Nat := 118140960795 + 2573128 * 2 ^ 59
def prefixEnd_2573128 : Nat := 4983230072969 + 3 ^ 40 * 2573128 * 2
def baseEnd_2573128 : Nat := 880834299694875905710937

theorem tailTrace_2573128 : CollatzResearch.WordTrace tailWord_2573128 prefixEnd_2573128 880834299694875905710937 := by
  unfold tailWord_2573128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46924844111002093060344019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62566458814669457413792025 46924844111002093060344019)
  ·
    refine ⟨70387266166503139590516029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46924844111002093060344019 70387266166503139590516029)
    ·
      refine ⟨26395224812438677346443511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70387266166503139590516029 26395224812438677346443511)
      ·
        refine ⟨39592837218658016019665267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26395224812438677346443511 39592837218658016019665267)
        ·
          refine ⟨59389255827987024029497901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39592837218658016019665267 59389255827987024029497901)
          ·
            refine ⟨22270970935495134011061713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59389255827987024029497901 22270970935495134011061713)
            ·
              refine ⟨16703228201621350508296285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22270970935495134011061713 16703228201621350508296285)
              ·
                refine ⟨6263710575608006440611107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16703228201621350508296285 6263710575608006440611107)
                ·
                  refine ⟨9395565863412009660916661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6263710575608006440611107 9395565863412009660916661)
                  ·
                    refine ⟨880834299694875905710937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9395565863412009660916661 880834299694875905710937)
                    ·
                      rfl

theorem cell22_2573128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_2573128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573128 prefixEnd_2573128 := by exact prefixLift 2573128
  have htrace : WordTrace (prefixWord ++ tailWord_2573128) baseStart_2573128 baseEnd_2573128 := by
    simpa [prefixWord, tailWord_2573128, baseEnd_2573128] using wordTrace_append hprefix tailTrace_2573128
  have hstable : (prefixWord ++ tailWord_2573128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573128).length < 2 ^ (prefixWord ++ tailWord_2573128).sum := by decide
  have hdescent : baseEnd_2573128 < baseStart_2573128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573132 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_2573132 : Nat := 118140960795 + 2573132 * 2 ^ 59
def prefixEnd_2573132 : Nat := 4983230072969 + 3 ^ 40 * 2573132 * 2
def baseEnd_2573132 : Nat := 880835668976621228610925

theorem tailTrace_2573132 : CollatzResearch.WordTrace tailWord_2573132 prefixEnd_2573132 880835668976621228610925 := by
  unfold tailWord_2573132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46924917056994847401916825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62566556075993129869222433 46924917056994847401916825)
  ·
    refine ⟨35193687792746135551437619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46924917056994847401916825 35193687792746135551437619)
    ·
      refine ⟨52790531689119203327156429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35193687792746135551437619 52790531689119203327156429)
      ·
        refine ⟨19796449383419701247683661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52790531689119203327156429 19796449383419701247683661)
        ·
          refine ⟨7423668518782387967881373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19796449383419701247683661 7423668518782387967881373)
          ·
            refine ⟨2783875694543395487955515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7423668518782387967881373 2783875694543395487955515)
            ·
              refine ⟨4175813541815093231933273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783875694543395487955515 4175813541815093231933273)
              ·
                refine ⟨3131860156361319923949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4175813541815093231933273 3131860156361319923949955)
                ·
                  refine ⟨4697790234541979885924933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131860156361319923949955 4697790234541979885924933)
                  ·
                    refine ⟨880835668976621228610925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4697790234541979885924933 880835668976621228610925)
                    ·
                      rfl

theorem cell22_2573132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_2573132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573132 prefixEnd_2573132 := by exact prefixLift 2573132
  have htrace : WordTrace (prefixWord ++ tailWord_2573132) baseStart_2573132 baseEnd_2573132 := by
    simpa [prefixWord, tailWord_2573132, baseEnd_2573132] using wordTrace_append hprefix tailTrace_2573132
  have hstable : (prefixWord ++ tailWord_2573132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573132).length < 2 ^ (prefixWord ++ tailWord_2573132).sum := by decide
  have hdescent : baseEnd_2573132 < baseStart_2573132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573160 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2573160 : Nat := 118140960795 + 2573160 * 2 ^ 59
def prefixEnd_2573160 : Nat := 4983230072969 + 3 ^ 40 * 2573160 * 2
def baseEnd_2573160 : Nat := 880845253948838488910839

theorem tailTrace_2573160 : CollatzResearch.WordTrace tailWord_2573160 prefixEnd_2573160 880845253948838488910839 := by
  unfold tailWord_2573160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46925427678944127792926467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62567236905258837057235289 46925427678944127792926467)
  ·
    refine ⟨70388141518416191689389701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46925427678944127792926467 70388141518416191689389701)
    ·
      refine ⟨13197776534703035941760569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70388141518416191689389701 13197776534703035941760569)
      ·
        refine ⟨9898332401027276956320427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13197776534703035941760569 9898332401027276956320427)
        ·
          refine ⟨14847498601540915434480641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9898332401027276956320427 14847498601540915434480641)
          ·
            refine ⟨11135623951155686575860481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14847498601540915434480641 11135623951155686575860481)
            ·
              refine ⟨8351717963366764931895361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11135623951155686575860481 8351717963366764931895361)
              ·
                refine ⟨6263788472525073698921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8351717963366764931895361 6263788472525073698921521)
                ·
                  refine ⟨4697841354393805274191141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6263788472525073698921521 4697841354393805274191141)
                  ·
                    refine ⟨880845253948838488910839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4697841354393805274191141 880845253948838488910839)
                    ·
                      rfl

theorem cell22_2573160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2573160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573160 prefixEnd_2573160 := by exact prefixLift 2573160
  have htrace : WordTrace (prefixWord ++ tailWord_2573160) baseStart_2573160 baseEnd_2573160 := by
    simpa [prefixWord, tailWord_2573160, baseEnd_2573160] using wordTrace_append hprefix tailTrace_2573160
  have hstable : (prefixWord ++ tailWord_2573160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573160).length < 2 ^ (prefixWord ++ tailWord_2573160).sum := by decide
  have hdescent : baseEnd_2573160 < baseStart_2573160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573188 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2573188 : Nat := 118140960795 + 2573188 * 2 ^ 59
def prefixEnd_2573188 : Nat := 4983230072969 + 3 ^ 40 * 2573188 * 2
def baseEnd_2573188 : Nat := 880854838921055749210753

theorem tailTrace_2573188 : CollatzResearch.WordTrace tailWord_2573188 prefixEnd_2573188 880854838921055749210753 := by
  unfold tailWord_2573188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46925938300893408183936109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62567917734524544245248145 46925938300893408183936109)
  ·
    refine ⟨17597226862835028068976041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46925938300893408183936109 17597226862835028068976041)
    ·
      refine ⟨13197920147126271051732031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17597226862835028068976041 13197920147126271051732031)
      ·
        refine ⟨19796880220689406577598047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13197920147126271051732031 19796880220689406577598047)
        ·
          refine ⟨29695320331034109866397071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19796880220689406577598047 29695320331034109866397071)
          ·
            refine ⟨44542980496551164799595607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29695320331034109866397071 44542980496551164799595607)
            ·
              refine ⟨66814470744826747199393411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44542980496551164799595607 66814470744826747199393411)
              ·
                refine ⟨100221706117240120799090117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66814470744826747199393411 100221706117240120799090117)
                ·
                  refine ⟨18791569896982522649829397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100221706117240120799090117 18791569896982522649829397)
                  ·
                    refine ⟨880854838921055749210753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18791569896982522649829397 880854838921055749210753)
                    ·
                      rfl

theorem cell22_2573188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2573188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573188 prefixEnd_2573188 := by exact prefixLift 2573188
  have htrace : WordTrace (prefixWord ++ tailWord_2573188) baseStart_2573188 baseEnd_2573188 := by
    simpa [prefixWord, tailWord_2573188, baseEnd_2573188] using wordTrace_append hprefix tailTrace_2573188
  have hstable : (prefixWord ++ tailWord_2573188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573188).length < 2 ^ (prefixWord ++ tailWord_2573188).sum := by decide
  have hdescent : baseEnd_2573188 < baseStart_2573188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573237 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 5]
def baseStart_2573237 : Nat := 118140960795 + 2573237 * 2 ^ 59
def prefixEnd_2573237 : Nat := 4983230072969 + 3 ^ 40 * 2573237 * 2
def baseEnd_2573237 : Nat := 293623870874145318245201

theorem tailTrace_2573237 : CollatzResearch.WordTrace tailWord_2573237 prefixEnd_2573237 293623870874145318245201 := by
  unfold tailWord_2573237
  simp only [CollatzResearch.WordTrace]
  refine ⟨93853663778609297736405965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62569109185739531824270643 93853663778609297736405965)
  ·
    refine ⟨35195123916978486651152237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93853663778609297736405965 35195123916978486651152237)
    ·
      refine ⟨13198171468866932494182089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35195123916978486651152237 13198171468866932494182089)
      ·
        refine ⟨9898628601650199370636567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13198171468866932494182089 9898628601650199370636567)
        ·
          refine ⟨14847942902475299055954851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9898628601650199370636567 14847942902475299055954851)
          ·
            refine ⟨22271914353712948583932277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14847942902475299055954851 22271914353712948583932277)
            ·
              refine ⟨2087991970660588929743651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22271914353712948583932277 2087991970660588929743651)
              ·
                refine ⟨3131987955990883394615477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087991970660588929743651 3131987955990883394615477)
                ·
                  refine ⟨293623870874145318245201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3131987955990883394615477 293623870874145318245201)
                  ·
                    rfl

theorem cell22_2573237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_2573237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573237 prefixEnd_2573237 := by exact prefixLift 2573237
  have htrace : WordTrace (prefixWord ++ tailWord_2573237) baseStart_2573237 baseEnd_2573237 := by
    simpa [prefixWord, tailWord_2573237, baseEnd_2573237] using wordTrace_append hprefix tailTrace_2573237
  have hstable : (prefixWord ++ tailWord_2573237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573237).length < 2 ^ (prefixWord ++ tailWord_2573237).sum := by decide
  have hdescent : baseEnd_2573237 < baseStart_2573237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573344 : List Nat := [2, 1, 1, 7, 1, 2, 1, 7]
def baseStart_2573344 : Nat := 118140960795 + 2573344 * 2 ^ 59
def prefixEnd_2573344 : Nat := 4983230072969 + 3 ^ 40 * 2573344 * 2
def baseEnd_2573344 : Nat := 97878693434347038034475

theorem tailTrace_2573344 : CollatzResearch.WordTrace tailWord_2573344 prefixEnd_2573344 97878693434347038034475 := by
  unfold tailWord_2573344
  simp only [CollatzResearch.WordTrace]
  refine ⟨46928783194610827505275543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62571710926147770007034057 46928783194610827505275543)
  ·
    refine ⟨70393174791916241257913315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46928783194610827505275543 70393174791916241257913315)
    ·
      refine ⟨105589762187874361886869973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70393174791916241257913315 105589762187874361886869973)
      ·
        refine ⟨2474760051278305356723515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 105589762187874361886869973 2474760051278305356723515)
        ·
          refine ⟨3712140076917458035085273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474760051278305356723515 3712140076917458035085273)
          ·
            refine ⟨2784105057688093526313955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712140076917458035085273 2784105057688093526313955)
            ·
              refine ⟨4176157586532140289470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784105057688093526313955 4176157586532140289470933)
              ·
                refine ⟨97878693434347038034475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4176157586532140289470933 97878693434347038034475)
                ·
                  rfl

theorem cell22_2573344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_2573344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573344 prefixEnd_2573344 := by exact prefixLift 2573344
  have htrace : WordTrace (prefixWord ++ tailWord_2573344) baseStart_2573344 baseEnd_2573344 := by
    simpa [prefixWord, tailWord_2573344, baseEnd_2573344] using wordTrace_append hprefix tailTrace_2573344
  have hstable : (prefixWord ++ tailWord_2573344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573344).length < 2 ^ (prefixWord ++ tailWord_2573344).sum := by decide
  have hdescent : baseEnd_2573344 < baseStart_2573344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573355 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 5]
def baseStart_2573355 : Nat := 118140960795 + 2573355 * 2 ^ 59
def prefixEnd_2573355 : Nat := 4983230072969 + 3 ^ 40 * 2573355 * 2
def baseEnd_2573355 : Nat := 293637335477974326761747

theorem tailTrace_2573355 : CollatzResearch.WordTrace tailWord_2573355 prefixEnd_2573355 293637335477974326761747 := by
  unfold tailWord_2573355
  simp only [CollatzResearch.WordTrace]
  refine ⟨93857967592181803889201519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62571978394787869259467679 93857967592181803889201519)
  ·
    refine ⟨140786951388272705833802279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93857967592181803889201519 140786951388272705833802279)
    ·
      refine ⟨211180427082409058750703419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140786951388272705833802279 211180427082409058750703419)
      ·
        refine ⟨316770640623613588126055129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211180427082409058750703419 316770640623613588126055129)
        ·
          refine ⟨237577980467710191094541347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316770640623613588126055129 237577980467710191094541347)
          ·
            refine ⟨356366970701565286641812021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237577980467710191094541347 356366970701565286641812021)
            ·
              refine ⟨33409403503271745622669877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 356366970701565286641812021 33409403503271745622669877)
              ·
                refine ⟨3132131578431726152125301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33409403503271745622669877 3132131578431726152125301)
                ·
                  refine ⟨293637335477974326761747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132131578431726152125301 293637335477974326761747)
                  ·
                    rfl

theorem cell22_2573355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 5].length) (baseStart_2573355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573355 prefixEnd_2573355 := by exact prefixLift 2573355
  have htrace : WordTrace (prefixWord ++ tailWord_2573355) baseStart_2573355 baseEnd_2573355 := by
    simpa [prefixWord, tailWord_2573355, baseEnd_2573355] using wordTrace_append hprefix tailTrace_2573355
  have hstable : (prefixWord ++ tailWord_2573355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573355).length < 2 ^ (prefixWord ++ tailWord_2573355).sum := by decide
  have hdescent : baseEnd_2573355 < baseStart_2573355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573385 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_2573385 : Nat := 118140960795 + 2573385 * 2 ^ 59
def prefixEnd_2573385 : Nat := 4983230072969 + 3 ^ 40 * 2573385 * 2
def baseEnd_2573385 : Nat := 880922276047012902035149

theorem tailTrace_2573385 : CollatzResearch.WordTrace tailWord_2573385 prefixEnd_2573385 880922276047012902035149 := by
  unfold tailWord_2573385
  simp only [CollatzResearch.WordTrace]
  refine ⟨93859061782073119012793609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62572707854715412675195739 93859061782073119012793609)
  ·
    refine ⟨70394296336554839259595207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93859061782073119012793609 70394296336554839259595207)
    ·
      refine ⟨105591444504832258889392811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70394296336554839259595207 105591444504832258889392811)
      ·
        refine ⟨158387166757248388334089217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105591444504832258889392811 158387166757248388334089217)
        ·
          refine ⟨118790375067936291250566913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158387166757248388334089217 118790375067936291250566913)
          ·
            refine ⟨89092781300952218437925185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118790375067936291250566913 89092781300952218437925185)
            ·
              refine ⟨66819585975714163828443889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89092781300952218437925185 66819585975714163828443889)
              ·
                refine ⟨50114689481785622871332917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66819585975714163828443889 50114689481785622871332917)
                ·
                  refine ⟨4698252138917402144187461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50114689481785622871332917 4698252138917402144187461)
                  ·
                    refine ⟨880922276047012902035149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698252138917402144187461 880922276047012902035149)
                    ·
                      rfl

theorem cell22_2573385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_2573385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573385 prefixEnd_2573385 := by exact prefixLift 2573385
  have htrace : WordTrace (prefixWord ++ tailWord_2573385) baseStart_2573385 baseEnd_2573385 := by
    simpa [prefixWord, tailWord_2573385, baseEnd_2573385] using wordTrace_append hprefix tailTrace_2573385
  have hstable : (prefixWord ++ tailWord_2573385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573385).length < 2 ^ (prefixWord ++ tailWord_2573385).sum := by decide
  have hdescent : baseEnd_2573385 < baseStart_2573385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573389 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2573389 : Nat := 118140960795 + 2573389 * 2 ^ 59
def prefixEnd_2573389 : Nat := 4983230072969 + 3 ^ 40 * 2573389 * 2
def baseEnd_2573389 : Nat := 293641215109586074978379

theorem tailTrace_2573389 : CollatzResearch.WordTrace tailWord_2573389 prefixEnd_2573389 293641215109586074978379 := by
  unfold tailWord_2573389
  simp only [CollatzResearch.WordTrace]
  refine ⟨93859207674058627695939221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62572805116039085130626147 93859207674058627695939221)
  ·
    refine ⟨4399650359721498173247151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93859207674058627695939221 4399650359721498173247151)
    ·
      refine ⟨6599475539582247259870727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399650359721498173247151 6599475539582247259870727)
      ·
        refine ⟨9899213309373370889806091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599475539582247259870727 9899213309373370889806091)
        ·
          refine ⟨14848819964060056334709137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899213309373370889806091 14848819964060056334709137)
          ·
            refine ⟨11136614973045042251031853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14848819964060056334709137 11136614973045042251031853)
            ·
              refine ⟨4176230614891890844136945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11136614973045042251031853 4176230614891890844136945)
              ·
                refine ⟨3132172961168918133102709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4176230614891890844136945 3132172961168918133102709)
                ·
                  refine ⟨293641215109586074978379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132172961168918133102709 293641215109586074978379)
                  ·
                    rfl

theorem cell22_2573389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2573389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573389 prefixEnd_2573389 := by exact prefixLift 2573389
  have htrace : WordTrace (prefixWord ++ tailWord_2573389) baseStart_2573389 baseEnd_2573389 := by
    simpa [prefixWord, tailWord_2573389, baseEnd_2573389] using wordTrace_append hprefix tailTrace_2573389
  have hstable : (prefixWord ++ tailWord_2573389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573389).length < 2 ^ (prefixWord ++ tailWord_2573389).sum := by decide
  have hdescent : baseEnd_2573389 < baseStart_2573389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573432 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_2573432 : Nat := 118140960795 + 2573432 * 2 ^ 59
def prefixEnd_2573432 : Nat := 4983230072969 + 3 ^ 40 * 2573432 * 2
def baseEnd_2573432 : Nat := 880938365107520446110005

theorem tailTrace_2573432 : CollatzResearch.WordTrace tailWord_2573432 prefixEnd_2573432 880938365107520446110005 := by
  unfold tailWord_2573432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46930388006451423019877275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62573850675268564026503033 46930388006451423019877275)
  ·
    refine ⟨70395582009677134529815913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46930388006451423019877275 70395582009677134529815913)
    ·
      refine ⟨52796686507257850897361935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70395582009677134529815913 52796686507257850897361935)
      ·
        refine ⟨79195029760886776346042903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52796686507257850897361935 79195029760886776346042903)
        ·
          refine ⟨118792544641330164519064355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79195029760886776346042903 118792544641330164519064355)
          ·
            refine ⟨178188816961995246778596533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118792544641330164519064355 178188816961995246778596533)
            ·
              refine ⟨16705201590187054385493425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178188816961995246778596533 16705201590187054385493425)
              ·
                refine ⟨12528901192640290789120069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16705201590187054385493425 12528901192640290789120069)
                ·
                  refine ⟨2349168973620054522960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12528901192640290789120069 2349168973620054522960013)
                  ·
                    refine ⟨880938365107520446110005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2349168973620054522960013 880938365107520446110005)
                    ·
                      rfl

theorem cell22_2573432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_2573432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573432 prefixEnd_2573432 := by exact prefixLift 2573432
  have htrace : WordTrace (prefixWord ++ tailWord_2573432) baseStart_2573432 baseEnd_2573432 := by
    simpa [prefixWord, tailWord_2573432, baseEnd_2573432] using wordTrace_append hprefix tailTrace_2573432
  have hstable : (prefixWord ++ tailWord_2573432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573432).length < 2 ^ (prefixWord ++ tailWord_2573432).sum := by decide
  have hdescent : baseEnd_2573432 < baseStart_2573432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573466 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_2573466 : Nat := 118140960795 + 2573466 * 2 ^ 59
def prefixEnd_2573466 : Nat := 4983230072969 + 3 ^ 40 * 2573466 * 2
def baseEnd_2573466 : Nat := 880950004002355690759901

theorem tailTrace_2573466 : CollatzResearch.WordTrace tailWord_2573466 prefixEnd_2573466 880950004002355690759901 := by
  unfold tailWord_2573466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23465504023694917461623063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62574677396519779897661501 23465504023694917461623063)
  ·
    refine ⟨35198256035542376192434595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23465504023694917461623063 35198256035542376192434595)
    ·
      refine ⟨52797384053313564288651893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35198256035542376192434595 52797384053313564288651893)
      ·
        refine ⟨4949754754998146652061115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52797384053313564288651893 4949754754998146652061115)
        ·
          refine ⟨7424632132497219978091673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949754754998146652061115 7424632132497219978091673)
          ·
            refine ⟨5568474099372914983568755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7424632132497219978091673 5568474099372914983568755)
            ·
              refine ⟨8352711149059372475353133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568474099372914983568755 8352711149059372475353133)
              ·
                refine ⟨3132266680897264678257425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8352711149059372475353133 3132266680897264678257425)
                ·
                  refine ⟨2349200010672948508693069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132266680897264678257425 2349200010672948508693069)
                  ·
                    refine ⟨880950004002355690759901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2349200010672948508693069 880950004002355690759901)
                    ·
                      rfl

theorem cell22_2573466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_2573466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573466 prefixEnd_2573466 := by exact prefixLift 2573466
  have htrace : WordTrace (prefixWord ++ tailWord_2573466) baseStart_2573466 baseEnd_2573466 := by
    simpa [prefixWord, tailWord_2573466, baseEnd_2573466] using wordTrace_append hprefix tailTrace_2573466
  have hstable : (prefixWord ++ tailWord_2573466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573466).length < 2 ^ (prefixWord ++ tailWord_2573466).sum := by decide
  have hdescent : baseEnd_2573466 < baseStart_2573466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573569 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 6]
def baseStart_2573569 : Nat := 118140960795 + 2573569 * 2 ^ 59
def prefixEnd_2573569 : Nat := 4983230072969 + 3 ^ 40 * 2573569 * 2
def baseEnd_2573569 : Nat := 293661754335765918478195

theorem tailTrace_2573569 : CollatzResearch.WordTrace tailWord_2573569 prefixEnd_2573569 293661754335765918478195 := by
  unfold tailWord_2573569
  simp only [CollatzResearch.WordTrace]
  refine ⟨93865772813406518437491761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62577181875604345624994507 93865772813406518437491761)
  ·
    refine ⟨70399329610054888828118821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93865772813406518437491761 70399329610054888828118821)
    ·
      refine ⟨13199874301885291655272279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70399329610054888828118821 13199874301885291655272279)
      ·
        refine ⟨19799811452827937482908419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13199874301885291655272279 19799811452827937482908419)
        ·
          refine ⟨29699717179241906224362629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19799811452827937482908419 29699717179241906224362629)
          ·
            refine ⟨5568696971107857417067993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29699717179241906224362629 5568696971107857417067993)
            ·
              refine ⟨4176522728330893062800995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568696971107857417067993 4176522728330893062800995)
              ·
                refine ⟨6264784092496339594201493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176522728330893062800995 6264784092496339594201493)
                ·
                  refine ⟨293661754335765918478195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6264784092496339594201493 293661754335765918478195)
                  ·
                    rfl

theorem cell22_2573569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_2573569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573569 prefixEnd_2573569 := by exact prefixLift 2573569
  have htrace : WordTrace (prefixWord ++ tailWord_2573569) baseStart_2573569 baseEnd_2573569 := by
    simpa [prefixWord, tailWord_2573569, baseEnd_2573569] using wordTrace_append hprefix tailTrace_2573569
  have hstable : (prefixWord ++ tailWord_2573569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573569).length < 2 ^ (prefixWord ++ tailWord_2573569).sum := by decide
  have hdescent : baseEnd_2573569 < baseStart_2573569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573676 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_2573676 : Nat := 118140960795 + 2573676 * 2 ^ 59
def prefixEnd_2573676 : Nat := 4983230072969 + 3 ^ 40 * 2573676 * 2
def baseEnd_2573676 : Nat := 293673963764661714336419

theorem tailTrace_2573676 : CollatzResearch.WordTrace tailWord_2573676 prefixEnd_2573676 293673963764661714336419 := by
  unfold tailWord_2573676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46934837712009437855818441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62579783616012583807757921 46934837712009437855818441)
  ·
    refine ⟨35201128284007078391863831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46934837712009437855818441 35201128284007078391863831)
    ·
      refine ⟨52801692426010617587795747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35201128284007078391863831 52801692426010617587795747)
      ·
        refine ⟨79202538639015926381693621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52801692426010617587795747 79202538639015926381693621)
        ·
          refine ⟨7425237997407743098283777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79202538639015926381693621 7425237997407743098283777)
          ·
            refine ⟨5568928498055807323712833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425237997407743098283777 5568928498055807323712833)
            ·
              refine ⟨4176696373541855492784625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568928498055807323712833 4176696373541855492784625)
              ·
                refine ⟨3132522280156391619588469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4176696373541855492784625 3132522280156391619588469)
                ·
                  refine ⟨293673963764661714336419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132522280156391619588469 293673963764661714336419)
                  ·
                    rfl

theorem cell22_2573676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_2573676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573676 prefixEnd_2573676 := by exact prefixLift 2573676
  have htrace : WordTrace (prefixWord ++ tailWord_2573676) baseStart_2573676 baseEnd_2573676 := by
    simpa [prefixWord, tailWord_2573676, baseEnd_2573676] using wordTrace_append hprefix tailTrace_2573676
  have hstable : (prefixWord ++ tailWord_2573676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573676).length < 2 ^ (prefixWord ++ tailWord_2573676).sum := by decide
  have hdescent : baseEnd_2573676 < baseStart_2573676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573689 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_2573689 : Nat := 118140960795 + 2573689 * 2 ^ 59
def prefixEnd_2573689 : Nat := 4983230072969 + 3 ^ 40 * 2573689 * 2
def baseEnd_2573689 : Nat := 881026341459657442434217

theorem tailTrace_2573689 : CollatzResearch.WordTrace tailWord_2573689 prefixEnd_2573689 881026341459657442434217 := by
  unfold tailWord_2573689
  simp only [CollatzResearch.WordTrace]
  refine ⟨93870149572971778931860121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62580099715314519287906747 93870149572971778931860121)
  ·
    refine ⟨70402612179728834198895091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93870149572971778931860121 70402612179728834198895091)
    ·
      refine ⟨105603918269593251298342637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70402612179728834198895091 105603918269593251298342637)
      ·
        refine ⟨39601469351097469236878489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105603918269593251298342637 39601469351097469236878489)
        ·
          refine ⟨29701102013323101927658867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39601469351097469236878489 29701102013323101927658867)
          ·
            refine ⟨44551653019984652891488301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29701102013323101927658867 44551653019984652891488301)
            ·
              refine ⟨16706869882494244834308113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44551653019984652891488301 16706869882494244834308113)
              ·
                refine ⟨12530152411870683625731085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16706869882494244834308113 12530152411870683625731085)
                ·
                  refine ⟨4698807154451506359649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12530152411870683625731085 4698807154451506359649157)
                  ·
                    refine ⟨881026341459657442434217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4698807154451506359649157 881026341459657442434217)
                    ·
                      rfl

theorem cell22_2573689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_2573689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573689 prefixEnd_2573689 := by exact prefixLift 2573689
  have htrace : WordTrace (prefixWord ++ tailWord_2573689) baseStart_2573689 baseEnd_2573689 := by
    simpa [prefixWord, tailWord_2573689, baseEnd_2573689] using wordTrace_append hprefix tailTrace_2573689
  have hstable : (prefixWord ++ tailWord_2573689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573689).length < 2 ^ (prefixWord ++ tailWord_2573689).sum := by decide
  have hdescent : baseEnd_2573689 < baseStart_2573689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573704 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_2573704 : Nat := 118140960795 + 2573704 * 2 ^ 59
def prefixEnd_2573704 : Nat := 4983230072969 + 3 ^ 40 * 2573704 * 2
def baseEnd_2573704 : Nat := 293677158755400801103057

theorem tailTrace_2573704 : CollatzResearch.WordTrace tailWord_2573704 prefixEnd_2573704 293677158755400801103057 := by
  unfold tailWord_2573704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46935348333958718246828083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62580464445278290995770777 46935348333958718246828083)
  ·
    refine ⟨70403022500938077370242125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46935348333958718246828083 70403022500938077370242125)
    ·
      refine ⟨26401133437851779013840797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70403022500938077370242125 26401133437851779013840797)
      ·
        refine ⟨9900425039194417130190299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26401133437851779013840797 9900425039194417130190299)
        ·
          refine ⟨14850637558791625695285449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9900425039194417130190299 14850637558791625695285449)
          ·
            refine ⟨11137978169093719271464087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14850637558791625695285449 11137978169093719271464087)
            ·
              refine ⟨16706967253640578907196131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11137978169093719271464087 16706967253640578907196131)
              ·
                refine ⟨25060450880460868360794197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16706967253640578907196131 25060450880460868360794197)
                ·
                  refine ⟨293677158755400801103057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25060450880460868360794197 293677158755400801103057)
                  ·
                    rfl

theorem cell22_2573704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_2573704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573704 prefixEnd_2573704 := by exact prefixLift 2573704
  have htrace : WordTrace (prefixWord ++ tailWord_2573704) baseStart_2573704 baseEnd_2573704 := by
    simpa [prefixWord, tailWord_2573704, baseEnd_2573704] using wordTrace_append hprefix tailTrace_2573704
  have hstable : (prefixWord ++ tailWord_2573704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573704).length < 2 ^ (prefixWord ++ tailWord_2573704).sum := by decide
  have hdescent : baseEnd_2573704 < baseStart_2573704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573721 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 4]
def baseStart_2573721 : Nat := 118140960795 + 2573721 * 2 ^ 59
def prefixEnd_2573721 : Nat := 4983230072969 + 3 ^ 40 * 2573721 * 2
def baseEnd_2573721 : Nat := 293679098571206675211373

theorem tailTrace_2573721 : CollatzResearch.WordTrace tailWord_2573721 prefixEnd_2573721 293679098571206675211373 := by
  unfold tailWord_2573721
  simp only [CollatzResearch.WordTrace]
  refine ⟨93871316708855848397025017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62580877805903898931350011 93871316708855848397025017)
  ·
    refine ⟨70403487531641886297768763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93871316708855848397025017 70403487531641886297768763)
    ·
      refine ⟨105605231297462829446653145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70403487531641886297768763 105605231297462829446653145)
      ·
        refine ⟨79203923473097122084989859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105605231297462829446653145 79203923473097122084989859)
        ·
          refine ⟨118805885209645683127484789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79203923473097122084989859 118805885209645683127484789)
          ·
            refine ⟨11138051738404282793201699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118805885209645683127484789 11138051738404282793201699)
            ·
              refine ⟨16707077607606424189802549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138051738404282793201699 16707077607606424189802549)
              ·
                refine ⟨1566288525713102267793989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16707077607606424189802549 1566288525713102267793989)
                ·
                  refine ⟨293679098571206675211373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1566288525713102267793989 293679098571206675211373)
                  ·
                    rfl

theorem cell22_2573721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_2573721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573721 prefixEnd_2573721 := by exact prefixLift 2573721
  have htrace : WordTrace (prefixWord ++ tailWord_2573721) baseStart_2573721 baseEnd_2573721 := by
    simpa [prefixWord, tailWord_2573721, baseEnd_2573721] using wordTrace_append hprefix tailTrace_2573721
  have hstable : (prefixWord ++ tailWord_2573721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573721).length < 2 ^ (prefixWord ++ tailWord_2573721).sum := by decide
  have hdescent : baseEnd_2573721 < baseStart_2573721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573753 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_2573753 : Nat := 118140960795 + 2573753 * 2 ^ 59
def prefixEnd_2573753 : Nat := 4983230072969 + 3 ^ 40 * 2573753 * 2
def baseEnd_2573753 : Nat := 881048249967582608834021

theorem tailTrace_2573753 : CollatzResearch.WordTrace tailWord_2573753 prefixEnd_2573753 881048249967582608834021 := by
  unfold tailWord_2573753
  simp only [CollatzResearch.WordTrace]
  refine ⟨93872483844739917862189913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62581655896493278574793275 93872483844739917862189913)
  ·
    refine ⟨70404362883554938396642435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93872483844739917862189913 70404362883554938396642435)
    ·
      refine ⟨105606544325332407594963653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70404362883554938396642435 105606544325332407594963653)
      ·
        refine ⟨19801227060999826424055685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105606544325332407594963653 19801227060999826424055685)
        ·
          refine ⟨3712730073937467454510441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19801227060999826424055685 3712730073937467454510441)
          ·
            refine ⟨2784547555453100590882831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712730073937467454510441 2784547555453100590882831)
            ·
              refine ⟨4176821333179650886324247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784547555453100590882831 4176821333179650886324247)
              ·
                refine ⟨6265231999769476329486371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176821333179650886324247 6265231999769476329486371)
                ·
                  refine ⟨9397847999654214494229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265231999769476329486371 9397847999654214494229557)
                  ·
                    refine ⟨881048249967582608834021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9397847999654214494229557 881048249967582608834021)
                    ·
                      rfl

theorem cell22_2573753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_2573753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573753 prefixEnd_2573753 := by exact prefixLift 2573753
  have htrace : WordTrace (prefixWord ++ tailWord_2573753) baseStart_2573753 baseEnd_2573753 := by
    simpa [prefixWord, tailWord_2573753, baseEnd_2573753] using wordTrace_append hprefix tailTrace_2573753
  have hstable : (prefixWord ++ tailWord_2573753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573753).length < 2 ^ (prefixWord ++ tailWord_2573753).sum := by decide
  have hdescent : baseEnd_2573753 < baseStart_2573753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573961 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_2573961 : Nat := 118140960795 + 2573961 * 2 ^ 59
def prefixEnd_2573961 : Nat := 4983230072969 + 3 ^ 40 * 2573961 * 2
def baseEnd_2573961 : Nat := 881119452618339399633383

theorem tailTrace_2573961 : CollatzResearch.WordTrace tailWord_2573961 prefixEnd_2573961 881119452618339399633383 := by
  unfold tailWord_2573961
  simp only [CollatzResearch.WordTrace]
  refine ⟨93880070227986369385761737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62586713485324246257174491 93880070227986369385761737)
  ·
    refine ⟨70410052670989777039321303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93880070227986369385761737 70410052670989777039321303)
    ·
      refine ⟨105615079006484665558981955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70410052670989777039321303 105615079006484665558981955)
      ·
        refine ⟨158422618509726998338472933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105615079006484665558981955 158422618509726998338472933)
        ·
          refine ⟨29704240970573812188463675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158422618509726998338472933 29704240970573812188463675)
          ·
            refine ⟨44556361455860718282695513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29704240970573812188463675 44556361455860718282695513)
            ·
              refine ⟨33417271091895538712021635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44556361455860718282695513 33417271091895538712021635)
              ·
                refine ⟨50125906637843308068032453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33417271091895538712021635 50125906637843308068032453)
                ·
                  refine ⟨9398607494595620262756085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50125906637843308068032453 9398607494595620262756085)
                  ·
                    refine ⟨881119452618339399633383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9398607494595620262756085 881119452618339399633383)
                    ·
                      rfl

theorem cell22_2573961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_2573961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573961 prefixEnd_2573961 := by exact prefixLift 2573961
  have htrace : WordTrace (prefixWord ++ tailWord_2573961) baseStart_2573961 baseEnd_2573961 := by
    simpa [prefixWord, tailWord_2573961, baseEnd_2573961] using wordTrace_append hprefix tailTrace_2573961
  have hstable : (prefixWord ++ tailWord_2573961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573961).length < 2 ^ (prefixWord ++ tailWord_2573961).sum := by decide
  have hdescent : baseEnd_2573961 < baseStart_2573961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2573980 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_2573980 : Nat := 118140960795 + 2573980 * 2 ^ 59
def prefixEnd_2573980 : Nat := 4983230072969 + 3 ^ 40 * 2573980 * 2
def baseEnd_2573980 : Nat := 293708652235543227802775

theorem tailTrace_2573980 : CollatzResearch.WordTrace tailWord_2573980 prefixEnd_2573980 293708652235543227802775 := by
  unfold tailWord_2573980
  simp only [CollatzResearch.WordTrace]
  refine ⟨46940381607458767815351697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62587175476611690420468929 46940381607458767815351697)
  ·
    refine ⟨35205286205594075861513773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46940381607458767815351697 35205286205594075861513773)
    ·
      refine ⟨13201982327097778448067665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35205286205594075861513773 13201982327097778448067665)
      ·
        refine ⟨9901486745323333836050749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13201982327097778448067665 9901486745323333836050749)
        ·
          refine ⟨3713057529496250188519031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9901486745323333836050749 3713057529496250188519031)
          ·
            refine ⟨5569586294244375282778547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713057529496250188519031 5569586294244375282778547)
            ·
              refine ⟨8354379441366562924167821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569586294244375282778547 8354379441366562924167821)
              ·
                refine ⟨3132892290512461096562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8354379441366562924167821 3132892290512461096562933)
                ·
                  refine ⟨293708652235543227802775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132892290512461096562933 293708652235543227802775)
                  ·
                    rfl

theorem cell22_2573980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_2573980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2573980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2573980 prefixEnd_2573980 := by exact prefixLift 2573980
  have htrace : WordTrace (prefixWord ++ tailWord_2573980) baseStart_2573980 baseEnd_2573980 := by
    simpa [prefixWord, tailWord_2573980, baseEnd_2573980] using wordTrace_append hprefix tailTrace_2573980
  have hstable : (prefixWord ++ tailWord_2573980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2573980).length < 2 ^ (prefixWord ++ tailWord_2573980).sum := by decide
  have hdescent : baseEnd_2573980 < baseStart_2573980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2573980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574018 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2574018 : Nat := 118140960795 + 2574018 * 2 ^ 59
def prefixEnd_2574018 : Nat := 4983230072969 + 3 ^ 40 * 2574018 * 2
def baseEnd_2574018 : Nat := 881138964883210250958209

theorem tailTrace_2574018 : CollatzResearch.WordTrace tailWord_2574018 prefixEnd_2574018 881138964883210250958209 := by
  unfold tailWord_2574018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23470537297194967030146677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62588099459186578747057805 23470537297194967030146677)
  ·
    refine ⟨2200362871612028159076251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23470537297194967030146677 2200362871612028159076251)
    ·
      refine ⟨3300544307418042238614377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200362871612028159076251 3300544307418042238614377)
      ·
        refine ⟨2475408230563531678960783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3300544307418042238614377 2475408230563531678960783)
        ·
          refine ⟨3713112345845297518441175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475408230563531678960783 3713112345845297518441175)
          ·
            refine ⟨5569668518767946277661763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713112345845297518441175 5569668518767946277661763)
            ·
              refine ⟨8354502778151919416492645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5569668518767946277661763 8354502778151919416492645)
              ·
                refine ⟨1566469270903484890592371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8354502778151919416492645 1566469270903484890592371)
                ·
                  refine ⟨2349703906355227335888557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566469270903484890592371 2349703906355227335888557)
                  ·
                    refine ⟨881138964883210250958209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2349703906355227335888557 881138964883210250958209)
                    ·
                      rfl

theorem cell22_2574018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2574018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574018 prefixEnd_2574018 := by exact prefixLift 2574018
  have htrace : WordTrace (prefixWord ++ tailWord_2574018) baseStart_2574018 baseEnd_2574018 := by
    simpa [prefixWord, tailWord_2574018, baseEnd_2574018] using wordTrace_append hprefix tailTrace_2574018
  have hstable : (prefixWord ++ tailWord_2574018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574018).length < 2 ^ (prefixWord ++ tailWord_2574018).sum := by decide
  have hdescent : baseEnd_2574018 < baseStart_2574018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574040 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_2574040 : Nat := 118140960795 + 2574040 * 2 ^ 59
def prefixEnd_2574040 : Nat := 4983230072969 + 3 ^ 40 * 2574040 * 2
def baseEnd_2574040 : Nat := 881146495932809526908141

theorem tailTrace_2574040 : CollatzResearch.WordTrace tailWord_2574040 prefixEnd_2574040 881146495932809526908141 := by
  unfold tailWord_2574040
  simp only [CollatzResearch.WordTrace]
  refine ⟨46941475797350082938943787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62588634396466777251925049 46941475797350082938943787)
  ·
    refine ⟨70412213696025124408415681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46941475797350082938943787 70412213696025124408415681)
    ·
      refine ⟨52809160272018843306311761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70412213696025124408415681 52809160272018843306311761)
      ·
        refine ⟨39606870204014132479733821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52809160272018843306311761 39606870204014132479733821)
        ·
          refine ⟨14852576326505299679900183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39606870204014132479733821 14852576326505299679900183)
          ·
            refine ⟨22278864489757949519850275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14852576326505299679900183 22278864489757949519850275)
            ·
              refine ⟨33418296734636924279775413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22278864489757949519850275 33418296734636924279775413)
              ·
                refine ⟨3132965318872211651228945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33418296734636924279775413 3132965318872211651228945)
                ·
                  refine ⟨2349723989154158738421709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132965318872211651228945 2349723989154158738421709)
                  ·
                    refine ⟨881146495932809526908141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2349723989154158738421709 881146495932809526908141)
                    ·
                      rfl

theorem cell22_2574040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_2574040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574040 prefixEnd_2574040 := by exact prefixLift 2574040
  have htrace : WordTrace (prefixWord ++ tailWord_2574040) baseStart_2574040 baseEnd_2574040 := by
    simpa [prefixWord, tailWord_2574040, baseEnd_2574040] using wordTrace_append hprefix tailTrace_2574040
  have hstable : (prefixWord ++ tailWord_2574040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574040).length < 2 ^ (prefixWord ++ tailWord_2574040).sum := by decide
  have hdescent : baseEnd_2574040 < baseStart_2574040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574128 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_2574128 : Nat := 118140960795 + 2574128 * 2 ^ 59
def prefixEnd_2574128 : Nat := 4983230072969 + 3 ^ 40 * 2574128 * 2
def baseEnd_2574128 : Nat := 881176620131206630707871

theorem tailTrace_2574128 : CollatzResearch.WordTrace tailWord_2574128 prefixEnd_2574128 881176620131206630707871 := by
  unfold tailWord_2574128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46943080609190678453545519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62590774145587571271394025 46943080609190678453545519)
  ·
    refine ⟨70414620913786017680318279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46943080609190678453545519 70414620913786017680318279)
    ·
      refine ⟨105621931370679026520477419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70414620913786017680318279 105621931370679026520477419)
      ·
        refine ⟨158432897056018539780716129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105621931370679026520477419 158432897056018539780716129)
        ·
          refine ⟨118824672792013904835537097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158432897056018539780716129 118824672792013904835537097)
          ·
            refine ⟨89118504594010428626652823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118824672792013904835537097 89118504594010428626652823)
            ·
              refine ⟨133677756891015642939979235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89118504594010428626652823 133677756891015642939979235)
              ·
                refine ⟨200516635336523464409968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133677756891015642939979235 200516635336523464409968853)
                ·
                  refine ⟨4699608640699768697108645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 200516635336523464409968853 4699608640699768697108645)
                  ·
                    refine ⟨881176620131206630707871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699608640699768697108645 881176620131206630707871)
                    ·
                      rfl

theorem cell22_2574128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_2574128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574128 prefixEnd_2574128 := by exact prefixLift 2574128
  have htrace : WordTrace (prefixWord ++ tailWord_2574128) baseStart_2574128 baseEnd_2574128 := by
    simpa [prefixWord, tailWord_2574128, baseEnd_2574128] using wordTrace_append hprefix tailTrace_2574128
  have hstable : (prefixWord ++ tailWord_2574128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574128).length < 2 ^ (prefixWord ++ tailWord_2574128).sum := by decide
  have hdescent : baseEnd_2574128 < baseStart_2574128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574162 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2574162 : Nat := 118140960795 + 2574162 * 2 ^ 59
def prefixEnd_2574162 : Nat := 4983230072969 + 3 ^ 40 * 2574162 * 2
def baseEnd_2574162 : Nat := 881188259026041875357767

theorem tailTrace_2574162 : CollatzResearch.WordTrace tailWord_2574162 prefixEnd_2574162 881188259026041875357767 := by
  unfold tailWord_2574162
  simp only [CollatzResearch.WordTrace]
  refine ⟨23471850325064545178457185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62591600866838787142552493 23471850325064545178457185)
  ·
    refine ⟨17603887743798408883842889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23471850325064545178457185 17603887743798408883842889)
    ·
      refine ⟨13202915807848806662882167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17603887743798408883842889 13202915807848806662882167)
      ·
        refine ⟨19804373711773209994323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13202915807848806662882167 19804373711773209994323251)
        ·
          refine ⟨29706560567659814991484877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19804373711773209994323251 29706560567659814991484877)
          ·
            refine ⟨11139960212872430621806829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29706560567659814991484877 11139960212872430621806829)
            ·
              refine ⟨4177485079827161483177561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11139960212872430621806829 4177485079827161483177561)
              ·
                refine ⟨3133113809870371112383171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177485079827161483177561 3133113809870371112383171)
                ·
                  refine ⟨4699670714805556668574757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133113809870371112383171 4699670714805556668574757)
                  ·
                    refine ⟨881188259026041875357767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699670714805556668574757 881188259026041875357767)
                    ·
                      rfl

theorem cell22_2574162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2574162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574162 prefixEnd_2574162 := by exact prefixLift 2574162
  have htrace : WordTrace (prefixWord ++ tailWord_2574162) baseStart_2574162 baseEnd_2574162 := by
    simpa [prefixWord, tailWord_2574162, baseEnd_2574162] using wordTrace_append hprefix tailTrace_2574162
  have hstable : (prefixWord ++ tailWord_2574162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574162).length < 2 ^ (prefixWord ++ tailWord_2574162).sum := by decide
  have hdescent : baseEnd_2574162 < baseStart_2574162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574175 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2574175 : Nat := 118140960795 + 2574175 * 2 ^ 59
def prefixEnd_2574175 : Nat := 4983230072969 + 3 ^ 40 * 2574175 * 2
def baseEnd_2574175 : Nat := 881192709191714174782727

theorem tailTrace_2574175 : CollatzResearch.WordTrace tailWord_2574175 prefixEnd_2574175 881192709191714174782727 := by
  unfold tailWord_2574175
  simp only [CollatzResearch.WordTrace]
  refine ⟨93887875449211083934051979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62591916966140722622701319 93887875449211083934051979)
  ·
    refine ⟨140831813173816625901077969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93887875449211083934051979 140831813173816625901077969)
    ·
      refine ⟨105623859880362469425808477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140831813173816625901077969 105623859880362469425808477)
      ·
        refine ⟨39608947455135926034678179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105623859880362469425808477 39608947455135926034678179)
        ·
          refine ⟨59413421182703889052017269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39608947455135926034678179 59413421182703889052017269)
          ·
            refine ⟨5570008235878489598626619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59413421182703889052017269 5570008235878489598626619)
            ·
              refine ⟨8355012353817734397939929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570008235878489598626619 8355012353817734397939929)
              ·
                refine ⟨6266259265363300798454947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355012353817734397939929 6266259265363300798454947)
                ·
                  refine ⟨9399388898044951197682421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266259265363300798454947 9399388898044951197682421)
                  ·
                    refine ⟨881192709191714174782727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9399388898044951197682421 881192709191714174782727)
                    ·
                      rfl

theorem cell22_2574175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2574175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574175 prefixEnd_2574175 := by exact prefixLift 2574175
  have htrace : WordTrace (prefixWord ++ tailWord_2574175) baseStart_2574175 baseEnd_2574175 := by
    simpa [prefixWord, tailWord_2574175, baseEnd_2574175] using wordTrace_append hprefix tailTrace_2574175
  have hstable : (prefixWord ++ tailWord_2574175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574175).length < 2 ^ (prefixWord ++ tailWord_2574175).sum := by decide
  have hdescent : baseEnd_2574175 < baseStart_2574175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574179 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 1, 4]
def baseStart_2574179 : Nat := 118140960795 + 2574179 * 2 ^ 59
def prefixEnd_2574179 : Nat := 4983230072969 + 3 ^ 40 * 2574179 * 2
def baseEnd_2574179 : Nat := 881194078473459497682715

theorem tailTrace_2574179 : CollatzResearch.WordTrace tailWord_2574179 prefixEnd_2574179 881194078473459497682715 := by
  unfold tailWord_2574179
  simp only [CollatzResearch.WordTrace]
  refine ⟨93888021341196592617197591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62592014227464395078131727 93888021341196592617197591)
  ·
    refine ⟨140832032011794888925796387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93888021341196592617197591 140832032011794888925796387)
    ·
      refine ⟨211248048017692333388694581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140832032011794888925796387 211248048017692333388694581)
      ·
        refine ⟨19804504501658656255190117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211248048017692333388694581 19804504501658656255190117)
        ·
          refine ⟨3713344594060998047848147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19804504501658656255190117 3713344594060998047848147)
          ·
            refine ⟨5570016891091497071772221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713344594060998047848147 5570016891091497071772221)
            ·
              refine ⟨2088756334159311401914583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5570016891091497071772221 2088756334159311401914583)
              ·
                refine ⟨3133134501238967102871875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088756334159311401914583 3133134501238967102871875)
                ·
                  refine ⟨4699701751858450654307813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133134501238967102871875 4699701751858450654307813)
                  ·
                    refine ⟨881194078473459497682715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699701751858450654307813 881194078473459497682715)
                    ·
                      rfl

theorem cell22_2574179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 4].length) (baseStart_2574179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574179 prefixEnd_2574179 := by exact prefixLift 2574179
  have htrace : WordTrace (prefixWord ++ tailWord_2574179) baseStart_2574179 baseEnd_2574179 := by
    simpa [prefixWord, tailWord_2574179, baseEnd_2574179] using wordTrace_append hprefix tailTrace_2574179
  have hstable : (prefixWord ++ tailWord_2574179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574179).length < 2 ^ (prefixWord ++ tailWord_2574179).sum := by decide
  have hdescent : baseEnd_2574179 < baseStart_2574179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574188 : List Nat := [2, 2, 1, 1, 4, 12]
def baseStart_2574188 : Nat := 118140960795 + 2574188 * 2 ^ 59
def prefixEnd_2574188 : Nat := 4983230072969 + 3 ^ 40 * 2574188 * 2
def baseEnd_2574188 : Nat := 10878977276017116965527

theorem tailTrace_2574188 : CollatzResearch.WordTrace tailWord_2574188 prefixEnd_2574188 10878977276017116965527 := by
  unfold tailWord_2574188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46944174799081993577137609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62592233065442658102850145 46944174799081993577137609)
  ·
    refine ⟨35208131099311495182853207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46944174799081993577137609 35208131099311495182853207)
    ·
      refine ⟨52812196648967242774279811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35208131099311495182853207 52812196648967242774279811)
      ·
        refine ⟨79218294973450864161419717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52812196648967242774279811 79218294973450864161419717)
        ·
          refine ⟨14853430307522037030266197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79218294973450864161419717 14853430307522037030266197)
          ·
            refine ⟨10878977276017116965527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14853430307522037030266197 10878977276017116965527)
            ·
              rfl

theorem cell22_2574188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 12].length) (baseStart_2574188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574188 prefixEnd_2574188 := by exact prefixLift 2574188
  have htrace : WordTrace (prefixWord ++ tailWord_2574188) baseStart_2574188 baseEnd_2574188 := by
    simpa [prefixWord, tailWord_2574188, baseEnd_2574188] using wordTrace_append hprefix tailTrace_2574188
  have hstable : (prefixWord ++ tailWord_2574188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574188).length < 2 ^ (prefixWord ++ tailWord_2574188).sum := by decide
  have hdescent : baseEnd_2574188 < baseStart_2574188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_2574203 : Nat := 118140960795 + 2574203 * 2 ^ 59
def prefixEnd_2574203 : Nat := 4983230072969 + 3 ^ 40 * 2574203 * 2
def baseEnd_2574203 : Nat := 881202294163931435082641

theorem tailTrace_2574203 : CollatzResearch.WordTrace tailWord_2574203 prefixEnd_2574203 881202294163931435082641 := by
  unfold tailWord_2574203
  simp only [CollatzResearch.WordTrace]
  refine ⟨93888896693109644716071263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62592597795406429810714175 93888896693109644716071263)
  ·
    refine ⟨140833345039664467074106895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93888896693109644716071263 140833345039664467074106895)
    ·
      refine ⟨211250017559496700611160343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140833345039664467074106895 211250017559496700611160343)
      ·
        refine ⟨316875026339245050916740515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211250017559496700611160343 316875026339245050916740515)
        ·
          refine ⟨475312539508867576375110773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316875026339245050916740515 475312539508867576375110773)
          ·
            refine ⟨44560550578956335285166635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 475312539508867576375110773 44560550578956335285166635)
            ·
              refine ⟨66840825868434502927749953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44560550578956335285166635 66840825868434502927749953)
              ·
                refine ⟨50130619401325877195812465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66840825868434502927749953 50130619401325877195812465)
                ·
                  refine ⟨37597964550994407896859349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50130619401325877195812465 37597964550994407896859349)
                  ·
                    refine ⟨881202294163931435082641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37597964550994407896859349 881202294163931435082641)
                    ·
                      rfl

theorem cell22_2574203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_2574203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574203 prefixEnd_2574203 := by exact prefixLift 2574203
  have htrace : WordTrace (prefixWord ++ tailWord_2574203) baseStart_2574203 baseEnd_2574203 := by
    simpa [prefixWord, tailWord_2574203, baseEnd_2574203] using wordTrace_append hprefix tailTrace_2574203
  have hstable : (prefixWord ++ tailWord_2574203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574203).length < 2 ^ (prefixWord ++ tailWord_2574203).sum := by decide
  have hdescent : baseEnd_2574203 < baseStart_2574203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574209 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2574209 : Nat := 118140960795 + 2574209 * 2 ^ 59
def prefixEnd_2574209 : Nat := 4983230072969 + 3 ^ 40 * 2574209 * 2
def baseEnd_2574209 : Nat := 881204348086549419432623

theorem tailTrace_2574209 : CollatzResearch.WordTrace tailWord_2574209 prefixEnd_2574209 881204348086549419432623 := by
  unfold tailWord_2574209
  simp only [CollatzResearch.WordTrace]
  refine ⟨93889115531087907740789681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62592743687391938493859787 93889115531087907740789681)
  ·
    refine ⟨70416836648315930805592261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93889115531087907740789681 70416836648315930805592261)
    ·
      refine ⟨13203156871559237026048549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70416836648315930805592261 13203156871559237026048549)
      ·
        refine ⟨2475591913417356942384103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13203156871559237026048549 2475591913417356942384103)
        ·
          refine ⟨3713387870126035413576155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475591913417356942384103 3713387870126035413576155)
          ·
            refine ⟨5570081805189053120364233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713387870126035413576155 5570081805189053120364233)
            ·
              refine ⟨4177561353891789840273175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570081805189053120364233 4177561353891789840273175)
              ·
                refine ⟨6266342030837684760409763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177561353891789840273175 6266342030837684760409763)
                ·
                  refine ⟨9399513046256527140614645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6266342030837684760409763 9399513046256527140614645)
                  ·
                    refine ⟨881204348086549419432623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9399513046256527140614645 881204348086549419432623)
                    ·
                      rfl

theorem cell22_2574209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2574209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574209 prefixEnd_2574209 := by exact prefixLift 2574209
  have htrace : WordTrace (prefixWord ++ tailWord_2574209) baseStart_2574209 baseEnd_2574209 := by
    simpa [prefixWord, tailWord_2574209, baseEnd_2574209] using wordTrace_append hprefix tailTrace_2574209
  have hstable : (prefixWord ++ tailWord_2574209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574209).length < 2 ^ (prefixWord ++ tailWord_2574209).sum := by decide
  have hdescent : baseEnd_2574209 < baseStart_2574209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574230 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2574230 : Nat := 118140960795 + 2574230 * 2 ^ 59
def prefixEnd_2574230 : Nat := 4983230072969 + 3 ^ 40 * 2574230 * 2
def baseEnd_2574230 : Nat := 881211536815712364657559

theorem tailTrace_2574230 : CollatzResearch.WordTrace tailWord_2574230 prefixEnd_2574230 881211536815712364657559 := by
  unfold tailWord_2574230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868117591500739270456509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62593254309341218884869429 5868117591500739270456509)
  ·
    refine ⟨2200544096812777226421191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5868117591500739270456509 2200544096812777226421191)
    ·
      refine ⟨3300816145219165839631787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200544096812777226421191 3300816145219165839631787)
      ·
        refine ⟨4951224217828748759447681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300816145219165839631787 4951224217828748759447681)
        ·
          refine ⟨3713418163371561569585761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951224217828748759447681 3713418163371561569585761)
          ·
            refine ⟨2785063622528671177189321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713418163371561569585761 2785063622528671177189321)
            ·
              refine ⟨2088797716896503382891991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785063622528671177189321 2088797716896503382891991)
              ·
                refine ⟨3133196575344755074337987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088797716896503382891991 3133196575344755074337987)
                ·
                  refine ⟨4699794863017132611506981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133196575344755074337987 4699794863017132611506981)
                  ·
                    refine ⟨881211536815712364657559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699794863017132611506981 881211536815712364657559)
                    ·
                      rfl

theorem cell22_2574230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2574230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574230 prefixEnd_2574230 := by exact prefixLift 2574230
  have htrace : WordTrace (prefixWord ++ tailWord_2574230) baseStart_2574230 baseEnd_2574230 := by
    simpa [prefixWord, tailWord_2574230, baseEnd_2574230] using wordTrace_append hprefix tailTrace_2574230
  have hstable : (prefixWord ++ tailWord_2574230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574230).length < 2 ^ (prefixWord ++ tailWord_2574230).sum := by decide
  have hdescent : baseEnd_2574230 < baseStart_2574230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574265 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_2574265 : Nat := 118140960795 + 2574265 * 2 ^ 59
def prefixEnd_2574265 : Nat := 4983230072969 + 3 ^ 40 * 2574265 * 2
def baseEnd_2574265 : Nat := 881223518030983940032451

theorem tailTrace_2574265 : CollatzResearch.WordTrace tailWord_2574265 prefixEnd_2574265 881223518030983940032451 := by
  unfold tailWord_2574265
  simp only [CollatzResearch.WordTrace]
  refine ⟨93891158018885029304828249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62594105345923352869885499 93891158018885029304828249)
  ·
    refine ⟨70418368514163771978621187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93891158018885029304828249 70418368514163771978621187)
    ·
      refine ⟨105627552771245657967931781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70418368514163771978621187 105627552771245657967931781)
      ·
        refine ⟨19805166144608560868987209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105627552771245657967931781 19805166144608560868987209)
        ·
          refine ⟨14853874608456420651740407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19805166144608560868987209 14853874608456420651740407)
          ·
            refine ⟨22280811912684630977610611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14853874608456420651740407 22280811912684630977610611)
            ·
              refine ⟨33421217869026946466415917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22280811912684630977610611 33421217869026946466415917)
              ·
                refine ⟨12532956700885104924905969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33421217869026946466415917 12532956700885104924905969)
                ·
                  refine ⟨9399717525663828693679477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12532956700885104924905969 9399717525663828693679477)
                  ·
                    refine ⟨881223518030983940032451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9399717525663828693679477 881223518030983940032451)
                    ·
                      rfl

theorem cell22_2574265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_2574265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574265 prefixEnd_2574265 := by exact prefixLift 2574265
  have htrace : WordTrace (prefixWord ++ tailWord_2574265) baseStart_2574265 baseEnd_2574265 := by
    simpa [prefixWord, tailWord_2574265, baseEnd_2574265] using wordTrace_append hprefix tailTrace_2574265
  have hstable : (prefixWord ++ tailWord_2574265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574265).length < 2 ^ (prefixWord ++ tailWord_2574265).sum := by decide
  have hdescent : baseEnd_2574265 < baseStart_2574265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574357 : List Nat := [1, 3, 2, 1, 6, 9]
def baseStart_2574357 : Nat := 118140960795 + 2574357 * 2 ^ 59
def prefixEnd_2574357 : Nat := 4983230072969 + 3 ^ 40 * 2574357 * 2
def baseEnd_2574357 : Nat := 10879691500137362552249

theorem tailTrace_2574357 : CollatzResearch.WordTrace tailWord_2574357 prefixEnd_2574357 10879691500137362552249 := by
  unfold tailWord_2574357
  simp only [CollatzResearch.WordTrace]
  refine ⟨93894513534551729017177325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62596342356367819344784883 93894513534551729017177325)
  ·
    refine ⟨35210442575456898381441497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93894513534551729017177325 35210442575456898381441497)
    ·
      refine ⟨26407831931592673786081123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35210442575456898381441497 26407831931592673786081123)
      ·
        refine ⟨39611747897389010679121685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26407831931592673786081123 39611747897389010679121685)
        ·
          refine ⟨1856800682690109875583829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39611747897389010679121685 1856800682690109875583829)
          ·
            refine ⟨10879691500137362552249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1856800682690109875583829 10879691500137362552249)
            ·
              rfl

theorem cell22_2574357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 9].length) (baseStart_2574357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574357 prefixEnd_2574357 := by exact prefixLift 2574357
  have htrace : WordTrace (prefixWord ++ tailWord_2574357) baseStart_2574357 baseEnd_2574357 := by
    simpa [prefixWord, tailWord_2574357, baseEnd_2574357] using wordTrace_append hprefix tailTrace_2574357
  have hstable : (prefixWord ++ tailWord_2574357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574357).length < 2 ^ (prefixWord ++ tailWord_2574357).sum := by decide
  have hdescent : baseEnd_2574357 < baseStart_2574357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574406 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2574406 : Nat := 118140960795 + 2574406 * 2 ^ 59
def prefixEnd_2574406 : Nat := 4983230072969 + 3 ^ 40 * 2574406 * 2
def baseEnd_2574406 : Nat := 881271785212506572257019

theorem tailTrace_2574406 : CollatzResearch.WordTrace tailWord_2574406 prefixEnd_2574406 881271785212506572257019 := by
  unfold tailWord_2574406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934259397230444074553471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62597533807582806923807381 2934259397230444074553471)
  ·
    refine ⟨4401389095845666111830207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934259397230444074553471 4401389095845666111830207)
    ·
      refine ⟨6602083643768499167745311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401389095845666111830207 6602083643768499167745311)
      ·
        refine ⟨9903125465652748751617967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602083643768499167745311 9903125465652748751617967)
        ·
          refine ⟨14854688198479123127426951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903125465652748751617967 14854688198479123127426951)
          ·
            refine ⟨22282032297718684691140427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14854688198479123127426951 22282032297718684691140427)
            ·
              refine ⟨33423048446578027036710641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22282032297718684691140427 33423048446578027036710641)
              ·
                refine ⟨25067286334933520277532981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33423048446578027036710641 25067286334933520277532981)
                ·
                  refine ⟨2350058093900017526018717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25067286334933520277532981 2350058093900017526018717)
                  ·
                    refine ⟨881271785212506572257019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350058093900017526018717 881271785212506572257019)
                    ·
                      rfl

theorem cell22_2574406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2574406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574406 prefixEnd_2574406 := by exact prefixLift 2574406
  have htrace : WordTrace (prefixWord ++ tailWord_2574406) baseStart_2574406 baseEnd_2574406 := by
    simpa [prefixWord, tailWord_2574406, baseEnd_2574406] using wordTrace_append hprefix tailTrace_2574406
  have hstable : (prefixWord ++ tailWord_2574406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574406).length < 2 ^ (prefixWord ++ tailWord_2574406).sum := by decide
  have hdescent : baseEnd_2574406 < baseStart_2574406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574447 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 6]
def baseStart_2574447 : Nat := 118140960795 + 2574447 * 2 ^ 59
def prefixEnd_2574447 : Nat := 4983230072969 + 3 ^ 40 * 2574447 * 2
def baseEnd_2574447 : Nat := 293761940116798710660631

theorem tailTrace_2574447 : CollatzResearch.WordTrace tailWord_2574447 prefixEnd_2574447 293761940116798710660631 := by
  unfold tailWord_2574447
  simp only [CollatzResearch.WordTrace]
  refine ⟨93897796104225674387953595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62598530736150449591969063 93897796104225674387953595)
  ·
    refine ⟨140846694156338511581930393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93897796104225674387953595 140846694156338511581930393)
    ·
      refine ⟨105635020617253883686447795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140846694156338511581930393 105635020617253883686447795)
      ·
        refine ⟨158452530925880825529671693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105635020617253883686447795 158452530925880825529671693)
        ·
          refine ⟨59419699097205309573626885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158452530925880825529671693 59419699097205309573626885)
          ·
            refine ⟨11141193580725995545055041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59419699097205309573626885 11141193580725995545055041)
            ·
              refine ⟨8355895185544496658791281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141193580725995545055041 8355895185544496658791281)
              ·
                refine ⟨6266921389158372494093461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355895185544496658791281 6266921389158372494093461)
                ·
                  refine ⟨293761940116798710660631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6266921389158372494093461 293761940116798710660631)
                  ·
                    rfl

theorem cell22_2574447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_2574447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574447 prefixEnd_2574447 := by exact prefixLift 2574447
  have htrace : WordTrace (prefixWord ++ tailWord_2574447) baseStart_2574447 baseEnd_2574447 := by
    simpa [prefixWord, tailWord_2574447, baseEnd_2574447] using wordTrace_append hprefix tailTrace_2574447
  have hstable : (prefixWord ++ tailWord_2574447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574447).length < 2 ^ (prefixWord ++ tailWord_2574447).sum := by decide
  have hdescent : baseEnd_2574447 < baseStart_2574447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574449 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2574449 : Nat := 118140960795 + 2574449 * 2 ^ 59
def prefixEnd_2574449 : Nat := 4983230072969 + 3 ^ 40 * 2574449 * 2
def baseEnd_2574449 : Nat := 881286504991268793431887

theorem tailTrace_2574449 : CollatzResearch.WordTrace tailWord_2574449 prefixEnd_2574449 881286504991268793431887 := by
  unfold tailWord_2574449
  simp only [CollatzResearch.WordTrace]
  refine ⟨93897869050218428729526401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62598579366812285819684267 93897869050218428729526401)
  ·
    refine ⟨70423401787663821547144801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93897869050218428729526401 70423401787663821547144801)
    ·
      refine ⟨52817551340747866160358601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70423401787663821547144801 52817551340747866160358601)
      ·
        refine ⟨39613163505560899620268951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52817551340747866160358601 39613163505560899620268951)
        ·
          refine ⟨59419745258341349430403427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39613163505560899620268951 59419745258341349430403427)
          ·
            refine ⟨89129617887512024145605141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59419745258341349430403427 89129617887512024145605141)
            ·
              refine ⟨4177950838477126131825241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89129617887512024145605141 4177950838477126131825241)
              ·
                refine ⟨3133463128857844598868931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177950838477126131825241 3133463128857844598868931)
                ·
                  refine ⟨4700194693286766898303397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133463128857844598868931 4700194693286766898303397)
                  ·
                    refine ⟨881286504991268793431887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700194693286766898303397 881286504991268793431887)
                    ·
                      rfl

theorem cell22_2574449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2574449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574449 prefixEnd_2574449 := by exact prefixLift 2574449
  have htrace : WordTrace (prefixWord ++ tailWord_2574449) baseStart_2574449 baseEnd_2574449 := by
    simpa [prefixWord, tailWord_2574449, baseEnd_2574449] using wordTrace_append hprefix tailTrace_2574449
  have hstable : (prefixWord ++ tailWord_2574449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574449).length < 2 ^ (prefixWord ++ tailWord_2574449).sum := by decide
  have hdescent : baseEnd_2574449 < baseStart_2574449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574496 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_2574496 : Nat := 118140960795 + 2574496 * 2 ^ 59
def prefixEnd_2574496 : Nat := 4983230072969 + 3 ^ 40 * 2574496 * 2
def baseEnd_2574496 : Nat := 881302594051776337506743

theorem tailTrace_2574496 : CollatzResearch.WordTrace tailWord_2574496 prefixEnd_2574496 881302594051776337506743 := by
  unfold tailWord_2574496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46949791640524077878243671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62599722187365437170991561 46949791640524077878243671)
  ·
    refine ⟨70424687460786116817365507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46949791640524077878243671 70424687460786116817365507)
    ·
      refine ⟨105637031191179175226048261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70424687460786116817365507 105637031191179175226048261)
      ·
        refine ⟨19806943348346095354884049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105637031191179175226048261 19806943348346095354884049)
        ·
          refine ⟨14855207511259571516163037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19806943348346095354884049 14855207511259571516163037)
          ·
            refine ⟨5570702816722339318561139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14855207511259571516163037 5570702816722339318561139)
            ·
              refine ⟨8356054225083508977841709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570702816722339318561139 8356054225083508977841709)
              ·
                refine ⟨3133520334406315866690641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8356054225083508977841709 3133520334406315866690641)
                ·
                  refine ⟨2350140250804736900017981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133520334406315866690641 2350140250804736900017981)
                  ·
                    refine ⟨881302594051776337506743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350140250804736900017981 881302594051776337506743)
                    ·
                      rfl

theorem cell22_2574496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_2574496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574496 prefixEnd_2574496 := by exact prefixLift 2574496
  have htrace : WordTrace (prefixWord ++ tailWord_2574496) baseStart_2574496 baseEnd_2574496 := by
    simpa [prefixWord, tailWord_2574496, baseEnd_2574496] using wordTrace_append hprefix tailTrace_2574496
  have hstable : (prefixWord ++ tailWord_2574496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574496).length < 2 ^ (prefixWord ++ tailWord_2574496).sum := by decide
  have hdescent : baseEnd_2574496 < baseStart_2574496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574509 : List Nat := [1, 5, 2, 1, 2, 1, 2, 8]
def baseStart_2574509 : Nat := 118140960795 + 2574509 * 2 ^ 59
def prefixEnd_2574509 : Nat := 4983230072969 + 3 ^ 40 * 2574509 * 2
def baseEnd_2574509 : Nat := 97923004913049848547967

theorem tailTrace_2574509 : CollatzResearch.WordTrace tailWord_2574509 prefixEnd_2574509 97923004913049848547967 := by
  unfold tailWord_2574509
  simp only [CollatzResearch.WordTrace]
  refine ⟨93900057430001058976710581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62600038286667372651140387 93900057430001058976710581)
  ·
    refine ⟨8803130384062599279066617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93900057430001058976710581 8803130384062599279066617)
    ·
      refine ⟨6602347788046949459299963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8803130384062599279066617 6602347788046949459299963)
      ·
        refine ⟨9903521682070424188949945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602347788046949459299963 9903521682070424188949945)
        ·
          refine ⟨7427641261552818141712459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903521682070424188949945 7427641261552818141712459)
          ·
            refine ⟨11141461892329227212568689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427641261552818141712459 11141461892329227212568689)
            ·
              refine ⟨8356096419246920409426517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11141461892329227212568689 8356096419246920409426517)
              ·
                refine ⟨97923004913049848547967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8356096419246920409426517 97923004913049848547967)
                ·
                  rfl

theorem cell22_2574509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 8].length) (baseStart_2574509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574509 prefixEnd_2574509 := by exact prefixLift 2574509
  have htrace : WordTrace (prefixWord ++ tailWord_2574509) baseStart_2574509 baseEnd_2574509 := by
    simpa [prefixWord, tailWord_2574509, baseEnd_2574509] using wordTrace_append hprefix tailTrace_2574509
  have hstable : (prefixWord ++ tailWord_2574509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574509).length < 2 ^ (prefixWord ++ tailWord_2574509).sum := by decide
  have hdescent : baseEnd_2574509 < baseStart_2574509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574530 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2574530 : Nat := 118140960795 + 2574530 * 2 ^ 59
def prefixEnd_2574530 : Nat := 4983230072969 + 3 ^ 40 * 2574530 * 2
def baseEnd_2574530 : Nat := 881314232946611582156639

theorem tailTrace_2574530 : CollatzResearch.WordTrace tailWord_2574530 prefixEnd_2574530 881314232946611582156639 := by
  unfold tailWord_2574530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475205840731244890806261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62600548908616653042150029 23475205840731244890806261)
  ·
    refine ⟨2200800547568554208513087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23475205840731244890806261 2200800547568554208513087)
    ·
      refine ⟨3301200821352831312769631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200800547568554208513087 3301200821352831312769631)
      ·
        refine ⟨4951801232029246969154447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301200821352831312769631 4951801232029246969154447)
        ·
          refine ⟨7427701848043870453731671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4951801232029246969154447 7427701848043870453731671)
          ·
            refine ⟨11141552772065805680597507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427701848043870453731671 11141552772065805680597507)
            ·
              refine ⟨16712329158098708520896261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11141552772065805680597507 16712329158098708520896261)
              ·
                refine ⟨3133561717143507847668049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16712329158098708520896261 3133561717143507847668049)
                ·
                  refine ⟨2350171287857630885751037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133561717143507847668049 2350171287857630885751037)
                  ·
                    refine ⟨881314232946611582156639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350171287857630885751037 881314232946611582156639)
                    ·
                      rfl

theorem cell22_2574530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2574530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574530 prefixEnd_2574530 := by exact prefixLift 2574530
  have htrace : WordTrace (prefixWord ++ tailWord_2574530) baseStart_2574530 baseEnd_2574530 := by
    simpa [prefixWord, tailWord_2574530, baseEnd_2574530] using wordTrace_append hprefix tailTrace_2574530
  have hstable : (prefixWord ++ tailWord_2574530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574530).length < 2 ^ (prefixWord ++ tailWord_2574530).sum := by decide
  have hdescent : baseEnd_2574530 < baseStart_2574530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574554 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_2574554 : Nat := 118140960795 + 2574554 * 2 ^ 59
def prefixEnd_2574554 : Nat := 4983230072969 + 3 ^ 40 * 2574554 * 2
def baseEnd_2574554 : Nat := 293774149545694506518855

theorem tailTrace_2574554 : CollatzResearch.WordTrace tailWord_2574554 prefixEnd_2574554 293774149545694506518855 := by
  unfold tailWord_2574554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475424678709507915524679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62601132476558687774732477 23475424678709507915524679)
  ·
    refine ⟨35213137018064261873287019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23475424678709507915524679 35213137018064261873287019)
    ·
      refine ⟨52819705527096392809930529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35213137018064261873287019 52819705527096392809930529)
      ·
        refine ⟨39614779145322294607447897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52819705527096392809930529 39614779145322294607447897)
        ·
          refine ⟨29711084358991720955585923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39614779145322294607447897 29711084358991720955585923)
          ·
            refine ⟨44566626538487581433378885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29711084358991720955585923 44566626538487581433378885)
            ·
              refine ⟨8356242475966421518758541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44566626538487581433378885 8356242475966421518758541)
              ·
                refine ⟨3133590928487408069534453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8356242475966421518758541 3133590928487408069534453)
                ·
                  refine ⟨293774149545694506518855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133590928487408069534453 293774149545694506518855)
                  ·
                    rfl

theorem cell22_2574554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_2574554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574554 prefixEnd_2574554 := by exact prefixLift 2574554
  have htrace : WordTrace (prefixWord ++ tailWord_2574554) baseStart_2574554 baseEnd_2574554 := by
    simpa [prefixWord, tailWord_2574554, baseEnd_2574554] using wordTrace_append hprefix tailTrace_2574554
  have hstable : (prefixWord ++ tailWord_2574554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574554).length < 2 ^ (prefixWord ++ tailWord_2574554).sum := by decide
  have hdescent : baseEnd_2574554 < baseStart_2574554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574562 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2574562 : Nat := 118140960795 + 2574562 * 2 ^ 59
def prefixEnd_2574562 : Nat := 4983230072969 + 3 ^ 40 * 2574562 * 2
def baseEnd_2574562 : Nat := 881325187200574165356541

theorem tailTrace_2574562 : CollatzResearch.WordTrace tailWord_2574562 prefixEnd_2574562 881325187200574165356541 := by
  unfold tailWord_2574562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475497624702262257097485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62601326999206032685593293 23475497624702262257097485)
  ·
    refine ⟨8803311609263348346411557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23475497624702262257097485 8803311609263348346411557)
    ·
      refine ⟨1650620926736877814952167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8803311609263348346411557 1650620926736877814952167)
      ·
        refine ⟨2475931390105316722428251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650620926736877814952167 2475931390105316722428251)
        ·
          refine ⟨3713897085157975083642377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475931390105316722428251 3713897085157975083642377)
          ·
            refine ⟨2785422813868481312731783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713897085157975083642377 2785422813868481312731783)
            ·
              refine ⟨4178134220802721969097675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785422813868481312731783 4178134220802721969097675)
              ·
                refine ⟨6267201331204082953646513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178134220802721969097675 6267201331204082953646513)
                ·
                  refine ⟨4700400998403062215234885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6267201331204082953646513 4700400998403062215234885)
                  ·
                    refine ⟨881325187200574165356541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700400998403062215234885 881325187200574165356541)
                    ·
                      rfl

theorem cell22_2574562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2574562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574562 prefixEnd_2574562 := by exact prefixLift 2574562
  have htrace : WordTrace (prefixWord ++ tailWord_2574562) baseStart_2574562 baseEnd_2574562 := by
    simpa [prefixWord, tailWord_2574562, baseEnd_2574562] using wordTrace_append hprefix tailTrace_2574562
  have hstable : (prefixWord ++ tailWord_2574562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574562).length < 2 ^ (prefixWord ++ tailWord_2574562).sum := by decide
  have hdescent : baseEnd_2574562 < baseStart_2574562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574618 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_2574618 : Nat := 118140960795 + 2574618 * 2 ^ 59
def prefixEnd_2574618 : Nat := 4983230072969 + 3 ^ 40 * 2574618 * 2
def baseEnd_2574618 : Nat := 881344357145008685956369

theorem tailTrace_2574618 : CollatzResearch.WordTrace tailWord_2574618 prefixEnd_2574618 881344357145008685956369 := by
  unfold tailWord_2574618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476008246651542648107127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62602688657737447061619005 23476008246651542648107127)
  ·
    refine ⟨35214012369977313972160691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23476008246651542648107127 35214012369977313972160691)
    ·
      refine ⟨52821018554965970958241037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35214012369977313972160691 52821018554965970958241037)
      ·
        refine ⟨19807881958112239109340389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52821018554965970958241037 19807881958112239109340389)
        ·
          refine ⟨3713977867146044833001323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19807881958112239109340389 3713977867146044833001323)
          ·
            refine ⟨5570966800719067249501985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713977867146044833001323 5570966800719067249501985)
            ·
              refine ⟨4178225100539300437126489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570966800719067249501985 4178225100539300437126489)
              ·
                refine ⟨3133668825404475327844867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178225100539300437126489 3133668825404475327844867)
                ·
                  refine ⟨4700503238106712991767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133668825404475327844867 4700503238106712991767301)
                  ·
                    refine ⟨881344357145008685956369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700503238106712991767301 881344357145008685956369)
                    ·
                      rfl

theorem cell22_2574618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_2574618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574618 prefixEnd_2574618 := by exact prefixLift 2574618
  have htrace : WordTrace (prefixWord ++ tailWord_2574618) baseStart_2574618 baseEnd_2574618 := by
    simpa [prefixWord, tailWord_2574618, baseEnd_2574618] using wordTrace_append hprefix tailTrace_2574618
  have hstable : (prefixWord ++ tailWord_2574618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574618).length < 2 ^ (prefixWord ++ tailWord_2574618).sum := by decide
  have hdescent : baseEnd_2574618 < baseStart_2574618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574686 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2574686 : Nat := 118140960795 + 2574686 * 2 ^ 59
def prefixEnd_2574686 : Nat := 4983230072969 + 3 ^ 40 * 2574686 * 2
def baseEnd_2574686 : Nat := 881367634934679175256161

theorem tailTrace_2574686 : CollatzResearch.WordTrace tailWord_2574686 prefixEnd_2574686 881367634934679175256161 := by
  unfold tailWord_2574686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738314143794977275737989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62604342100239878803935941 11738314143794977275737989)
  ·
    refine ⟨2200933901961558239200873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11738314143794977275737989 2200933901961558239200873)
    ·
      refine ⟨1650700426471168679400655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200933901961558239200873 1650700426471168679400655)
      ·
        refine ⟨2476050639706753019100983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650700426471168679400655 2476050639706753019100983)
        ·
          refine ⟨3714075959560129528651475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476050639706753019100983 3714075959560129528651475)
          ·
            refine ⟨5571113939340194292977213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714075959560129528651475 5571113939340194292977213)
            ·
              refine ⟨2089167727252572859866455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5571113939340194292977213 2089167727252572859866455)
              ·
                refine ⟨3133751590878859289799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089167727252572859866455 3133751590878859289799683)
                ·
                  refine ⟨4700627386318288934699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133751590878859289799683 4700627386318288934699525)
                  ·
                    refine ⟨881367634934679175256161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4700627386318288934699525 881367634934679175256161)
                    ·
                      rfl

theorem cell22_2574686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2574686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574686 prefixEnd_2574686 := by exact prefixLift 2574686
  have htrace : WordTrace (prefixWord ++ tailWord_2574686) baseStart_2574686 baseEnd_2574686 := by
    simpa [prefixWord, tailWord_2574686, baseEnd_2574686] using wordTrace_append hprefix tailTrace_2574686
  have hstable : (prefixWord ++ tailWord_2574686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574686).length < 2 ^ (prefixWord ++ tailWord_2574686).sum := by decide
  have hdescent : baseEnd_2574686 < baseStart_2574686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574706 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_2574706 : Nat := 118140960795 + 2574706 * 2 ^ 59
def prefixEnd_2574706 : Nat := 4983230072969 + 3 ^ 40 * 2574706 * 2
def baseEnd_2574706 : Nat := 293791493781135263252033

theorem tailTrace_2574706 : CollatzResearch.WordTrace tailWord_2574706 prefixEnd_2574706 293791493781135263252033 := by
  unfold tailWord_2574706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476810652571840405407993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62604828406858241081087981 23476810652571840405407993)
  ·
    refine ⟨17607607989428880304055995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23476810652571840405407993 17607607989428880304055995)
    ·
      refine ⟨26411411984143320456083993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17607607989428880304055995 26411411984143320456083993)
      ·
        refine ⟨19808558988107490342062995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26411411984143320456083993 19808558988107490342062995)
        ·
          refine ⟨29712838482161235513094493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19808558988107490342062995 29712838482161235513094493)
          ·
            refine ⟨11142314430810463317410435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29712838482161235513094493 11142314430810463317410435)
            ·
              refine ⟨16713471646215694976115653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142314430810463317410435 16713471646215694976115653)
              ·
                refine ⟨3133775933665442808021685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16713471646215694976115653 3133775933665442808021685)
                ·
                  refine ⟨293791493781135263252033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3133775933665442808021685 293791493781135263252033)
                  ·
                    rfl

theorem cell22_2574706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_2574706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574706 prefixEnd_2574706 := by exact prefixLift 2574706
  have htrace : WordTrace (prefixWord ++ tailWord_2574706) baseStart_2574706 baseEnd_2574706 := by
    simpa [prefixWord, tailWord_2574706, baseEnd_2574706] using wordTrace_append hprefix tailTrace_2574706
  have hstable : (prefixWord ++ tailWord_2574706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574706).length < 2 ^ (prefixWord ++ tailWord_2574706).sum := by decide
  have hdescent : baseEnd_2574706 < baseStart_2574706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574721 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2574721 : Nat := 118140960795 + 2574721 * 2 ^ 59
def prefixEnd_2574721 : Nat := 4983230072969 + 3 ^ 40 * 2574721 * 2
def baseEnd_2574721 : Nat := 881379616149950750631053

theorem tailTrace_2574721 : CollatzResearch.WordTrace tailWord_2574721 prefixEnd_2574721 881379616149950750631053 := by
  unfold tailWord_2574721
  simp only [CollatzResearch.WordTrace]
  refine ⟨93907789705233019183428017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62605193136822012788952011 93907789705233019183428017)
  ·
    refine ⟨70430842278924764387571013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93907789705233019183428017 70430842278924764387571013)
    ·
      refine ⟨13205782927298393322669565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70430842278924764387571013 13205782927298393322669565)
      ·
        refine ⟨4952168597736897496001087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13205782927298393322669565 4952168597736897496001087)
        ·
          refine ⟨7428252896605346244001631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952168597736897496001087 7428252896605346244001631)
          ·
            refine ⟨11142379344908019366002447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428252896605346244001631 11142379344908019366002447)
            ·
              refine ⟨16713569017362029049003671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142379344908019366002447 16713569017362029049003671)
              ·
                refine ⟨25070353526043043573505507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16713569017362029049003671 25070353526043043573505507)
                ·
                  refine ⟨37605530289064565360258261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25070353526043043573505507 37605530289064565360258261)
                  ·
                    refine ⟨881379616149950750631053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37605530289064565360258261 881379616149950750631053)
                    ·
                      rfl

theorem cell22_2574721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2574721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574721 prefixEnd_2574721 := by exact prefixLift 2574721
  have htrace : WordTrace (prefixWord ++ tailWord_2574721) baseStart_2574721 baseEnd_2574721 := by
    simpa [prefixWord, tailWord_2574721, baseEnd_2574721] using wordTrace_append hprefix tailTrace_2574721
  have hstable : (prefixWord ++ tailWord_2574721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574721).length < 2 ^ (prefixWord ++ tailWord_2574721).sum := by decide
  have hdescent : baseEnd_2574721 < baseStart_2574721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574781 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2574781 : Nat := 118140960795 + 2574781 * 2 ^ 59
def prefixEnd_2574781 : Nat := 4983230072969 + 3 ^ 40 * 2574781 * 2
def baseEnd_2574781 : Nat := 881400155376130594130869

theorem tailTrace_2574781 : CollatzResearch.WordTrace tailWord_2574781 prefixEnd_2574781 881400155376130594130869 := by
  unfold tailWord_2574781
  simp only [CollatzResearch.WordTrace]
  refine ⟨93909978085015649430612197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62606652056677099620408131 93909978085015649430612197)
  ·
    refine ⟨17608120890940434268239787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93909978085015649430612197 17608120890940434268239787)
    ·
      refine ⟨26412181336410651402359681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17608120890940434268239787 26412181336410651402359681)
      ·
        refine ⟨19809136002307988551769761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26412181336410651402359681 19809136002307988551769761)
        ·
          refine ⟨14856852001730991413827321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19809136002307988551769761 14856852001730991413827321)
          ·
            refine ⟨11142639001298243560370491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14856852001730991413827321 11142639001298243560370491)
            ·
              refine ⟨16713958501947365340555737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11142639001298243560370491 16713958501947365340555737)
              ·
                refine ⟨12535468876460524005416803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16713958501947365340555737 12535468876460524005416803)
                ·
                  refine ⟨18803203314690786008125205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12535468876460524005416803 18803203314690786008125205)
                  ·
                    refine ⟨881400155376130594130869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18803203314690786008125205 881400155376130594130869)
                    ·
                      rfl

theorem cell22_2574781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2574781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574781 prefixEnd_2574781 := by exact prefixLift 2574781
  have htrace : WordTrace (prefixWord ++ tailWord_2574781) baseStart_2574781 baseEnd_2574781 := by
    simpa [prefixWord, tailWord_2574781, baseEnd_2574781] using wordTrace_append hprefix tailTrace_2574781
  have hstable : (prefixWord ++ tailWord_2574781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574781).length < 2 ^ (prefixWord ++ tailWord_2574781).sum := by decide
  have hdescent : baseEnd_2574781 < baseStart_2574781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574834 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_2574834 : Nat := 118140960795 + 2574834 * 2 ^ 59
def prefixEnd_2574834 : Nat := 4983230072969 + 3 ^ 40 * 2574834 * 2
def baseEnd_2574834 : Nat := 881418298359256122555707

theorem tailTrace_2574834 : CollatzResearch.WordTrace tailWord_2574834 prefixEnd_2574834 881418298359256122555707 := by
  unfold tailWord_2574834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23477977788455909870572889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62607940769215759654861037 23477977788455909870572889)
  ·
    refine ⟨17608483341341932402929667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23477977788455909870572889 17608483341341932402929667)
    ·
      refine ⟨26412725012012898604394501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17608483341341932402929667 26412725012012898604394501)
      ·
        refine ⟨4952385939752418488323969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26412725012012898604394501 4952385939752418488323969)
        ·
          refine ⟨3714289454814313866242977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952385939752418488323969 3714289454814313866242977)
          ·
            refine ⟨2785717091110735399682233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3714289454814313866242977 2785717091110735399682233)
            ·
              refine ⟨2089287818333051549761675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785717091110735399682233 2089287818333051549761675)
              ·
                refine ⟨3133931727499577324642513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089287818333051549761675 3133931727499577324642513)
                ·
                  refine ⟨2350448795624682993481885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133931727499577324642513 2350448795624682993481885)
                  ·
                    refine ⟨881418298359256122555707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350448795624682993481885 881418298359256122555707)
                    ·
                      rfl

theorem cell22_2574834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_2574834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574834 prefixEnd_2574834 := by exact prefixLift 2574834
  have htrace : WordTrace (prefixWord ++ tailWord_2574834) baseStart_2574834 baseEnd_2574834 := by
    simpa [prefixWord, tailWord_2574834, baseEnd_2574834] using wordTrace_append hprefix tailTrace_2574834
  have hstable : (prefixWord ++ tailWord_2574834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574834).length < 2 ^ (prefixWord ++ tailWord_2574834).sum := by decide
  have hdescent : baseEnd_2574834 < baseStart_2574834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574856 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_2574856 : Nat := 118140960795 + 2574856 * 2 ^ 59
def prefixEnd_2574856 : Nat := 4983230072969 + 3 ^ 40 * 2574856 * 2
def baseEnd_2574856 : Nat := 881425829408855398505639

theorem tailTrace_2574856 : CollatzResearch.WordTrace tailWord_2574856 prefixEnd_2574856 881425829408855398505639 := by
  unfold tailWord_2574856
  simp only [CollatzResearch.WordTrace]
  refine ⟨46956356779871968619796211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62608475706495958159728281 46956356779871968619796211)
  ·
    refine ⟨70434535169807952929694317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46956356779871968619796211 70434535169807952929694317)
    ·
      refine ⟨26412950688677982348635369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70434535169807952929694317 26412950688677982348635369)
      ·
        refine ⟨19809713016508486761476527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26412950688677982348635369 19809713016508486761476527)
        ·
          refine ⟨29714569524762730142214791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809713016508486761476527 29714569524762730142214791)
          ·
            refine ⟨44571854287144095213322187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29714569524762730142214791 44571854287144095213322187)
            ·
              refine ⟨66857781430716142819983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44571854287144095213322187 66857781430716142819983281)
              ·
                refine ⟨50143336073037107114987461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66857781430716142819983281 50143336073037107114987461)
                ·
                  refine ⟨9401875513694457584060149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50143336073037107114987461 9401875513694457584060149)
                  ·
                    refine ⟨881425829408855398505639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9401875513694457584060149 881425829408855398505639)
                    ·
                      rfl

theorem cell22_2574856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_2574856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574856 prefixEnd_2574856 := by exact prefixLift 2574856
  have htrace : WordTrace (prefixWord ++ tailWord_2574856) baseStart_2574856 baseEnd_2574856 := by
    simpa [prefixWord, tailWord_2574856, baseEnd_2574856] using wordTrace_append hprefix tailTrace_2574856
  have hstable : (prefixWord ++ tailWord_2574856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574856).length < 2 ^ (prefixWord ++ tailWord_2574856).sum := by decide
  have hdescent : baseEnd_2574856 < baseStart_2574856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574922 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2574922 : Nat := 118140960795 + 2574922 * 2 ^ 59
def prefixEnd_2574922 : Nat := 4983230072969 + 3 ^ 40 * 2574922 * 2
def baseEnd_2574922 : Nat := 881448422557653226355437

theorem tailTrace_2574922 : CollatzResearch.WordTrace tailWord_2574922 prefixEnd_2574922 881448422557653226355437 := by
  unfold tailWord_2574922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478780194376207627873755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62610080518336553674330013 23478780194376207627873755)
  ·
    refine ⟨35218170291564311441810633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478780194376207627873755 35218170291564311441810633)
    ·
      refine ⟨26413627718673233581357975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35218170291564311441810633 26413627718673233581357975)
      ·
        refine ⟨39620441578009850372036963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26413627718673233581357975 39620441578009850372036963)
        ·
          refine ⟨59430662367014775558055445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39620441578009850372036963 59430662367014775558055445)
          ·
            refine ⟨2785812298453817604283849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59430662367014775558055445 2785812298453817604283849)
            ·
              refine ⟨2089359223840363203212887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785812298453817604283849 2089359223840363203212887)
              ·
                refine ⟨3134038835760544804819331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089359223840363203212887 3134038835760544804819331)
                ·
                  refine ⟨4701058253640817207228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134038835760544804819331 4701058253640817207228997)
                  ·
                    refine ⟨881448422557653226355437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701058253640817207228997 881448422557653226355437)
                    ·
                      rfl

theorem cell22_2574922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2574922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574922 prefixEnd_2574922 := by exact prefixLift 2574922
  have htrace : WordTrace (prefixWord ++ tailWord_2574922) baseStart_2574922 baseEnd_2574922 := by
    simpa [prefixWord, tailWord_2574922, baseEnd_2574922] using wordTrace_append hprefix tailTrace_2574922
  have hstable : (prefixWord ++ tailWord_2574922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574922).length < 2 ^ (prefixWord ++ tailWord_2574922).sum := by decide
  have hdescent : baseEnd_2574922 < baseStart_2574922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574933 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2574933 : Nat := 118140960795 + 2574933 * 2 ^ 59
def prefixEnd_2574933 : Nat := 4983230072969 + 3 ^ 40 * 2574933 * 2
def baseEnd_2574933 : Nat := 881452188082452864330403

theorem tailTrace_2574933 : CollatzResearch.WordTrace tailWord_2574933 prefixEnd_2574933 881452188082452864330403 := by
  unfold tailWord_2574933
  simp only [CollatzResearch.WordTrace]
  refine ⟨93915521980464979390145453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62610347986976652926763635 93915521980464979390145453)
  ·
    refine ⟨35218320742674367271304545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93915521980464979390145453 35218320742674367271304545)
    ·
      refine ⟨26413740557005775453478409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35218320742674367271304545 26413740557005775453478409)
      ·
        refine ⟨19810305417754331590108807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26413740557005775453478409 19810305417754331590108807)
        ·
          refine ⟨29715458126631497385163211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19810305417754331590108807 29715458126631497385163211)
          ·
            refine ⟨44573187189947246077744817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29715458126631497385163211 44573187189947246077744817)
            ·
              refine ⟨33429890392460434558308613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44573187189947246077744817 33429890392460434558308613)
              ·
                refine ⟨6268104448586331479682865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33429890392460434558308613 6268104448586331479682865)
                ·
                  refine ⟨4701078336439748609762149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6268104448586331479682865 4701078336439748609762149)
                  ·
                    refine ⟨881452188082452864330403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701078336439748609762149 881452188082452864330403)
                    ·
                      rfl

theorem cell22_2574933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2574933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574933 prefixEnd_2574933 := by exact prefixLift 2574933
  have htrace : WordTrace (prefixWord ++ tailWord_2574933) baseStart_2574933 baseEnd_2574933 := by
    simpa [prefixWord, tailWord_2574933, baseEnd_2574933] using wordTrace_append hprefix tailTrace_2574933
  have hstable : (prefixWord ++ tailWord_2574933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574933).length < 2 ^ (prefixWord ++ tailWord_2574933).sum := by decide
  have hdescent : baseEnd_2574933 < baseStart_2574933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574952 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2574952 : Nat := 118140960795 + 2574952 * 2 ^ 59
def prefixEnd_2574952 : Nat := 4983230072969 + 3 ^ 40 * 2574952 * 2
def baseEnd_2574952 : Nat := 881458692170743148105345

theorem tailTrace_2574952 : CollatzResearch.WordTrace tailWord_2574952 prefixEnd_2574952 881458692170743148105345 := by
  unfold tailWord_2574952
  simp only [CollatzResearch.WordTrace]
  refine ⟨46958107483698072817543555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62610809978264097090058073 46958107483698072817543555)
  ·
    refine ⟨70437161225547109226315333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46958107483698072817543555 70437161225547109226315333)
    ·
      refine ⟨13206967729790082979934125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70437161225547109226315333 13206967729790082979934125)
      ·
        refine ⟨4952612898671281117475297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13206967729790082979934125 4952612898671281117475297)
        ·
          refine ⟨3714459674003460838106473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952612898671281117475297 3714459674003460838106473)
          ·
            refine ⟨2785844755502595628579855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3714459674003460838106473 2785844755502595628579855)
            ·
              refine ⟨4178767133253893442869783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785844755502595628579855 4178767133253893442869783)
              ·
                refine ⟨6268150699880840164304675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178767133253893442869783 6268150699880840164304675)
                ·
                  refine ⟨9402226049821260246457013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268150699880840164304675 9402226049821260246457013)
                  ·
                    refine ⟨881458692170743148105345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9402226049821260246457013 881458692170743148105345)
                    ·
                      rfl

theorem cell22_2574952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2574952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574952 prefixEnd_2574952 := by exact prefixLift 2574952
  have htrace : WordTrace (prefixWord ++ tailWord_2574952) baseStart_2574952 baseEnd_2574952 := by
    simpa [prefixWord, tailWord_2574952, baseEnd_2574952] using wordTrace_append hprefix tailTrace_2574952
  have hstable : (prefixWord ++ tailWord_2574952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574952).length < 2 ^ (prefixWord ++ tailWord_2574952).sum := by decide
  have hdescent : baseEnd_2574952 < baseStart_2574952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574963 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 5, 3]
def baseStart_2574963 : Nat := 118140960795 + 2574963 * 2 ^ 59
def prefixEnd_2574963 : Nat := 4983230072969 + 3 ^ 40 * 2574963 * 2
def baseEnd_2574963 : Nat := 881462457695542786080311

theorem tailTrace_2574963 : CollatzResearch.WordTrace tailWord_2574963 prefixEnd_2574963 881462457695542786080311 := by
  unfold tailWord_2574963
  simp only [CollatzResearch.WordTrace]
  refine ⟨93916616170356294513737543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62611077446904196342491695 93916616170356294513737543)
  ·
    refine ⟨140874924255534441770606315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93916616170356294513737543 140874924255534441770606315)
    ·
      refine ⟨211312386383301662655909473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140874924255534441770606315 211312386383301662655909473)
      ·
        refine ⟨158484289787476246991932105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211312386383301662655909473 158484289787476246991932105)
        ·
          refine ⟨118863217340607185243949079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158484289787476246991932105 118863217340607185243949079)
          ·
            refine ⟨178294826010910777865923619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118863217340607185243949079 178294826010910777865923619)
            ·
              refine ⟨267442239016366166798885429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178294826010910777865923619 267442239016366166798885429)
              ·
                refine ⟨25072709907784328137395509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267442239016366166798885429 25072709907784328137395509)
                ·
                  refine ⟨2350566553854780762880829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25072709907784328137395509 2350566553854780762880829)
                  ·
                    refine ⟨881462457695542786080311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350566553854780762880829 881462457695542786080311)
                    ·
                      rfl

theorem cell22_2574963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 3].length) (baseStart_2574963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574963 prefixEnd_2574963 := by exact prefixLift 2574963
  have htrace : WordTrace (prefixWord ++ tailWord_2574963) baseStart_2574963 baseEnd_2574963 := by
    simpa [prefixWord, tailWord_2574963, baseEnd_2574963] using wordTrace_append hprefix tailTrace_2574963
  have hstable : (prefixWord ++ tailWord_2574963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574963).length < 2 ^ (prefixWord ++ tailWord_2574963).sum := by decide
  have hdescent : baseEnd_2574963 < baseStart_2574963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2574965 : List Nat := [1, 3, 4, 2, 2, 1, 1, 8]
def baseStart_2574965 : Nat := 118140960795 + 2574965 * 2 ^ 59
def prefixEnd_2574965 : Nat := 4983230072969 + 3 ^ 40 * 2574965 * 2
def baseEnd_2574965 : Nat := 97940349148490605281145

theorem tailTrace_2574965 : CollatzResearch.WordTrace tailWord_2574965 prefixEnd_2574965 97940349148490605281145 := by
  unfold tailWord_2574965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93916689116349048855310349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62611126077566032570206899 93916689116349048855310349)
  ·
    refine ⟨35218758418630893320741381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93916689116349048855310349 35218758418630893320741381)
    ·
      refine ⟨6603517203493292497639009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35218758418630893320741381 6603517203493292497639009)
      ·
        refine ⟨4952637902619969373229257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6603517203493292497639009 4952637902619969373229257)
        ·
          refine ⟨3714478426964977029921943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952637902619969373229257 3714478426964977029921943)
          ·
            refine ⟨5571717640447465544882915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714478426964977029921943 5571717640447465544882915)
            ·
              refine ⟨8357576460671198317324373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5571717640447465544882915 8357576460671198317324373)
              ·
                refine ⟨97940349148490605281145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8357576460671198317324373 97940349148490605281145)
                ·
                  rfl

theorem cell22_2574965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 8].length) (baseStart_2574965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2574965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2574965 prefixEnd_2574965 := by exact prefixLift 2574965
  have htrace : WordTrace (prefixWord ++ tailWord_2574965) baseStart_2574965 baseEnd_2574965 := by
    simpa [prefixWord, tailWord_2574965, baseEnd_2574965] using wordTrace_append hprefix tailTrace_2574965
  have hstable : (prefixWord ++ tailWord_2574965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2574965).length < 2 ^ (prefixWord ++ tailWord_2574965).sum := by decide
  have hdescent : baseEnd_2574965 < baseStart_2574965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2574965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575085 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2575085 : Nat := 118140960795 + 2575085 * 2 ^ 59
def prefixEnd_2575085 : Nat := 4983230072969 + 3 ^ 40 * 2575085 * 2
def baseEnd_2575085 : Nat := 881504220788775134529937

theorem tailTrace_2575085 : CollatzResearch.WordTrace tailWord_2575085 prefixEnd_2575085 881504220788775134529937 := by
  unfold tailWord_2575085
  simp only [CollatzResearch.WordTrace]
  refine ⟨93921065875914309349678709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62614043917276206233119139 93921065875914309349678709)
  ·
    refine ⟨8805099925866966501532379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93921065875914309349678709 8805099925866966501532379)
    ·
      refine ⟨13207649888800449752298569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8805099925866966501532379 13207649888800449752298569)
      ·
        refine ⟨9905737416600337314223927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13207649888800449752298569 9905737416600337314223927)
        ·
          refine ⟨14858606124900505971335891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905737416600337314223927 14858606124900505971335891)
          ·
            refine ⟨22287909187350758957003837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14858606124900505971335891 22287909187350758957003837)
            ·
              refine ⟨8357965945256534608876439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22287909187350758957003837 8357965945256534608876439)
              ·
                refine ⟨12536948917884801913314659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8357965945256534608876439 12536948917884801913314659)
                ·
                  refine ⟨18805423376827202869971989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12536948917884801913314659 18805423376827202869971989)
                  ·
                    refine ⟨881504220788775134529937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18805423376827202869971989 881504220788775134529937)
                    ·
                      rfl

theorem cell22_2575085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2575085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575085 prefixEnd_2575085 := by exact prefixLift 2575085
  have htrace : WordTrace (prefixWord ++ tailWord_2575085) baseStart_2575085 baseEnd_2575085 := by
    simpa [prefixWord, tailWord_2575085, baseEnd_2575085] using wordTrace_append hprefix tailTrace_2575085
  have hstable : (prefixWord ++ tailWord_2575085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575085).length < 2 ^ (prefixWord ++ tailWord_2575085).sum := by decide
  have hdescent : baseEnd_2575085 < baseStart_2575085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575113 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2575113 : Nat := 118140960795 + 2575113 * 2 ^ 59
def prefixEnd_2575113 : Nat := 4983230072969 + 3 ^ 40 * 2575113 * 2
def baseEnd_2575113 : Nat := 881513805760992394829851

theorem tailTrace_2575113 : CollatzResearch.WordTrace tailWord_2575113 prefixEnd_2575113 881513805760992394829851 := by
  unfold tailWord_2575113
  simp only [CollatzResearch.WordTrace]
  refine ⟨93922087119812870131697993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62614724746541913421131995 93922087119812870131697993)
  ·
    refine ⟨70441565339859652598773495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93922087119812870131697993 70441565339859652598773495)
    ·
      refine ⟨105662348009789478898160243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70441565339859652598773495 105662348009789478898160243)
      ·
        refine ⟨158493522014684218347240365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105662348009789478898160243 158493522014684218347240365)
        ·
          refine ⟨59435070755506581880215137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158493522014684218347240365 59435070755506581880215137)
          ·
            refine ⟨44576303066629936410161353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59435070755506581880215137 44576303066629936410161353)
            ·
              refine ⟨33432227299972452307621015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44576303066629936410161353 33432227299972452307621015)
              ·
                refine ⟨50148340949958678461431523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33432227299972452307621015 50148340949958678461431523)
                ·
                  refine ⟨75222511424938017692147285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50148340949958678461431523 75222511424938017692147285)
                  ·
                    refine ⟨881513805760992394829851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75222511424938017692147285 881513805760992394829851)
                    ·
                      rfl

theorem cell22_2575113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2575113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575113 prefixEnd_2575113 := by exact prefixLift 2575113
  have htrace : WordTrace (prefixWord ++ tailWord_2575113) baseStart_2575113 baseEnd_2575113 := by
    simpa [prefixWord, tailWord_2575113, baseEnd_2575113] using wordTrace_append hprefix tailTrace_2575113
  have hstable : (prefixWord ++ tailWord_2575113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575113).length < 2 ^ (prefixWord ++ tailWord_2575113).sum := by decide
  have hdescent : baseEnd_2575113 < baseStart_2575113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575132 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2575132 : Nat := 118140960795 + 2575132 * 2 ^ 59
def prefixEnd_2575132 : Nat := 4983230072969 + 3 ^ 40 * 2575132 * 2
def baseEnd_2575132 : Nat := 881520309849282678604793

theorem tailTrace_2575132 : CollatzResearch.WordTrace tailWord_2575132 prefixEnd_2575132 881520309849282678604793 := by
  unfold tailWord_2575132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46961390053372018188319825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62615186737829357584426433 46961390053372018188319825)
  ·
    refine ⟨35221042540029013641239869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46961390053372018188319825 35221042540029013641239869)
    ·
      refine ⟨13207890952510880115464951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35221042540029013641239869 13207890952510880115464951)
      ·
        refine ⟨19811836428766320173197427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13207890952510880115464951 19811836428766320173197427)
        ·
          refine ⟨29717754643149480259796141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19811836428766320173197427 29717754643149480259796141)
          ·
            refine ⟨11144157991181055097423553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29717754643149480259796141 11144157991181055097423553)
            ·
              refine ⟨8358118493385791323067665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11144157991181055097423553 8358118493385791323067665)
              ·
                refine ⟨6268588870039343492300749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8358118493385791323067665 6268588870039343492300749)
                ·
                  refine ⟨2350720826264753809612781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6268588870039343492300749 2350720826264753809612781)
                  ·
                    refine ⟨881520309849282678604793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350720826264753809612781 881520309849282678604793)
                    ·
                      rfl

theorem cell22_2575132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2575132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575132 prefixEnd_2575132 := by exact prefixLift 2575132
  have htrace : WordTrace (prefixWord ++ tailWord_2575132) baseStart_2575132 baseEnd_2575132 := by
    simpa [prefixWord, tailWord_2575132, baseEnd_2575132] using wordTrace_append hprefix tailTrace_2575132
  have hstable : (prefixWord ++ tailWord_2575132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575132).length < 2 ^ (prefixWord ++ tailWord_2575132).sum := by decide
  have hdescent : baseEnd_2575132 < baseStart_2575132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575166 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2575166 : Nat := 118140960795 + 2575166 * 2 ^ 59
def prefixEnd_2575166 : Nat := 4983230072969 + 3 ^ 40 * 2575166 * 2
def baseEnd_2575166 : Nat := 881531948744117923254689

theorem tailTrace_2575166 : CollatzResearch.WordTrace tailWord_2575166 prefixEnd_2575166 881531948744117923254689 := by
  unfold tailWord_2575166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740502523577607522922169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62616013459080573455584901 11740502523577607522922169)
  ·
    refine ⟨8805376892683205642191627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11740502523577607522922169 8805376892683205642191627)
    ·
      refine ⟨13208065339024808463287441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8805376892683205642191627 13208065339024808463287441)
      ·
        refine ⟨9906049004268606347465581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13208065339024808463287441 9906049004268606347465581)
        ·
          refine ⟨3714768376600727380299593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9906049004268606347465581 3714768376600727380299593)
          ·
            refine ⟨2786076282450545535224695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3714768376600727380299593 2786076282450545535224695)
            ·
              refine ⟨4179114423675818302837043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786076282450545535224695 4179114423675818302837043)
              ·
                refine ⟨6268671635513727454255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179114423675818302837043 6268671635513727454255565)
                ·
                  refine ⟨2350751863317647795345837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6268671635513727454255565 2350751863317647795345837)
                  ·
                    refine ⟨881531948744117923254689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350751863317647795345837 881531948744117923254689)
                    ·
                      rfl

theorem cell22_2575166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2575166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575166 prefixEnd_2575166 := by exact prefixLift 2575166
  have htrace : WordTrace (prefixWord ++ tailWord_2575166) baseStart_2575166 baseEnd_2575166 := by
    simpa [prefixWord, tailWord_2575166, baseEnd_2575166] using wordTrace_append hprefix tailTrace_2575166
  have hstable : (prefixWord ++ tailWord_2575166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575166).length < 2 ^ (prefixWord ++ tailWord_2575166).sum := by decide
  have hdescent : baseEnd_2575166 < baseStart_2575166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575175 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2575175 : Nat := 118140960795 + 2575175 * 2 ^ 59
def prefixEnd_2575175 : Nat := 4983230072969 + 3 ^ 40 * 2575175 * 2
def baseEnd_2575175 : Nat := 881535029628044899779661

theorem tailTrace_2575175 : CollatzResearch.WordTrace tailWord_2575175 prefixEnd_2575175 881535029628044899779661 := by
  unfold tailWord_2575175
  simp only [CollatzResearch.WordTrace]
  refine ⟨93924348445588254720454979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62616232297058836480303319 93924348445588254720454979)
  ·
    refine ⟨140886522668382382080682469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93924348445588254720454979 140886522668382382080682469)
    ·
      refine ⟨26416223000321696640127963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140886522668382382080682469 26416223000321696640127963)
      ·
        refine ⟨39624334500482544960191945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26416223000321696640127963 39624334500482544960191945)
        ·
          refine ⟨29718250875361908720143959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39624334500482544960191945 29718250875361908720143959)
          ·
            refine ⟨44577376313042863080215939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29718250875361908720143959 44577376313042863080215939)
            ·
              refine ⟨66866064469564294620323909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44577376313042863080215939 66866064469564294620323909)
              ·
                refine ⟨12537387088043305241310733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66866064469564294620323909 12537387088043305241310733)
                ·
                  refine ⟨4701520158016239465491525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12537387088043305241310733 4701520158016239465491525)
                  ·
                    refine ⟨881535029628044899779661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701520158016239465491525 881535029628044899779661)
                    ·
                      rfl

theorem cell22_2575175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2575175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575175 prefixEnd_2575175 := by exact prefixLift 2575175
  have htrace : WordTrace (prefixWord ++ tailWord_2575175) baseStart_2575175 baseEnd_2575175 := by
    simpa [prefixWord, tailWord_2575175, baseEnd_2575175] using wordTrace_append hprefix tailTrace_2575175
  have hstable : (prefixWord ++ tailWord_2575175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575175).length < 2 ^ (prefixWord ++ tailWord_2575175).sum := by decide
  have hdescent : baseEnd_2575175 < baseStart_2575175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575205 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2575205 : Nat := 118140960795 + 2575205 * 2 ^ 59
def prefixEnd_2575205 : Nat := 4983230072969 + 3 ^ 40 * 2575205 * 2
def baseEnd_2575205 : Nat := 881545299241134821529569

theorem tailTrace_2575205 : CollatzResearch.WordTrace tailWord_2575205 prefixEnd_2575205 881545299241134821529569 := by
  unfold tailWord_2575205
  simp only [CollatzResearch.WordTrace]
  refine ⟨93925442635479569844047069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62616961756986379896031379 93925442635479569844047069)
  ·
    refine ⟨35222040988304838691517651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93925442635479569844047069 35222040988304838691517651)
    ·
      refine ⟨52833061482457258037276477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35222040988304838691517651 52833061482457258037276477)
      ·
        refine ⟨19812398055921471763978679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52833061482457258037276477 19812398055921471763978679)
        ·
          refine ⟨29718597083882207645968019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19812398055921471763978679 29718597083882207645968019)
          ·
            refine ⟨44577895625823311468952029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29718597083882207645968019 44577895625823311468952029)
            ·
              refine ⟨16716710859683741800857011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44577895625823311468952029 16716710859683741800857011)
              ·
                refine ⟨25075066289525612701285517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16716710859683741800857011 25075066289525612701285517)
                ·
                  refine ⟨9403149858572104762982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25075066289525612701285517 9403149858572104762982069)
                  ·
                    refine ⟨881545299241134821529569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9403149858572104762982069 881545299241134821529569)
                    ·
                      rfl

theorem cell22_2575205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2575205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575205 prefixEnd_2575205 := by exact prefixLift 2575205
  have htrace : WordTrace (prefixWord ++ tailWord_2575205) baseStart_2575205 baseEnd_2575205 := by
    simpa [prefixWord, tailWord_2575205, baseEnd_2575205] using wordTrace_append hprefix tailTrace_2575205
  have hstable : (prefixWord ++ tailWord_2575205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575205).length < 2 ^ (prefixWord ++ tailWord_2575205).sum := by decide
  have hdescent : baseEnd_2575205 < baseStart_2575205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575239 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 2, 3]
def baseStart_2575239 : Nat := 118140960795 + 2575239 * 2 ^ 59
def prefixEnd_2575239 : Nat := 4983230072969 + 3 ^ 40 * 2575239 * 2
def baseEnd_2575239 : Nat := 881556938135970066179465

theorem tailTrace_2575239 : CollatzResearch.WordTrace tailWord_2575239 prefixEnd_2575239 881556938135970066179465 := by
  unfold tailWord_2575239
  simp only [CollatzResearch.WordTrace]
  refine ⟨93926682717356393650784771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62617788478237595767189847 93926682717356393650784771)
  ·
    refine ⟨140890024076034590476177157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93926682717356393650784771 140890024076034590476177157)
    ·
      refine ⟨26416879514256485714283217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140890024076034590476177157 26416879514256485714283217)
      ·
        refine ⟨19812659635692364285712413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26416879514256485714283217 19812659635692364285712413)
        ·
          refine ⟨7429747363384636607142155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19812659635692364285712413 7429747363384636607142155)
          ·
            refine ⟨11144621045076954910713233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429747363384636607142155 11144621045076954910713233)
            ·
              refine ⟨8358465783807716183034925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11144621045076954910713233 8358465783807716183034925)
              ·
                refine ⟨3134424668927893568638097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8358465783807716183034925 3134424668927893568638097)
                ·
                  refine ⟨2350818501695920176478573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134424668927893568638097 2350818501695920176478573)
                  ·
                    refine ⟨881556938135970066179465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350818501695920176478573 881556938135970066179465)
                    ·
                      rfl

theorem cell22_2575239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_2575239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575239 prefixEnd_2575239 := by exact prefixLift 2575239
  have htrace : WordTrace (prefixWord ++ tailWord_2575239) baseStart_2575239 baseEnd_2575239 := by
    simpa [prefixWord, tailWord_2575239, baseEnd_2575239] using wordTrace_append hprefix tailTrace_2575239
  have hstable : (prefixWord ++ tailWord_2575239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575239).length < 2 ^ (prefixWord ++ tailWord_2575239).sum := by decide
  have hdescent : baseEnd_2575239 < baseStart_2575239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575295 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2575295 : Nat := 118140960795 + 2575295 * 2 ^ 59
def prefixEnd_2575295 : Nat := 4983230072969 + 3 ^ 40 * 2575295 * 2
def baseEnd_2575295 : Nat := 881576108080404586779293

theorem tailTrace_2575295 : CollatzResearch.WordTrace tailWord_2575295 prefixEnd_2575295 881576108080404586779293 := by
  unfold tailWord_2575295
  simp only [CollatzResearch.WordTrace]
  refine ⟨93928725205153515214823339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62619150136769010143215559 93928725205153515214823339)
  ·
    refine ⟨140893087807730272822235009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93928725205153515214823339 140893087807730272822235009)
    ·
      refine ⟨105669815855797704616676257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140893087807730272822235009 105669815855797704616676257)
      ·
        refine ⟨79252361891848278462507193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105669815855797704616676257 79252361891848278462507193)
        ·
          refine ⟨59439271418886208846880395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79252361891848278462507193 59439271418886208846880395)
          ·
            refine ⟨89158907128329313270320593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59439271418886208846880395 89158907128329313270320593)
            ·
              refine ⟨66869180346246984952740445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89158907128329313270320593 66869180346246984952740445)
              ·
                refine ⟨25075942629842619357277667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66869180346246984952740445 25075942629842619357277667)
                ·
                  refine ⟨37613913944763929035916501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25075942629842619357277667 37613913944763929035916501)
                  ·
                    refine ⟨881576108080404586779293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37613913944763929035916501 881576108080404586779293)
                    ·
                      rfl

theorem cell22_2575295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2575295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575295 prefixEnd_2575295 := by exact prefixLift 2575295
  have htrace : WordTrace (prefixWord ++ tailWord_2575295) baseStart_2575295 baseEnd_2575295 := by
    simpa [prefixWord, tailWord_2575295, baseEnd_2575295] using wordTrace_append hprefix tailTrace_2575295
  have hstable : (prefixWord ++ tailWord_2575295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575295).length < 2 ^ (prefixWord ++ tailWord_2575295).sum := by decide
  have hdescent : baseEnd_2575295 < baseStart_2575295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575357 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2575357 : Nat := 118140960795 + 2575357 * 2 ^ 59
def prefixEnd_2575357 : Nat := 4983230072969 + 3 ^ 40 * 2575357 * 2
def baseEnd_2575357 : Nat := 881597331947457091729103

theorem tailTrace_2575357 : CollatzResearch.WordTrace tailWord_2575357 prefixEnd_2575357 881597331947457091729103 := by
  unfold tailWord_2575357
  simp only [CollatzResearch.WordTrace]
  refine ⟨93930986530928899803580325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62620657687285933202386883 93930986530928899803580325)
  ·
    refine ⟨17612059974549168713171311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93930986530928899803580325 17612059974549168713171311)
    ·
      refine ⟨26418089961823753069756967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17612059974549168713171311 26418089961823753069756967)
      ·
        refine ⟨39627134942735629604635451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26418089961823753069756967 39627134942735629604635451)
        ·
          refine ⟨59440702414103444406953177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39627134942735629604635451 59440702414103444406953177)
          ·
            refine ⟨44580526810577583305214883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59440702414103444406953177 44580526810577583305214883)
            ·
              refine ⟨66870790215866374957822325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44580526810577583305214883 66870790215866374957822325)
              ·
                refine ⟨6269136582737472652295843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66870790215866374957822325 6269136582737472652295843)
                ·
                  refine ⟨9403704874106208978443765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269136582737472652295843 9403704874106208978443765)
                  ·
                    refine ⟨881597331947457091729103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9403704874106208978443765 881597331947457091729103)
                    ·
                      rfl

theorem cell22_2575357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2575357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575357 prefixEnd_2575357 := by exact prefixLift 2575357
  have htrace : WordTrace (prefixWord ++ tailWord_2575357) baseStart_2575357 baseEnd_2575357 := by
    simpa [prefixWord, tailWord_2575357, baseEnd_2575357] using wordTrace_append hprefix tailTrace_2575357
  have hstable : (prefixWord ++ tailWord_2575357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575357).length < 2 ^ (prefixWord ++ tailWord_2575357).sum := by decide
  have hdescent : baseEnd_2575357 < baseStart_2575357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575361 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2575361 : Nat := 118140960795 + 2575361 * 2 ^ 59
def prefixEnd_2575361 : Nat := 4983230072969 + 3 ^ 40 * 2575361 * 2
def baseEnd_2575361 : Nat := 881598701229202414629091

theorem tailTrace_2575361 : CollatzResearch.WordTrace tailWord_2575361 prefixEnd_2575361 881598701229202414629091 := by
  unfold tailWord_2575361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93931132422914408486725937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62620754948609605657817291 93931132422914408486725937)
  ·
    refine ⟨70448349317185806365044453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93931132422914408486725937 70448349317185806365044453)
    ·
      refine ⟨13209065496972338693445835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70448349317185806365044453 13209065496972338693445835)
      ·
        refine ⟨19813598245458508040168753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13209065496972338693445835 19813598245458508040168753)
        ·
          refine ⟨14860198684093881030126565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19813598245458508040168753 14860198684093881030126565)
          ·
            refine ⟨2786287253267602693148731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14860198684093881030126565 2786287253267602693148731)
            ·
              refine ⟨4179430879901404039723097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786287253267602693148731 4179430879901404039723097)
              ·
                refine ⟨3134573159926053029792323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179430879901404039723097 3134573159926053029792323)
                ·
                  refine ⟨4701859739889079544688485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134573159926053029792323 4701859739889079544688485)
                  ·
                    refine ⟨881598701229202414629091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4701859739889079544688485 881598701229202414629091)
                    ·
                      rfl

theorem cell22_2575361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2575361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575361 prefixEnd_2575361 := by exact prefixLift 2575361
  have htrace : WordTrace (prefixWord ++ tailWord_2575361) baseStart_2575361 baseEnd_2575361 := by
    simpa [prefixWord, tailWord_2575361, baseEnd_2575361] using wordTrace_append hprefix tailTrace_2575361
  have hstable : (prefixWord ++ tailWord_2575361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575361).length < 2 ^ (prefixWord ++ tailWord_2575361).sum := by decide
  have hdescent : baseEnd_2575361 < baseStart_2575361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575374 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2575374 : Nat := 118140960795 + 2575374 * 2 ^ 59
def prefixEnd_2575374 : Nat := 4983230072969 + 3 ^ 40 * 2575374 * 2
def baseEnd_2575374 : Nat := 881603151394874714054051

theorem tailTrace_2575374 : CollatzResearch.WordTrace tailWord_2575374 prefixEnd_2575374 881603151394874714054051 := by
  unfold tailWord_2575374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741450821483413963368647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62621071047911541137966117 11741450821483413963368647)
  ·
    refine ⟨17612176232225120945052971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11741450821483413963368647 17612176232225120945052971)
    ·
      refine ⟨26418264348337681417579457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17612176232225120945052971 26418264348337681417579457)
      ·
        refine ⟨19813698261253261063184593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26418264348337681417579457 19813698261253261063184593)
        ·
          refine ⟨14860273695939945797388445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19813698261253261063184593 14860273695939945797388445)
          ·
            refine ⟨5572602635977479674020667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14860273695939945797388445 5572602635977479674020667)
            ·
              refine ⟨8358903953966219511031001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572602635977479674020667 8358903953966219511031001)
              ·
                refine ⟨6269177965474664633273251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8358903953966219511031001 6269177965474664633273251)
                ·
                  refine ⟨9403766948211996949909877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269177965474664633273251 9403766948211996949909877)
                  ·
                    refine ⟨881603151394874714054051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9403766948211996949909877 881603151394874714054051)
                    ·
                      rfl

theorem cell22_2575374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2575374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575374 prefixEnd_2575374 := by exact prefixLift 2575374
  have htrace : WordTrace (prefixWord ++ tailWord_2575374) baseStart_2575374 baseEnd_2575374 := by
    simpa [prefixWord, tailWord_2575374, baseEnd_2575374] using wordTrace_append hprefix tailTrace_2575374
  have hstable : (prefixWord ++ tailWord_2575374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575374).length < 2 ^ (prefixWord ++ tailWord_2575374).sum := by decide
  have hdescent : baseEnd_2575374 < baseStart_2575374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575391 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 2, 3]
def baseStart_2575391 : Nat := 118140960795 + 2575391 * 2 ^ 59
def prefixEnd_2575391 : Nat := 4983230072969 + 3 ^ 40 * 2575391 * 2
def baseEnd_2575391 : Nat := 881608970842292336378999

theorem tailTrace_2575391 : CollatzResearch.WordTrace tailWord_2575391 prefixEnd_2575391 881608970842292336378999 := by
  unfold tailWord_2575391
  simp only [CollatzResearch.WordTrace]
  refine ⟨93932226612805723610318027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62621484408537149073545351 93932226612805723610318027)
  ·
    refine ⟨140898339919208585415477041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93932226612805723610318027 140898339919208585415477041)
    ·
      refine ⟨105673754939406439061607781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140898339919208585415477041 105673754939406439061607781)
      ·
        refine ⟨19813829051138707324051459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105673754939406439061607781 19813829051138707324051459)
        ·
          refine ⟨29720743576708060986077189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19813829051138707324051459 29720743576708060986077189)
          ·
            refine ⟨5572639420632761434889473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29720743576708060986077189 5572639420632761434889473)
            ·
              refine ⟨4179479565474571076167105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572639420632761434889473 4179479565474571076167105)
              ·
                refine ⟨3134609674105928307125329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179479565474571076167105 3134609674105928307125329)
                ·
                  refine ⟨2350957255579446230343997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134609674105928307125329 2350957255579446230343997)
                  ·
                    refine ⟨881608970842292336378999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350957255579446230343997 881608970842292336378999)
                    ·
                      rfl

theorem cell22_2575391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_2575391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575391 prefixEnd_2575391 := by exact prefixLift 2575391
  have htrace : WordTrace (prefixWord ++ tailWord_2575391) baseStart_2575391 baseEnd_2575391 := by
    simpa [prefixWord, tailWord_2575391, baseEnd_2575391] using wordTrace_append hprefix tailTrace_2575391
  have hstable : (prefixWord ++ tailWord_2575391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575391).length < 2 ^ (prefixWord ++ tailWord_2575391).sum := by decide
  have hdescent : baseEnd_2575391 < baseStart_2575391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575393 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 4]
def baseStart_2575393 : Nat := 118140960795 + 2575393 * 2 ^ 59
def prefixEnd_2575393 : Nat := 4983230072969 + 3 ^ 40 * 2575393 * 2
def baseEnd_2575393 : Nat := 293869885161054999276331

theorem tailTrace_2575393 : CollatzResearch.WordTrace tailWord_2575393 prefixEnd_2575393 293869885161054999276331 := by
  unfold tailWord_2575393
  simp only [CollatzResearch.WordTrace]
  refine ⟨93932299558798477951890833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62621533039198985301260555 93932299558798477951890833)
  ·
    refine ⟨70449224669098858463918125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93932299558798477951890833 70449224669098858463918125)
    ·
      refine ⟨26418459250912071923969297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70449224669098858463918125 26418459250912071923969297)
      ·
        refine ⟨19813844438184053942976973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26418459250912071923969297 19813844438184053942976973)
        ·
          refine ⟨7430191664319020228616365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19813844438184053942976973 7430191664319020228616365)
          ·
            refine ⟨2786321874119632585731137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7430191664319020228616365 2786321874119632585731137)
            ·
              refine ⟨2089741405589724439298353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786321874119632585731137 2089741405589724439298353)
              ·
                refine ⟨1567306054192293329473765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089741405589724439298353 1567306054192293329473765)
                ·
                  refine ⟨293869885161054999276331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1567306054192293329473765 293869885161054999276331)
                  ·
                    rfl

theorem cell22_2575393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_2575393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575393 prefixEnd_2575393 := by exact prefixLift 2575393
  have htrace : WordTrace (prefixWord ++ tailWord_2575393) baseStart_2575393 baseEnd_2575393 := by
    simpa [prefixWord, tailWord_2575393, baseEnd_2575393] using wordTrace_append hprefix tailTrace_2575393
  have hstable : (prefixWord ++ tailWord_2575393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575393).length < 2 ^ (prefixWord ++ tailWord_2575393).sum := by decide
  have hdescent : baseEnd_2575393 < baseStart_2575393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575432 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_2575432 : Nat := 118140960795 + 2575432 * 2 ^ 59
def prefixEnd_2575432 : Nat := 4983230072969 + 3 ^ 40 * 2575432 * 2
def baseEnd_2575432 : Nat := 293874335326727298701291

theorem tailTrace_2575432 : CollatzResearch.WordTrace tailWord_2575432 prefixEnd_2575432 293874335326727298701291 := by
  unfold tailWord_2575432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46966861002828593806280275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62622481337104791741707033 46966861002828593806280275)
  ·
    refine ⟨70450291504242890709420413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46966861002828593806280275 70450291504242890709420413)
    ·
      refine ⟨26418859314091084016032655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70450291504242890709420413 26418859314091084016032655)
      ·
        refine ⟨39628288971136626024048983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26418859314091084016032655 39628288971136626024048983)
        ·
          refine ⟨59442433456704939036073475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39628288971136626024048983 59442433456704939036073475)
          ·
            refine ⟨89163650185057408554110213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59442433456704939036073475 89163650185057408554110213)
            ·
              refine ⟨16718184409698264103895665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89163650185057408554110213 16718184409698264103895665)
              ·
                refine ⟨12538638307273698077921749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16718184409698264103895665 12538638307273698077921749)
                ·
                  refine ⟨293874335326727298701291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12538638307273698077921749 293874335326727298701291)
                  ·
                    rfl

theorem cell22_2575432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_2575432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575432 prefixEnd_2575432 := by exact prefixLift 2575432
  have htrace : WordTrace (prefixWord ++ tailWord_2575432) baseStart_2575432 baseEnd_2575432 := by
    simpa [prefixWord, tailWord_2575432, baseEnd_2575432] using wordTrace_append hprefix tailTrace_2575432
  have hstable : (prefixWord ++ tailWord_2575432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575432).length < 2 ^ (prefixWord ++ tailWord_2575432).sum := by decide
  have hdescent : baseEnd_2575432 < baseStart_2575432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575511 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 6]
def baseStart_2575511 : Nat := 118140960795 + 2575511 * 2 ^ 59
def prefixEnd_2575511 : Nat := 4983230072969 + 3 ^ 40 * 2575511 * 2
def baseEnd_2575511 : Nat := 293883349764884007792877

theorem tailTrace_2575511 : CollatzResearch.WordTrace tailWord_2575511 prefixEnd_2575511 293883349764884007792877 := by
  unfold tailWord_2575511
  simp only [CollatzResearch.WordTrace]
  refine ⟨93936603372370984104686387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62624402248247322736457591 93936603372370984104686387)
  ·
    refine ⟨140904905058556476157029581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93936603372370984104686387 140904905058556476157029581)
    ·
      refine ⟨52839339396958678558886093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140904905058556476157029581 52839339396958678558886093)
      ·
        refine ⟨19814752273859504459582285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52839339396958678558886093 19814752273859504459582285)
        ·
          refine ⟨7430532102697314172343357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19814752273859504459582285 7430532102697314172343357)
          ·
            refine ⟨2786449538511492814628759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7430532102697314172343357 2786449538511492814628759)
            ·
              refine ⟨4179674307767239221943139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786449538511492814628759 4179674307767239221943139)
              ·
                refine ⟨6269511461650858832914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179674307767239221943139 6269511461650858832914709)
                ·
                  refine ⟨293883349764884007792877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6269511461650858832914709 293883349764884007792877)
                  ·
                    rfl

theorem cell22_2575511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].length) (baseStart_2575511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575511 prefixEnd_2575511 := by exact prefixLift 2575511
  have htrace : WordTrace (prefixWord ++ tailWord_2575511) baseStart_2575511 baseEnd_2575511 := by
    simpa [prefixWord, tailWord_2575511, baseEnd_2575511] using wordTrace_append hprefix tailTrace_2575511
  have hstable : (prefixWord ++ tailWord_2575511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575511).length < 2 ^ (prefixWord ++ tailWord_2575511).sum := by decide
  have hdescent : baseEnd_2575511 < baseStart_2575511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575530 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2575530 : Nat := 118140960795 + 2575530 * 2 ^ 59
def prefixEnd_2575530 : Nat := 4983230072969 + 3 ^ 40 * 2575530 * 2
def baseEnd_2575530 : Nat := 881656553382942307153573

theorem tailTrace_2575530 : CollatzResearch.WordTrace tailWord_2575530 prefixEnd_2575530 881656553382942307153573 := by
  unfold tailWord_2575530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23484324089825537587407011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62624864239534766899752029 23484324089825537587407011)
  ·
    refine ⟨35226486134738306381110517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23484324089825537587407011 35226486134738306381110517)
    ·
      refine ⟨3302483075131716223229111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35226486134738306381110517 3302483075131716223229111)
      ·
        refine ⟨4953724612697574334843667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302483075131716223229111 4953724612697574334843667)
        ·
          refine ⟨7430586919046361502265501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953724612697574334843667 7430586919046361502265501)
          ·
            refine ⟨2786470094642385563349563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7430586919046361502265501 2786470094642385563349563)
            ·
              refine ⟨4179705141963578345024345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786470094642385563349563 4179705141963578345024345)
              ·
                refine ⟨3134778856472683758768259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179705141963578345024345 3134778856472683758768259)
                ·
                  refine ⟨4702168284709025638152389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134778856472683758768259 4702168284709025638152389)
                  ·
                    refine ⟨881656553382942307153573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702168284709025638152389 881656553382942307153573)
                    ·
                      rfl

theorem cell22_2575530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2575530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575530 prefixEnd_2575530 := by exact prefixLift 2575530
  have htrace : WordTrace (prefixWord ++ tailWord_2575530) baseStart_2575530 baseEnd_2575530 := by
    simpa [prefixWord, tailWord_2575530, baseEnd_2575530] using wordTrace_append hprefix tailTrace_2575530
  have hstable : (prefixWord ++ tailWord_2575530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575530).length < 2 ^ (prefixWord ++ tailWord_2575530).sum := by decide
  have hdescent : baseEnd_2575530 < baseStart_2575530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575556 : List Nat := [2, 3, 3, 1, 4, 9]
def baseStart_2575556 : Nat := 118140960795 + 2575556 * 2 ^ 59
def prefixEnd_2575556 : Nat := 4983230072969 + 3 ^ 40 * 2575556 * 2
def baseEnd_2575556 : Nat := 10884758687830702543253

theorem tailTrace_2575556 : CollatzResearch.WordTrace tailWord_2575556 prefixEnd_2575556 10884758687830702543253 := by
  unfold tailWord_2575556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46969122328603978395037261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62625496438138637860049681 46969122328603978395037261)
  ·
    refine ⟨17613420873226491898138973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46969122328603978395037261 17613420873226491898138973)
    ·
      refine ⟨6605032827459934461802115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17613420873226491898138973 6605032827459934461802115)
      ·
        refine ⟨9907549241189901692703173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605032827459934461802115 9907549241189901692703173)
        ·
          refine ⟨1857665482723106567381845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9907549241189901692703173 1857665482723106567381845)
          ·
            refine ⟨10884758687830702543253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1857665482723106567381845 10884758687830702543253)
            ·
              rfl

theorem cell22_2575556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 9].length) (baseStart_2575556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575556 prefixEnd_2575556 := by exact prefixLift 2575556
  have htrace : WordTrace (prefixWord ++ tailWord_2575556) baseStart_2575556 baseEnd_2575556 := by
    simpa [prefixWord, tailWord_2575556, baseEnd_2575556] using wordTrace_append hprefix tailTrace_2575556
  have hstable : (prefixWord ++ tailWord_2575556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575556).length < 2 ^ (prefixWord ++ tailWord_2575556).sum := by decide
  have hdescent : baseEnd_2575556 < baseStart_2575556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575618 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2575618 : Nat := 118140960795 + 2575618 * 2 ^ 59
def prefixEnd_2575618 : Nat := 4983230072969 + 3 ^ 40 * 2575618 * 2
def baseEnd_2575618 : Nat := 293895559193779803651101

theorem tailTrace_2575618 : CollatzResearch.WordTrace tailWord_2575618 prefixEnd_2575618 293895559193779803651101 := by
  unfold tailWord_2575618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23485126495745835344707877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62627003988655560919221005 23485126495745835344707877)
  ·
    refine ⟨4403461217952344127132727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23485126495745835344707877 4403461217952344127132727)
    ·
      refine ⟨6605191826928516190699091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403461217952344127132727 6605191826928516190699091)
      ·
        refine ⟨9907787740392774286048637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605191826928516190699091 9907787740392774286048637)
        ·
          refine ⟨3715420402647290357268239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9907787740392774286048637 3715420402647290357268239)
          ·
            refine ⟨5573130603970935535902359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715420402647290357268239 5573130603970935535902359)
            ·
              refine ⟨8359695905956403303853539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573130603970935535902359 8359695905956403303853539)
              ·
                refine ⟨12539543858934604955780309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359695905956403303853539 12539543858934604955780309)
                ·
                  refine ⟨293895559193779803651101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12539543858934604955780309 293895559193779803651101)
                  ·
                    rfl

theorem cell22_2575618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2575618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575618 prefixEnd_2575618 := by exact prefixLift 2575618
  have htrace : WordTrace (prefixWord ++ tailWord_2575618) baseStart_2575618 baseEnd_2575618 := by
    simpa [prefixWord, tailWord_2575618, baseEnd_2575618] using wordTrace_append hprefix tailTrace_2575618
  have hstable : (prefixWord ++ tailWord_2575618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575618).length < 2 ^ (prefixWord ++ tailWord_2575618).sum := by decide
  have hdescent : baseEnd_2575618 < baseStart_2575618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575676 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_2575676 : Nat := 118140960795 + 2575676 * 2 ^ 59
def prefixEnd_2575676 : Nat := 4983230072969 + 3 ^ 40 * 2575676 * 2
def baseEnd_2575676 : Nat := 881706532166646593003125

theorem tailTrace_2575676 : CollatzResearch.WordTrace tailWord_2575676 prefixEnd_2575676 881706532166646593003125 := by
  unfold tailWord_2575676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46971310708386608642221441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62628414277848811522961921 46971310708386608642221441)
  ·
    refine ⟨35228483031289956481666081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46971310708386608642221441 35228483031289956481666081)
    ·
      refine ⟨26421362273467467361249561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35228483031289956481666081 26421362273467467361249561)
      ·
        refine ⟨19816021705100600520937171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26421362273467467361249561 19816021705100600520937171)
        ·
          refine ⟨29724032557650900781405757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19816021705100600520937171 29724032557650900781405757)
          ·
            refine ⟨11146512209119087793027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29724032557650900781405757 11146512209119087793027159)
            ·
              refine ⟨16719768313678631689540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11146512209119087793027159 16719768313678631689540739)
              ·
                refine ⟨25079652470517947534311109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16719768313678631689540739 25079652470517947534311109)
                ·
                  refine ⟨4702434838222115162683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25079652470517947534311109 4702434838222115162683333)
                  ·
                    refine ⟨881706532166646593003125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702434838222115162683333 881706532166646593003125)
                    ·
                      rfl

theorem cell22_2575676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_2575676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575676 prefixEnd_2575676 := by exact prefixLift 2575676
  have htrace : WordTrace (prefixWord ++ tailWord_2575676) baseStart_2575676 baseEnd_2575676 := by
    simpa [prefixWord, tailWord_2575676, baseEnd_2575676] using wordTrace_append hprefix tailTrace_2575676
  have hstable : (prefixWord ++ tailWord_2575676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575676).length < 2 ^ (prefixWord ++ tailWord_2575676).sum := by decide
  have hdescent : baseEnd_2575676 < baseStart_2575676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575678 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2575678 : Nat := 118140960795 + 2575678 * 2 ^ 59
def prefixEnd_2575678 : Nat := 4983230072969 + 3 ^ 40 * 2575678 * 2
def baseEnd_2575678 : Nat := 881707216807519254453119

theorem tailTrace_2575678 : CollatzResearch.WordTrace tailWord_2575678 prefixEnd_2575678 881707216807519254453119 := by
  unfold tailWord_2575678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742836795345746453251961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62628462908510647750677125 11742836795345746453251961)
  ·
    refine ⟨8807127596509309839938971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11742836795345746453251961 8807127596509309839938971)
    ·
      refine ⟨13210691394763964759908457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807127596509309839938971 13210691394763964759908457)
      ·
        refine ⟨9908018546072973569931343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13210691394763964759908457 9908018546072973569931343)
        ·
          refine ⟨14862027819109460354897015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908018546072973569931343 14862027819109460354897015)
          ·
            refine ⟨22293041728664190532345523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14862027819109460354897015 22293041728664190532345523)
            ·
              refine ⟨33439562592996285798518285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22293041728664190532345523 33439562592996285798518285)
              ·
                refine ⟨12539835972373607174444357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33439562592996285798518285 12539835972373607174444357)
                ·
                  refine ⟨2351219244820051345208317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12539835972373607174444357 2351219244820051345208317)
                  ·
                    refine ⟨881707216807519254453119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351219244820051345208317 881707216807519254453119)
                    ·
                      rfl

theorem cell22_2575678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2575678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575678 prefixEnd_2575678 := by exact prefixLift 2575678
  have htrace : WordTrace (prefixWord ++ tailWord_2575678) baseStart_2575678 baseEnd_2575678 := by
    simpa [prefixWord, tailWord_2575678, baseEnd_2575678] using wordTrace_append hprefix tailTrace_2575678
  have hstable : (prefixWord ++ tailWord_2575678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575678).length < 2 ^ (prefixWord ++ tailWord_2575678).sum := by decide
  have hdescent : baseEnd_2575678 < baseStart_2575678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575686 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2575686 : Nat := 118140960795 + 2575686 * 2 ^ 59
def prefixEnd_2575686 : Nat := 4983230072969 + 3 ^ 40 * 2575686 * 2
def baseEnd_2575686 : Nat := 293903318457003300084365

theorem tailTrace_2575686 : CollatzResearch.WordTrace tailWord_2575686 prefixEnd_2575686 293903318457003300084365 := by
  unfold tailWord_2575686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935718317085530906009591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62628657431157992661537941 2935718317085530906009591)
  ·
    refine ⟨4403577475628296359014387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935718317085530906009591 4403577475628296359014387)
    ·
      refine ⟨6605366213442444538521581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403577475628296359014387 6605366213442444538521581)
      ·
        refine ⟨2477012330040916701945593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6605366213442444538521581 2477012330040916701945593)
        ·
          refine ⟨1857759247530687526459195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2477012330040916701945593 1857759247530687526459195)
          ·
            refine ⟨2786638871296031289688793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857759247530687526459195 2786638871296031289688793)
            ·
              refine ⟨2089979153472023467266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786638871296031289688793 2089979153472023467266595)
              ·
                refine ⟨3134968730208035200899893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089979153472023467266595 3134968730208035200899893)
                ·
                  refine ⟨293903318457003300084365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3134968730208035200899893 293903318457003300084365)
                  ·
                    rfl

theorem cell22_2575686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2575686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575686 prefixEnd_2575686 := by exact prefixLift 2575686
  have htrace : WordTrace (prefixWord ++ tailWord_2575686) baseStart_2575686 baseEnd_2575686 := by
    simpa [prefixWord, tailWord_2575686, baseEnd_2575686] using wordTrace_append hprefix tailTrace_2575686
  have hstable : (prefixWord ++ tailWord_2575686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575686).length < 2 ^ (prefixWord ++ tailWord_2575686).sum := by decide
  have hdescent : baseEnd_2575686 < baseStart_2575686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575740 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2575740 : Nat := 118140960795 + 2575740 * 2 ^ 59
def prefixEnd_2575740 : Nat := 4983230072969 + 3 ^ 40 * 2575740 * 2
def baseEnd_2575740 : Nat := 881728440674571759402929

theorem tailTrace_2575740 : CollatzResearch.WordTrace tailWord_2575740 prefixEnd_2575740 881728440674571759402929 := by
  unfold tailWord_2575740
  simp only [CollatzResearch.WordTrace]
  refine ⟨46972477844270678107386337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62629970459027570809848449 46972477844270678107386337)
  ·
    refine ⟨35229358383203008580539753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46972477844270678107386337 35229358383203008580539753)
    ·
      refine ⟨26422018787402256435404815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35229358383203008580539753 26422018787402256435404815)
      ·
        refine ⟨39633028181103384653107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26422018787402256435404815 39633028181103384653107223)
        ·
          refine ⟨59449542271655076979660835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39633028181103384653107223 59449542271655076979660835)
          ·
            refine ⟨89174313407482615469491253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59449542271655076979660835 89174313407482615469491253)
            ·
              refine ⟨8360091881951495200264805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89174313407482615469491253 8360091881951495200264805)
              ·
                refine ⟨1567517227865905350049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8360091881951495200264805 1567517227865905350049651)
                ·
                  refine ⟨2351275841798858025074477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567517227865905350049651 2351275841798858025074477)
                  ·
                    refine ⟨881728440674571759402929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351275841798858025074477 881728440674571759402929)
                    ·
                      rfl

theorem cell22_2575740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2575740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575740 prefixEnd_2575740 := by exact prefixLift 2575740
  have htrace : WordTrace (prefixWord ++ tailWord_2575740) baseStart_2575740 baseEnd_2575740 := by
    simpa [prefixWord, tailWord_2575740, baseEnd_2575740] using wordTrace_append hprefix tailTrace_2575740
  have hstable : (prefixWord ++ tailWord_2575740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575740).length < 2 ^ (prefixWord ++ tailWord_2575740).sum := by decide
  have hdescent : baseEnd_2575740 < baseStart_2575740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575742 : List Nat := [4, 2, 3, 2, 1, 2, 1, 7]
def baseStart_2575742 : Nat := 118140960795 + 2575742 * 2 ^ 59
def prefixEnd_2575742 : Nat := 4983230072969 + 3 ^ 40 * 2575742 * 2
def baseEnd_2575742 : Nat := 97969902812827157872547

theorem tailTrace_2575742 : CollatzResearch.WordTrace tailWord_2575742 prefixEnd_2575742 97969902812827157872547 := by
  unfold tailWord_2575742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743128579316763819543185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62630019089689407037563653 11743128579316763819543185)
  ·
    refine ⟨8807346434487572864657389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11743128579316763819543185 8807346434487572864657389)
    ·
      refine ⟨3302754912932839824246521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8807346434487572864657389 3302754912932839824246521)
      ·
        refine ⟨2477066184699629868184891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302754912932839824246521 2477066184699629868184891)
        ·
          refine ⟨3715599277049444802277337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477066184699629868184891 3715599277049444802277337)
          ·
            refine ⟨2786699457787083601708003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3715599277049444802277337 2786699457787083601708003)
            ·
              refine ⟨4180049186680625402562005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786699457787083601708003 4180049186680625402562005)
              ·
                refine ⟨97969902812827157872547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4180049186680625402562005 97969902812827157872547)
                ·
                  rfl

theorem cell22_2575742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_2575742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575742 prefixEnd_2575742 := by exact prefixLift 2575742
  have htrace : WordTrace (prefixWord ++ tailWord_2575742) baseStart_2575742 baseEnd_2575742 := by
    simpa [prefixWord, tailWord_2575742, baseEnd_2575742] using wordTrace_append hprefix tailTrace_2575742
  have hstable : (prefixWord ++ tailWord_2575742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575742).length < 2 ^ (prefixWord ++ tailWord_2575742).sum := by decide
  have hdescent : baseEnd_2575742 < baseStart_2575742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575751 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2575751 : Nat := 118140960795 + 2575751 * 2 ^ 59
def prefixEnd_2575751 : Nat := 4983230072969 + 3 ^ 40 * 2575751 * 2
def baseEnd_2575751 : Nat := 881732206199371397377895

theorem tailTrace_2575751 : CollatzResearch.WordTrace tailWord_2575751 prefixEnd_2575751 881732206199371397377895 := by
  unfold tailWord_2575751
  simp only [CollatzResearch.WordTrace]
  refine ⟨93945356891501505093423107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62630237927667670062282071 93945356891501505093423107)
  ·
    refine ⟨140918035337252257640134661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93945356891501505093423107 140918035337252257640134661)
    ·
      refine ⟨26422131625734798307525249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140918035337252257640134661 26422131625734798307525249)
      ·
        refine ⟨19816598719301098730643937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26422131625734798307525249 19816598719301098730643937)
        ·
          refine ⟨14862449039475824047982953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19816598719301098730643937 14862449039475824047982953)
          ·
            refine ⟨11146836779606868035987215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14862449039475824047982953 11146836779606868035987215)
            ·
              refine ⟨16720255169410302053980823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11146836779606868035987215 16720255169410302053980823)
              ·
                refine ⟨25080382754115453080971235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16720255169410302053980823 25080382754115453080971235)
                ·
                  refine ⟨37620574131173179621456853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25080382754115453080971235 37620574131173179621456853)
                  ·
                    refine ⟨881732206199371397377895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37620574131173179621456853 881732206199371397377895)
                    ·
                      rfl

theorem cell22_2575751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2575751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575751 prefixEnd_2575751 := by exact prefixLift 2575751
  have htrace : WordTrace (prefixWord ++ tailWord_2575751) baseStart_2575751 baseEnd_2575751 := by
    simpa [prefixWord, tailWord_2575751, baseEnd_2575751] using wordTrace_append hprefix tailTrace_2575751
  have hstable : (prefixWord ++ tailWord_2575751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575751).length < 2 ^ (prefixWord ++ tailWord_2575751).sum := by decide
  have hdescent : baseEnd_2575751 < baseStart_2575751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575811 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_2575811 : Nat := 118140960795 + 2575811 * 2 ^ 59
def prefixEnd_2575811 : Nat := 4983230072969 + 3 ^ 40 * 2575811 * 2
def baseEnd_2575811 : Nat := 881752745425551240877711

theorem tailTrace_2575811 : CollatzResearch.WordTrace tailWord_2575811 prefixEnd_2575811 881752745425551240877711 := by
  unfold tailWord_2575811
  simp only [CollatzResearch.WordTrace]
  refine ⟨93947545271284135340607287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62631696847522756893738191 93947545271284135340607287)
  ·
    refine ⟨140921317906926203010910931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93947545271284135340607287 140921317906926203010910931)
    ·
      refine ⟨211381976860389304516366397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140921317906926203010910931 211381976860389304516366397)
      ·
        refine ⟨79268241322645989193637399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211381976860389304516366397 79268241322645989193637399)
        ·
          refine ⟨118902361983968983790456099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79268241322645989193637399 118902361983968983790456099)
          ·
            refine ⟨178353542975953475685684149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118902361983968983790456099 178353542975953475685684149)
            ·
              refine ⟨16720644653995638345532889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178353542975953475685684149 16720644653995638345532889)
              ·
                refine ⟨12540483490496728759149667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16720644653995638345532889 12540483490496728759149667)
                ·
                  refine ⟨18810725235745093138724501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12540483490496728759149667 18810725235745093138724501)
                  ·
                    refine ⟨881752745425551240877711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18810725235745093138724501 881752745425551240877711)
                    ·
                      rfl

theorem cell22_2575811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_2575811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575811 prefixEnd_2575811 := by exact prefixLift 2575811
  have htrace : WordTrace (prefixWord ++ tailWord_2575811) baseStart_2575811 baseEnd_2575811 := by
    simpa [prefixWord, tailWord_2575811, baseEnd_2575811] using wordTrace_append hprefix tailTrace_2575811
  have hstable : (prefixWord ++ tailWord_2575811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575811).length < 2 ^ (prefixWord ++ tailWord_2575811).sum := by decide
  have hdescent : baseEnd_2575811 < baseStart_2575811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575843 : List Nat := [1, 1, 1, 6, 2, 3, 8]
def baseStart_2575843 : Nat := 118140960795 + 2575843 * 2 ^ 59
def prefixEnd_2575843 : Nat := 4983230072969 + 3 ^ 40 * 2575843 * 2
def baseEnd_2575843 : Nat := 32657914802944956447319

theorem tailTrace_2575843 : CollatzResearch.WordTrace tailWord_2575843 prefixEnd_2575843 32657914802944956447319 := by
  unfold tailWord_2575843
  simp only [CollatzResearch.WordTrace]
  refine ⟨93948712407168204805772183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62632474938112136537181455 93948712407168204805772183)
  ·
    refine ⟨140923068610752307208658275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93948712407168204805772183 140923068610752307208658275)
    ·
      refine ⟨211384602916128460812987413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140923068610752307208658275 211384602916128460812987413)
      ·
        refine ⟨9908653261693521600608785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211384602916128460812987413 9908653261693521600608785)
        ·
          refine ⟨7431489946270141200456589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9908653261693521600608785 7431489946270141200456589)
          ·
            refine ⟨2786808729851302950171221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7431489946270141200456589 2786808729851302950171221)
            ·
              refine ⟨32657914802944956447319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2786808729851302950171221 32657914802944956447319)
              ·
                rfl

theorem cell22_2575843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 8].length) (baseStart_2575843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575843 prefixEnd_2575843 := by exact prefixLift 2575843
  have htrace : WordTrace (prefixWord ++ tailWord_2575843) baseStart_2575843 baseEnd_2575843 := by
    simpa [prefixWord, tailWord_2575843, baseEnd_2575843] using wordTrace_append hprefix tailTrace_2575843
  have hstable : (prefixWord ++ tailWord_2575843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575843).length < 2 ^ (prefixWord ++ tailWord_2575843).sum := by decide
  have hdescent : baseEnd_2575843 < baseStart_2575843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575845 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2575845 : Nat := 118140960795 + 2575845 * 2 ^ 59
def prefixEnd_2575845 : Nat := 4983230072969 + 3 ^ 40 * 2575845 * 2
def baseEnd_2575845 : Nat := 881764384320386485527607

theorem tailTrace_2575845 : CollatzResearch.WordTrace tailWord_2575845 prefixEnd_2575845 881764384320386485527607 := by
  unfold tailWord_2575845
  simp only [CollatzResearch.WordTrace]
  refine ⟨93948785353160959147344989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62632523568773972764896659 93948785353160959147344989)
  ·
    refine ⟨35230794507435359680254371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93948785353160959147344989 35230794507435359680254371)
    ·
      refine ⟨52846191761153039520381557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35230794507435359680254371 52846191761153039520381557)
      ·
        refine ⟨4954330477608097455035771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52846191761153039520381557 4954330477608097455035771)
        ·
          refine ⟨7431495716412146182553657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954330477608097455035771 7431495716412146182553657)
          ·
            refine ⟨5573621787309109636915243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7431495716412146182553657 5573621787309109636915243)
            ·
              refine ⟨8360432680963664455372865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573621787309109636915243 8360432680963664455372865)
              ·
                refine ⟨6270324510722748341529649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360432680963664455372865 6270324510722748341529649)
                ·
                  refine ⟨4702743383042061256147237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270324510722748341529649 4702743383042061256147237)
                  ·
                    refine ⟨881764384320386485527607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4702743383042061256147237 881764384320386485527607)
                    ·
                      rfl

theorem cell22_2575845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2575845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575845 prefixEnd_2575845 := by exact prefixLift 2575845
  have htrace : WordTrace (prefixWord ++ tailWord_2575845) baseStart_2575845 baseEnd_2575845 := by
    simpa [prefixWord, tailWord_2575845, baseEnd_2575845] using wordTrace_append hprefix tailTrace_2575845
  have hstable : (prefixWord ++ tailWord_2575845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575845).length < 2 ^ (prefixWord ++ tailWord_2575845).sum := by decide
  have hdescent : baseEnd_2575845 < baseStart_2575845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575871 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 9]
def baseStart_2575871 : Nat := 118140960795 + 2575871 * 2 ^ 59
def prefixEnd_2575871 : Nat := 4983230072969 + 3 ^ 40 * 2575871 * 2
def baseEnd_2575871 : Nat := 293924428217243694792509

theorem tailTrace_2575871 : CollatzResearch.WordTrace tailWord_2575871 prefixEnd_2575871 293924428217243694792509 := by
  unfold tailWord_2575871
  simp only [CollatzResearch.WordTrace]
  refine ⟨93949733651066765587791467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62633155767377843725194311 93949733651066765587791467)
  ·
    refine ⟨140924600476600148381687201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93949733651066765587791467 140924600476600148381687201)
    ·
      refine ⟨105693450357450111286265401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140924600476600148381687201 105693450357450111286265401)
      ·
        refine ⟨79270087768087583464699051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105693450357450111286265401 79270087768087583464699051)
        ·
          refine ⟨118905131652131375197048577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79270087768087583464699051 118905131652131375197048577)
          ·
            refine ⟨89178848739098531397786433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118905131652131375197048577 89178848739098531397786433)
            ·
              refine ⟨66884136554323898548339825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89178848739098531397786433 66884136554323898548339825)
              ·
                refine ⟨50163102415742923911254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66884136554323898548339825 50163102415742923911254869)
                ·
                  refine ⟨293924428217243694792509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50163102415742923911254869 293924428217243694792509)
                  ·
                    rfl

theorem cell22_2575871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_2575871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575871 prefixEnd_2575871 := by exact prefixLift 2575871
  have htrace : WordTrace (prefixWord ++ tailWord_2575871) baseStart_2575871 baseEnd_2575871 := by
    simpa [prefixWord, tailWord_2575871, baseEnd_2575871] using wordTrace_append hprefix tailTrace_2575871
  have hstable : (prefixWord ++ tailWord_2575871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575871).length < 2 ^ (prefixWord ++ tailWord_2575871).sum := by decide
  have hdescent : baseEnd_2575871 < baseStart_2575871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575905 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 5]
def baseStart_2575905 : Nat := 118140960795 + 2575905 * 2 ^ 59
def prefixEnd_2575905 : Nat := 4983230072969 + 3 ^ 40 * 2575905 * 2
def baseEnd_2575905 : Nat := 293928307848855443009141

theorem tailTrace_2575905 : CollatzResearch.WordTrace tailWord_2575905 prefixEnd_2575905 293928307848855443009141 := by
  unfold tailWord_2575905
  simp only [CollatzResearch.WordTrace]
  refine ⟨93950973732943589394529169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62633982488629059596352779 93950973732943589394529169)
  ·
    refine ⟨70463230299707692045896877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93950973732943589394529169 70463230299707692045896877)
    ·
      refine ⟨26423711362390384517211329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70463230299707692045896877 26423711362390384517211329)
      ·
        refine ⟨19817783521792788387908497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26423711362390384517211329 19817783521792788387908497)
        ·
          refine ⟨14863337641344591290931373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19817783521792788387908497 14863337641344591290931373)
          ·
            refine ⟨5573751615504221734099265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14863337641344591290931373 5573751615504221734099265)
            ·
              refine ⟨4180313711628166300574449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573751615504221734099265 4180313711628166300574449)
              ·
                refine ⟨3135235283721124725430837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4180313711628166300574449 3135235283721124725430837)
                ·
                  refine ⟨293928307848855443009141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135235283721124725430837 293928307848855443009141)
                  ·
                    rfl

theorem cell22_2575905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_2575905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575905 prefixEnd_2575905 := by exact prefixLift 2575905
  have htrace : WordTrace (prefixWord ++ tailWord_2575905) baseStart_2575905 baseEnd_2575905 := by
    simpa [prefixWord, tailWord_2575905, baseEnd_2575905] using wordTrace_append hprefix tailTrace_2575905
  have hstable : (prefixWord ++ tailWord_2575905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575905).length < 2 ^ (prefixWord ++ tailWord_2575905).sum := by decide
  have hdescent : baseEnd_2575905 < baseStart_2575905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2575993 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2575993 : Nat := 118140960795 + 2575993 * 2 ^ 59
def prefixEnd_2575993 : Nat := 4983230072969 + 3 ^ 40 * 2575993 * 2
def baseEnd_2575993 : Nat := 881815047744963432827153

theorem tailTrace_2575993 : CollatzResearch.WordTrace tailWord_2575993 prefixEnd_2575993 881815047744963432827153 := by
  unfold tailWord_2575993
  simp only [CollatzResearch.WordTrace]
  refine ⟨93954183356624780423732633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62636122237749853615821755 93954183356624780423732633)
  ·
    refine ⟨70465637517468585317799475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93954183356624780423732633 70465637517468585317799475)
    ·
      refine ⟨105698456276202877976699213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70465637517468585317799475 105698456276202877976699213)
      ·
        refine ⟨39636921103576079241262205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105698456276202877976699213 39636921103576079241262205)
        ·
          refine ⟨14863845413841029715473327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39636921103576079241262205 14863845413841029715473327)
          ·
            refine ⟨22295768120761544573209991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863845413841029715473327 22295768120761544573209991)
            ·
              refine ⟨33443652181142316859814987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22295768120761544573209991 33443652181142316859814987)
              ·
                refine ⟨50165478271713475289722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33443652181142316859814987 50165478271713475289722481)
                ·
                  refine ⟨37624108703785106467291861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50165478271713475289722481 37624108703785106467291861)
                  ·
                    refine ⟨881815047744963432827153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37624108703785106467291861 881815047744963432827153)
                    ·
                      rfl

theorem cell22_2575993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2575993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2575993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2575993 prefixEnd_2575993 := by exact prefixLift 2575993
  have htrace : WordTrace (prefixWord ++ tailWord_2575993) baseStart_2575993 baseEnd_2575993 := by
    simpa [prefixWord, tailWord_2575993, baseEnd_2575993] using wordTrace_append hprefix tailTrace_2575993
  have hstable : (prefixWord ++ tailWord_2575993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2575993).length < 2 ^ (prefixWord ++ tailWord_2575993).sum := by decide
  have hdescent : baseEnd_2575993 < baseStart_2575993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2575993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576151 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 2, 3]
def baseStart_2576151 : Nat := 118140960795 + 2576151 * 2 ^ 59
def prefixEnd_2576151 : Nat := 4983230072969 + 3 ^ 40 * 2576151 * 2
def baseEnd_2576151 : Nat := 881869134373903687376669

theorem tailTrace_2576151 : CollatzResearch.WordTrace tailWord_2576151 prefixEnd_2576151 881869134373903687376669 := by
  unfold tailWord_2576151
  simp only [CollatzResearch.WordTrace]
  refine ⟨93959946090052373407984307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62639964060034915605322871 93959946090052373407984307)
  ·
    refine ⟨140939919135078560111976461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93959946090052373407984307 140939919135078560111976461)
    ·
      refine ⟨52852469675654460041991173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140939919135078560111976461 52852469675654460041991173)
      ·
        refine ⟨9909838064185211257873345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52852469675654460041991173 9909838064185211257873345)
        ·
          refine ⟨7432378548138908443405009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9909838064185211257873345 7432378548138908443405009)
          ·
            refine ⟨5574283911104181332553757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7432378548138908443405009 5574283911104181332553757)
            ·
              refine ⟨2090356466664067999707659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5574283911104181332553757 2090356466664067999707659)
              ·
                refine ⟨3135534699996101999561489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090356466664067999707659 3135534699996101999561489)
                ·
                  refine ⟨2351651024997076499671117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135534699996101999561489 2351651024997076499671117)
                  ·
                    refine ⟨881869134373903687376669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351651024997076499671117 881869134373903687376669)
                    ·
                      rfl

theorem cell22_2576151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_2576151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576151 prefixEnd_2576151 := by exact prefixLift 2576151
  have htrace : WordTrace (prefixWord ++ tailWord_2576151) baseStart_2576151 baseEnd_2576151 := by
    simpa [prefixWord, tailWord_2576151, baseEnd_2576151] using wordTrace_append hprefix tailTrace_2576151
  have hstable : (prefixWord ++ tailWord_2576151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576151).length < 2 ^ (prefixWord ++ tailWord_2576151).sum := by decide
  have hdescent : baseEnd_2576151 < baseStart_2576151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576164 : List Nat := [2, 3, 1, 3, 2, 3, 2, 6]
def baseStart_2576164 : Nat := 118140960795 + 2576164 * 2 ^ 59
def prefixEnd_2576164 : Nat := 4983230072969 + 3 ^ 40 * 2576164 * 2
def baseEnd_2576164 : Nat := 97985953837730665200181

theorem tailTrace_2576164 : CollatzResearch.WordTrace tailWord_2576164 prefixEnd_2576164 97985953837730665200181 := by
  unfold tailWord_2576164
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980210119502638314103773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62640280159336851085471697 46980210119502638314103773)
  ·
    refine ⟨17617578794813489367788915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46980210119502638314103773 17617578794813489367788915)
    ·
      refine ⟨26426368192220234051683373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617578794813489367788915 26426368192220234051683373)
      ·
        refine ⟨9909888072082587769381265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26426368192220234051683373 9909888072082587769381265)
        ·
          refine ⟨7432416054061940827035949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9909888072082587769381265 7432416054061940827035949)
          ·
            refine ⟨2787156020273227810138481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7432416054061940827035949 2787156020273227810138481)
            ·
              refine ⟨2090367015204920857603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787156020273227810138481 2090367015204920857603861)
              ·
                refine ⟨97985953837730665200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2090367015204920857603861 97985953837730665200181)
                ·
                  rfl

theorem cell22_2576164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_2576164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576164 prefixEnd_2576164 := by exact prefixLift 2576164
  have htrace : WordTrace (prefixWord ++ tailWord_2576164) baseStart_2576164 baseEnd_2576164 := by
    simpa [prefixWord, tailWord_2576164, baseEnd_2576164] using wordTrace_append hprefix tailTrace_2576164
  have hstable : (prefixWord ++ tailWord_2576164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576164).length < 2 ^ (prefixWord ++ tailWord_2576164).sum := by decide
  have hdescent : baseEnd_2576164 < baseStart_2576164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576209 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 5]
def baseStart_2576209 : Nat := 118140960795 + 2576209 * 2 ^ 59
def prefixEnd_2576209 : Nat := 4983230072969 + 3 ^ 40 * 2576209 * 2
def baseEnd_2576209 : Nat := 293962996319736956475497

theorem tailTrace_2576209 : CollatzResearch.WordTrace tailWord_2576209 prefixEnd_2576209 293962996319736956475497 := by
  unfold tailWord_2576209
  simp only [CollatzResearch.WordTrace]
  refine ⟨93962061523842249313595681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62641374349228166209063787 93962061523842249313595681)
  ·
    refine ⟨70471546142881686985196761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93962061523842249313595681 70471546142881686985196761)
    ·
      refine ⟨52853659607161265238897571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70471546142881686985196761 52853659607161265238897571)
      ·
        refine ⟨79280489410741897858346357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52853659607161265238897571 79280489410741897858346357)
        ·
          refine ⟨7432545882257052924219971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79280489410741897858346357 7432545882257052924219971)
          ·
            refine ⟨11148818823385579386329957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7432545882257052924219971 11148818823385579386329957)
            ·
              refine ⟨2090403529384796134936867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11148818823385579386329957 2090403529384796134936867)
              ·
                refine ⟨3135605294077194202405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090403529384796134936867 3135605294077194202405301)
                ·
                  refine ⟨293962996319736956475497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135605294077194202405301 293962996319736956475497)
                  ·
                    rfl

theorem cell22_2576209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_2576209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576209 prefixEnd_2576209 := by exact prefixLift 2576209
  have htrace : WordTrace (prefixWord ++ tailWord_2576209) baseStart_2576209 baseEnd_2576209 := by
    simpa [prefixWord, tailWord_2576209, baseEnd_2576209] using wordTrace_append hprefix tailTrace_2576209
  have hstable : (prefixWord ++ tailWord_2576209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576209).length < 2 ^ (prefixWord ++ tailWord_2576209).sum := by decide
  have hdescent : baseEnd_2576209 < baseStart_2576209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576284 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2576284 : Nat := 118140960795 + 2576284 * 2 ^ 59
def prefixEnd_2576284 : Nat := 4983230072969 + 3 ^ 40 * 2576284 * 2
def baseEnd_2576284 : Nat := 881914662991935673801261

theorem tailTrace_2576284 : CollatzResearch.WordTrace tailWord_2576284 prefixEnd_2576284 881914662991935673801261 := by
  unfold tailWord_2576284
  simp only [CollatzResearch.WordTrace]
  refine ⟨46982398499285268561287953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62643197999047024748383937 46982398499285268561287953)
  ·
    refine ⟨35236798874463951420965965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46982398499285268561287953 35236798874463951420965965)
    ·
      refine ⟨13213799577923981782862237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35236798874463951420965965 13213799577923981782862237)
      ·
        refine ⟨4955174841721493168573339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13213799577923981782862237 4955174841721493168573339)
        ·
          refine ⟨7432762262582239752860009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955174841721493168573339 7432762262582239752860009)
          ·
            refine ⟨5574571696936679814645007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7432762262582239752860009 5574571696936679814645007)
            ·
              refine ⟨8361857545405019721967511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5574571696936679814645007 8361857545405019721967511)
              ·
                refine ⟨12542786318107529582951267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361857545405019721967511 12542786318107529582951267)
                ·
                  refine ⟨18814179477161294374426901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542786318107529582951267 18814179477161294374426901)
                  ·
                    refine ⟨881914662991935673801261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18814179477161294374426901 881914662991935673801261)
                    ·
                      rfl

theorem cell22_2576284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2576284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576284 prefixEnd_2576284 := by exact prefixLift 2576284
  have htrace : WordTrace (prefixWord ++ tailWord_2576284) baseStart_2576284 baseEnd_2576284 := by
    simpa [prefixWord, tailWord_2576284, baseEnd_2576284] using wordTrace_append hprefix tailTrace_2576284
  have hstable : (prefixWord ++ tailWord_2576284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576284).length < 2 ^ (prefixWord ++ tailWord_2576284).sum := by decide
  have hdescent : baseEnd_2576284 < baseStart_2576284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576290 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2576290 : Nat := 118140960795 + 2576290 * 2 ^ 59
def prefixEnd_2576290 : Nat := 4983230072969 + 3 ^ 40 * 2576290 * 2
def baseEnd_2576290 : Nat := 881916716914553658151243

theorem tailTrace_2576290 : CollatzResearch.WordTrace tailWord_2576290 prefixEnd_2576290 881916716914553658151243 := by
  unfold tailWord_2576290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23491253959137200036823581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62643343891032533431529549 23491253959137200036823581)
  ·
    refine ⟨8809220234676450013808843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23491253959137200036823581 8809220234676450013808843)
    ·
      refine ⟨13213830352014675020713265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8809220234676450013808843 13213830352014675020713265)
      ·
        refine ⟨9910372764011006265534949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13213830352014675020713265 9910372764011006265534949)
        ·
          refine ⟨1858194893252063674787803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9910372764011006265534949 1858194893252063674787803)
          ·
            refine ⟨2787292339878095512181705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858194893252063674787803 2787292339878095512181705)
            ·
              refine ⟨2090469254908571634136279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787292339878095512181705 2090469254908571634136279)
              ·
                refine ⟨3135703882362857451204419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090469254908571634136279 3135703882362857451204419)
                ·
                  refine ⟨4703555823544286176806629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135703882362857451204419 4703555823544286176806629)
                  ·
                    refine ⟨881916716914553658151243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703555823544286176806629 881916716914553658151243)
                    ·
                      rfl

theorem cell22_2576290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2576290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576290 prefixEnd_2576290 := by exact prefixLift 2576290
  have htrace : WordTrace (prefixWord ++ tailWord_2576290) baseStart_2576290 baseEnd_2576290 := by
    simpa [prefixWord, tailWord_2576290, baseEnd_2576290] using wordTrace_append hprefix tailTrace_2576290
  have hstable : (prefixWord ++ tailWord_2576290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576290).length < 2 ^ (prefixWord ++ tailWord_2576290).sum := by decide
  have hdescent : baseEnd_2576290 < baseStart_2576290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576365 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2576365 : Nat := 118140960795 + 2576365 * 2 ^ 59
def prefixEnd_2576365 : Nat := 4983230072969 + 3 ^ 40 * 2576365 * 2
def baseEnd_2576365 : Nat := 881942390947278462526013

theorem tailTrace_2576365 : CollatzResearch.WordTrace tailWord_2576365 prefixEnd_2576365 881942390947278462526013 := by
  unfold tailWord_2576365
  simp only [CollatzResearch.WordTrace]
  refine ⟨93967751311277087956274549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62645167540851391970849699 93967751311277087956274549)
  ·
    refine ⟨8809476685432226995900739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93967751311277087956274549 8809476685432226995900739)
    ·
      refine ⟨13214215028148340493851109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8809476685432226995900739 13214215028148340493851109)
      ·
        refine ⟨2477665317777813842597083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13214215028148340493851109 2477665317777813842597083)
        ·
          refine ⟨3716497976666720763895625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477665317777813842597083 3716497976666720763895625)
          ·
            refine ⟨2787373482500040572921719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3716497976666720763895625 2787373482500040572921719)
            ·
              refine ⟨4181060223750060859382579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787373482500040572921719 4181060223750060859382579)
              ·
                refine ⟨6271590335625091289073869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181060223750060859382579 6271590335625091289073869)
                ·
                  refine ⟨2351846375859409233402701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6271590335625091289073869 2351846375859409233402701)
                  ·
                    refine ⟨881942390947278462526013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351846375859409233402701 881942390947278462526013)
                    ·
                      rfl

theorem cell22_2576365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2576365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576365 prefixEnd_2576365 := by exact prefixLift 2576365
  have htrace : WordTrace (prefixWord ++ tailWord_2576365) baseStart_2576365 baseEnd_2576365 := by
    simpa [prefixWord, tailWord_2576365, baseEnd_2576365] using wordTrace_append hprefix tailTrace_2576365
  have hstable : (prefixWord ++ tailWord_2576365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576365).length < 2 ^ (prefixWord ++ tailWord_2576365).sum := by decide
  have hdescent : baseEnd_2576365 < baseStart_2576365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576387 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_2576387 : Nat := 118140960795 + 2576387 * 2 ^ 59
def prefixEnd_2576387 : Nat := 4983230072969 + 3 ^ 40 * 2576387 * 2
def baseEnd_2576387 : Nat := 881949921996877738475945

theorem tailTrace_2576387 : CollatzResearch.WordTrace tailWord_2576387 prefixEnd_2576387 881949921996877738475945 := by
  unfold tailWord_2576387
  simp only [CollatzResearch.WordTrace]
  refine ⟨93968553717197385713575415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62645702478131590475716943 93968553717197385713575415)
  ·
    refine ⟨140952830575796078570363123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93968553717197385713575415 140952830575796078570363123)
    ·
      refine ⟨211429245863694117855544685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140952830575796078570363123 211429245863694117855544685)
      ·
        refine ⟨79285967198885294195829257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211429245863694117855544685 79285967198885294195829257)
        ·
          refine ⟨59464475399163970646871943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79285967198885294195829257 59464475399163970646871943)
          ·
            refine ⟨89196713098745955970307915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59464475399163970646871943 89196713098745955970307915)
            ·
              refine ⟨133795069648118933955461873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89196713098745955970307915 133795069648118933955461873)
              ·
                refine ⟨100346302236089200466596405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133795069648118933955461873 100346302236089200466596405)
                ·
                  refine ⟨9407465834633362543743413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100346302236089200466596405 9407465834633362543743413)
                  ·
                    refine ⟨881949921996877738475945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9407465834633362543743413 881949921996877738475945)
                    ·
                      rfl

theorem cell22_2576387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_2576387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576387 prefixEnd_2576387 := by exact prefixLift 2576387
  have htrace : WordTrace (prefixWord ++ tailWord_2576387) baseStart_2576387 baseEnd_2576387 := by
    simpa [prefixWord, tailWord_2576387, baseEnd_2576387] using wordTrace_append hprefix tailTrace_2576387
  have hstable : (prefixWord ++ tailWord_2576387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576387).length < 2 ^ (prefixWord ++ tailWord_2576387).sum := by decide
  have hdescent : baseEnd_2576387 < baseStart_2576387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576391 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2576391 : Nat := 118140960795 + 2576391 * 2 ^ 59
def prefixEnd_2576391 : Nat := 4983230072969 + 3 ^ 40 * 2576391 * 2
def baseEnd_2576391 : Nat := 881951291278623061375933

theorem tailTrace_2576391 : CollatzResearch.WordTrace tailWord_2576391 prefixEnd_2576391 881951291278623061375933 := by
  unfold tailWord_2576391
  simp only [CollatzResearch.WordTrace]
  refine ⟨93968699609182894396721027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62645799739455262931147351 93968699609182894396721027)
  ·
    refine ⟨140953049413774341595081541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93968699609182894396721027 140953049413774341595081541)
    ·
      refine ⟨26428696765082689049077789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140953049413774341595081541 26428696765082689049077789)
      ·
        refine ⟨9910761286906008393404171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26428696765082689049077789 9910761286906008393404171)
        ·
          refine ⟨14866141930359012590106257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910761286906008393404171 14866141930359012590106257)
          ·
            refine ⟨11149606447769259442579693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14866141930359012590106257 11149606447769259442579693)
            ·
              refine ⟨4181102417913472290967385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11149606447769259442579693 4181102417913472290967385)
              ·
                refine ⟨3135826813435104218225539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181102417913472290967385 3135826813435104218225539)
                ·
                  refine ⟨4703740220152656327338309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135826813435104218225539 4703740220152656327338309)
                  ·
                    refine ⟨881951291278623061375933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703740220152656327338309 881951291278623061375933)
                    ·
                      rfl

theorem cell22_2576391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2576391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576391 prefixEnd_2576391 := by exact prefixLift 2576391
  have htrace : WordTrace (prefixWord ++ tailWord_2576391) baseStart_2576391 baseEnd_2576391 := by
    simpa [prefixWord, tailWord_2576391, baseEnd_2576391] using wordTrace_append hprefix tailTrace_2576391
  have hstable : (prefixWord ++ tailWord_2576391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576391).length < 2 ^ (prefixWord ++ tailWord_2576391).sum := by decide
  have hdescent : baseEnd_2576391 < baseStart_2576391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576417 : List Nat := [1, 2, 3, 2, 14]
def baseStart_2576417 : Nat := 118140960795 + 2576417 * 2 ^ 59
def prefixEnd_2576417 : Nat := 4983230072969 + 3 ^ 40 * 2576417 * 2
def baseEnd_2576417 : Nat := 3629465809094517120271

theorem tailTrace_2576417 : CollatzResearch.WordTrace tailWord_2576417 prefixEnd_2576417 3629465809094517120271 := by
  unfold tailWord_2576417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93969647907088700837167505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62646431938059133891445003 93969647907088700837167505)
  ·
    refine ⟨70477235930316525627875629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93969647907088700837167505 70477235930316525627875629)
    ·
      refine ⟨26428963473868697110453361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70477235930316525627875629 26428963473868697110453361)
      ·
        refine ⟨19821722605401522832840021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26428963473868697110453361 19821722605401522832840021)
        ·
          refine ⟨3629465809094517120271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 19821722605401522832840021 3629465809094517120271)
          ·
            rfl

theorem cell22_2576417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 14].length) (baseStart_2576417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576417 prefixEnd_2576417 := by exact prefixLift 2576417
  have htrace : WordTrace (prefixWord ++ tailWord_2576417) baseStart_2576417 baseEnd_2576417 := by
    simpa [prefixWord, tailWord_2576417, baseEnd_2576417] using wordTrace_append hprefix tailTrace_2576417
  have hstable : (prefixWord ++ tailWord_2576417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576417).length < 2 ^ (prefixWord ++ tailWord_2576417).sum := by decide
  have hdescent : baseEnd_2576417 < baseStart_2576417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576419 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_2576419 : Nat := 118140960795 + 2576419 * 2 ^ 59
def prefixEnd_2576419 : Nat := 4983230072969 + 3 ^ 40 * 2576419 * 2
def baseEnd_2576419 : Nat := 881960876250840321675847

theorem tailTrace_2576419 : CollatzResearch.WordTrace tailWord_2576419 prefixEnd_2576419 881960876250840321675847 := by
  unfold tailWord_2576419
  simp only [CollatzResearch.WordTrace]
  refine ⟨93969720853081455178740311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62646480568720970119160207 93969720853081455178740311)
  ·
    refine ⟨140954581279622182768110467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93969720853081455178740311 140954581279622182768110467)
    ·
      refine ⟨211431871919433274152165701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140954581279622182768110467 211431871919433274152165701)
      ·
        refine ⟨39643475984893738903531069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211431871919433274152165701 39643475984893738903531069)
        ·
          refine ⟨14866303494335152088824151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39643475984893738903531069 14866303494335152088824151)
          ·
            refine ⟨22299455241502728133236227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866303494335152088824151 22299455241502728133236227)
            ·
              refine ⟨33449182862254092199854341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22299455241502728133236227 33449182862254092199854341)
              ·
                refine ⟨6271721786672642287472689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33449182862254092199854341 6271721786672642287472689)
                ·
                  refine ⟨4703791340004481715604517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6271721786672642287472689 4703791340004481715604517)
                  ·
                    refine ⟨881960876250840321675847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4703791340004481715604517 881960876250840321675847)
                    ·
                      rfl

theorem cell22_2576419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_2576419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576419 prefixEnd_2576419 := by exact prefixLift 2576419
  have htrace : WordTrace (prefixWord ++ tailWord_2576419) baseStart_2576419 baseEnd_2576419 := by
    simpa [prefixWord, tailWord_2576419, baseEnd_2576419] using wordTrace_append hprefix tailTrace_2576419
  have hstable : (prefixWord ++ tailWord_2576419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576419).length < 2 ^ (prefixWord ++ tailWord_2576419).sum := by decide
  have hdescent : baseEnd_2576419 < baseStart_2576419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576421 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_2576421 : Nat := 118140960795 + 2576421 * 2 ^ 59
def prefixEnd_2576421 : Nat := 4983230072969 + 3 ^ 40 * 2576421 * 2
def baseEnd_2576421 : Nat := 881961560891712983125841

theorem tailTrace_2576421 : CollatzResearch.WordTrace tailWord_2576421 prefixEnd_2576421 881961560891712983125841 := by
  unfold tailWord_2576421
  simp only [CollatzResearch.WordTrace]
  refine ⟨93969793799074209520313117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62646529199382806346875411 93969793799074209520313117)
  ·
    refine ⟨35238672674652828570117419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93969793799074209520313117 35238672674652828570117419)
    ·
      refine ⟨52858009011979242855176129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35238672674652828570117419 52858009011979242855176129)
      ·
        refine ⟨39643506758984432141382097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52858009011979242855176129 39643506758984432141382097)
        ·
          refine ⟨29732630069238324106036573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39643506758984432141382097 29732630069238324106036573)
          ·
            refine ⟨11149736275964371539763715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29732630069238324106036573 11149736275964371539763715)
            ·
              refine ⟨16724604413946557309645573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11149736275964371539763715 16724604413946557309645573)
              ·
                refine ⟨3135863327614979495558545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16724604413946557309645573 3135863327614979495558545)
                ·
                  refine ⟨2351897495711234621668909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135863327614979495558545 2351897495711234621668909)
                  ·
                    refine ⟨881961560891712983125841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351897495711234621668909 881961560891712983125841)
                    ·
                      rfl

theorem cell22_2576421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_2576421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576421 prefixEnd_2576421 := by exact prefixLift 2576421
  have htrace : WordTrace (prefixWord ++ tailWord_2576421) baseStart_2576421 baseEnd_2576421 := by
    simpa [prefixWord, tailWord_2576421, baseEnd_2576421] using wordTrace_append hprefix tailTrace_2576421
  have hstable : (prefixWord ++ tailWord_2576421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576421).length < 2 ^ (prefixWord ++ tailWord_2576421).sum := by decide
  have hdescent : baseEnd_2576421 < baseStart_2576421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576434 : List Nat := [3, 2, 1, 1, 2, 3, 3, 7]
def baseStart_2576434 : Nat := 118140960795 + 2576434 * 2 ^ 59
def prefixEnd_2576434 : Nat := 4983230072969 + 3 ^ 40 * 2576434 * 2
def baseEnd_2576434 : Nat := 97996223450820586950089

theorem tailTrace_2576434 : CollatzResearch.WordTrace tailWord_2576434 prefixEnd_2576434 97996223450820586950089 := by
  unfold tailWord_2576434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492566987006778185134089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62646845298684741827024237 23492566987006778185134089)
  ·
    refine ⟨17619425240255083638850567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23492566987006778185134089 17619425240255083638850567)
    ·
      refine ⟨26429137860382625458275851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17619425240255083638850567 26429137860382625458275851)
      ·
        refine ⟨39643706790573938187413777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26429137860382625458275851 39643706790573938187413777)
        ·
          refine ⟨29732780092930453640560333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39643706790573938187413777 29732780092930453640560333)
          ·
            refine ⟨11149792534848920115210125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29732780092930453640560333 11149792534848920115210125)
            ·
              refine ⟨4181172200568345043203797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11149792534848920115210125 4181172200568345043203797)
              ·
                refine ⟨97996223450820586950089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4181172200568345043203797 97996223450820586950089)
                ·
                  rfl

theorem cell22_2576434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_2576434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576434 prefixEnd_2576434 := by exact prefixLift 2576434
  have htrace : WordTrace (prefixWord ++ tailWord_2576434) baseStart_2576434 baseEnd_2576434 := by
    simpa [prefixWord, tailWord_2576434, baseEnd_2576434] using wordTrace_append hprefix tailTrace_2576434
  have hstable : (prefixWord ++ tailWord_2576434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576434).length < 2 ^ (prefixWord ++ tailWord_2576434).sum := by decide
  have hdescent : baseEnd_2576434 < baseStart_2576434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576438 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2576438 : Nat := 118140960795 + 2576438 * 2 ^ 59
def prefixEnd_2576438 : Nat := 4983230072969 + 3 ^ 40 * 2576438 * 2
def baseEnd_2576438 : Nat := 881967380339130605450789

theorem tailTrace_2576438 : CollatzResearch.WordTrace tailWord_2576438 prefixEnd_2576438 881967380339130605450789 := by
  unfold tailWord_2576438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873150865000788838980123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62646942560008414282454645 5873150865000788838980123)
  ·
    refine ⟨8809726297501183258470185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5873150865000788838980123 8809726297501183258470185)
    ·
      refine ⟨6607294723125887443852639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809726297501183258470185 6607294723125887443852639)
      ·
        refine ⟨9910942084688831165778959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607294723125887443852639 9910942084688831165778959)
        ·
          refine ⟨14866413127033246748668439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910942084688831165778959 14866413127033246748668439)
          ·
            refine ⟨22299619690549870123002659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14866413127033246748668439 22299619690549870123002659)
            ·
              refine ⟨33449429535824805184503989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22299619690549870123002659 33449429535824805184503989)
              ·
                refine ⟨3135884018983575486047249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33449429535824805184503989 3135884018983575486047249)
                ·
                  refine ⟨2351913014237681614535437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3135884018983575486047249 2351913014237681614535437)
                  ·
                    refine ⟨881967380339130605450789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351913014237681614535437 881967380339130605450789)
                    ·
                      rfl

theorem cell22_2576438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2576438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576438 prefixEnd_2576438 := by exact prefixLift 2576438
  have htrace : WordTrace (prefixWord ++ tailWord_2576438) baseStart_2576438 baseEnd_2576438 := by
    simpa [prefixWord, tailWord_2576438, baseEnd_2576438] using wordTrace_append hprefix tailTrace_2576438
  have hstable : (prefixWord ++ tailWord_2576438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576438).length < 2 ^ (prefixWord ++ tailWord_2576438).sum := by decide
  have hdescent : baseEnd_2576438 < baseStart_2576438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576479 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 5]
def baseStart_2576479 : Nat := 118140960795 + 2576479 * 2 ^ 59
def prefixEnd_2576479 : Nat := 4983230072969 + 3 ^ 40 * 2576479 * 2
def baseEnd_2576479 : Nat := 293993805159006721725221

theorem tailTrace_2576479 : CollatzResearch.WordTrace tailWord_2576479 prefixEnd_2576479 293993805159006721725221 := by
  unfold tailWord_2576479
  simp only [CollatzResearch.WordTrace]
  refine ⟨93971909232864085425924491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62647939488576056950616327 93971909232864085425924491)
  ·
    refine ⟨140957863849296128138886737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93971909232864085425924491 140957863849296128138886737)
    ·
      refine ⟨105718397886972096104165053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140957863849296128138886737 105718397886972096104165053)
      ·
        refine ⟨39644399207614536039061895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105718397886972096104165053 39644399207614536039061895)
        ·
          refine ⟨59466598811421804058592843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39644399207614536039061895 59466598811421804058592843)
          ·
            refine ⟨89199898217132706087889265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59466598811421804058592843 89199898217132706087889265)
            ·
              refine ⟨66899923662849529565916949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89199898217132706087889265 66899923662849529565916949)
              ·
                refine ⟨3135933921696071698402357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66899923662849529565916949 3135933921696071698402357)
                ·
                  refine ⟨293993805159006721725221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135933921696071698402357 293993805159006721725221)
                  ·
                    rfl

theorem cell22_2576479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 5].length) (baseStart_2576479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576479 prefixEnd_2576479 := by exact prefixLift 2576479
  have htrace : WordTrace (prefixWord ++ tailWord_2576479) baseStart_2576479 baseEnd_2576479 := by
    simpa [prefixWord, tailWord_2576479, baseEnd_2576479] using wordTrace_append hprefix tailTrace_2576479
  have hstable : (prefixWord ++ tailWord_2576479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576479).length < 2 ^ (prefixWord ++ tailWord_2576479).sum := by decide
  have hdescent : baseEnd_2576479 < baseStart_2576479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576483 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 1, 3]
def baseStart_2576483 : Nat := 118140960795 + 2576483 * 2 ^ 59
def prefixEnd_2576483 : Nat := 4983230072969 + 3 ^ 40 * 2576483 * 2
def baseEnd_2576483 : Nat := 881982784758765488075651

theorem tailTrace_2576483 : CollatzResearch.WordTrace tailWord_2576483 prefixEnd_2576483 881982784758765488075651 := by
  unfold tailWord_2576483
  simp only [CollatzResearch.WordTrace]
  refine ⟨93972055124849594109070103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62648036749899729406046735 93972055124849594109070103)
  ·
    refine ⟨140958082687274391163605155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93972055124849594109070103 140958082687274391163605155)
    ·
      refine ⟨211437124030911586745407733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140958082687274391163605155 211437124030911586745407733)
      ·
        refine ⟨19822230377897961257381975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211437124030911586745407733 19822230377897961257381975)
        ·
          refine ⟨29733345566846941886072963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19822230377897961257381975 29733345566846941886072963)
          ·
            refine ⟨44600018350270412829109445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29733345566846941886072963 44600018350270412829109445)
            ·
              refine ⟨8362503440675702405458021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44600018350270412829109445 8362503440675702405458021)
              ·
                refine ⟨1567969395126694201023379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8362503440675702405458021 1567969395126694201023379)
                ·
                  refine ⟨2351954092690041301535069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567969395126694201023379 2351954092690041301535069)
                  ·
                    refine ⟨881982784758765488075651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351954092690041301535069 881982784758765488075651)
                    ·
                      rfl

theorem cell22_2576483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 3].length) (baseStart_2576483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576483 prefixEnd_2576483 := by exact prefixLift 2576483
  have htrace : WordTrace (prefixWord ++ tailWord_2576483) baseStart_2576483 baseEnd_2576483 := by
    simpa [prefixWord, tailWord_2576483, baseEnd_2576483] using wordTrace_append hprefix tailTrace_2576483
  have hstable : (prefixWord ++ tailWord_2576483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576483).length < 2 ^ (prefixWord ++ tailWord_2576483).sum := by decide
  have hdescent : baseEnd_2576483 < baseStart_2576483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576541 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2576541 : Nat := 118140960795 + 2576541 * 2 ^ 59
def prefixEnd_2576541 : Nat := 4983230072969 + 3 ^ 40 * 2576541 * 2
def baseEnd_2576541 : Nat := 294000879781357556708491

theorem tailTrace_2576541 : CollatzResearch.WordTrace tailWord_2576541 prefixEnd_2576541 294000879781357556708491 := by
  unfold tailWord_2576541
  simp only [CollatzResearch.WordTrace]
  refine ⟨93974170558639470014681477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62649447039092980009787651 93974170558639470014681477)
  ·
    refine ⟨17620156979744900627752777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93974170558639470014681477 17620156979744900627752777)
    ·
      refine ⟨13215117734808675470814583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17620156979744900627752777 13215117734808675470814583)
      ·
        refine ⟨19822676602213013206221875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13215117734808675470814583 19822676602213013206221875)
        ·
          refine ⟨29734014903319519809332813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19822676602213013206221875 29734014903319519809332813)
          ·
            refine ⟨11150255588744819928499805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29734014903319519809332813 11150255588744819928499805)
            ·
              refine ⟨4181345845779307473187427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11150255588744819928499805 4181345845779307473187427)
              ·
                refine ⟨6272018768668961209781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181345845779307473187427 6272018768668961209781141)
                ·
                  refine ⟨294000879781357556708491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6272018768668961209781141 294000879781357556708491)
                  ·
                    rfl

theorem cell22_2576541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2576541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576541 prefixEnd_2576541 := by exact prefixLift 2576541
  have htrace : WordTrace (prefixWord ++ tailWord_2576541) baseStart_2576541 baseEnd_2576541 := by
    simpa [prefixWord, tailWord_2576541, baseEnd_2576541] using wordTrace_append hprefix tailTrace_2576541
  have hstable : (prefixWord ++ tailWord_2576541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576541).length < 2 ^ (prefixWord ++ tailWord_2576541).sum := by decide
  have hdescent : baseEnd_2576541 < baseStart_2576541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576569 : List Nat := [1, 2, 1, 4, 1, 2, 1, 10]
def baseStart_2576569 : Nat := 118140960795 + 2576569 * 2 ^ 59
def prefixEnd_2576569 : Nat := 4983230072969 + 3 ^ 40 * 2576569 * 2
def baseEnd_2576569 : Nat := 98001358257365547825043

theorem tailTrace_2576569 : CollatzResearch.WordTrace tailWord_2576569 prefixEnd_2576569 98001358257365547825043 := by
  unfold tailWord_2576569
  simp only [CollatzResearch.WordTrace]
  refine ⟨93975191802538030796700761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62650127868358687197800507 93975191802538030796700761)
  ·
    refine ⟨70481393851903523097525571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93975191802538030796700761 70481393851903523097525571)
    ·
      refine ⟨105722090777855284646288357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70481393851903523097525571 105722090777855284646288357)
      ·
        refine ⟨19822892020847865871179067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105722090777855284646288357 19822892020847865871179067)
        ·
          refine ⟨29734338031271798806768601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19822892020847865871179067 29734338031271798806768601)
          ·
            refine ⟨22300753523453849105076451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29734338031271798806768601 22300753523453849105076451)
            ·
              refine ⟨33451130285180773657614677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22300753523453849105076451 33451130285180773657614677)
              ·
                refine ⟨98001358257365547825043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33451130285180773657614677 98001358257365547825043)
                ·
                  rfl

theorem cell22_2576569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 10].length) (baseStart_2576569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576569 prefixEnd_2576569 := by exact prefixLift 2576569
  have htrace : WordTrace (prefixWord ++ tailWord_2576569) baseStart_2576569 baseEnd_2576569 := by
    simpa [prefixWord, tailWord_2576569, baseEnd_2576569] using wordTrace_append hprefix tailTrace_2576569
  have hstable : (prefixWord ++ tailWord_2576569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576569).length < 2 ^ (prefixWord ++ tailWord_2576569).sum := by decide
  have hdescent : baseEnd_2576569 < baseStart_2576569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576571 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_2576571 : Nat := 118140960795 + 2576571 * 2 ^ 59
def prefixEnd_2576571 : Nat := 4983230072969 + 3 ^ 40 * 2576571 * 2
def baseEnd_2576571 : Nat := 882012908957162591875381

theorem tailTrace_2576571 : CollatzResearch.WordTrace tailWord_2576571 prefixEnd_2576571 882012908957162591875381 := by
  unfold tailWord_2576571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93975264748530785138273567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62650176499020523425515711 93975264748530785138273567)
  ·
    refine ⟨140962897122796177707410351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93975264748530785138273567 140962897122796177707410351)
    ·
      refine ⟨211444345684194266561115527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140962897122796177707410351 211444345684194266561115527)
      ·
        refine ⟨317166518526291399841673291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211444345684194266561115527 317166518526291399841673291)
        ·
          refine ⟨475749777789437099762509937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317166518526291399841673291 475749777789437099762509937)
          ·
            refine ⟨356812333342077824821882453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475749777789437099762509937 356812333342077824821882453)
            ·
              refine ⟨4181394531352474509631435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 356812333342077824821882453 4181394531352474509631435)
              ·
                refine ⟨6272091797028711764447153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181394531352474509631435 6272091797028711764447153)
                ·
                  refine ⟨4704068847771533823335365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272091797028711764447153 4704068847771533823335365)
                  ·
                    refine ⟨882012908957162591875381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704068847771533823335365 882012908957162591875381)
                    ·
                      rfl

theorem cell22_2576571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_2576571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576571 prefixEnd_2576571 := by exact prefixLift 2576571
  have htrace : WordTrace (prefixWord ++ tailWord_2576571) baseStart_2576571 baseEnd_2576571 := by
    simpa [prefixWord, tailWord_2576571, baseEnd_2576571] using wordTrace_append hprefix tailTrace_2576571
  have hstable : (prefixWord ++ tailWord_2576571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576571).length < 2 ^ (prefixWord ++ tailWord_2576571).sum := by decide
  have hdescent : baseEnd_2576571 < baseStart_2576571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576577 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2576577 : Nat := 118140960795 + 2576577 * 2 ^ 59
def prefixEnd_2576577 : Nat := 4983230072969 + 3 ^ 40 * 2576577 * 2
def baseEnd_2576577 : Nat := 882014962879780576225363

theorem tailTrace_2576577 : CollatzResearch.WordTrace tailWord_2576577 prefixEnd_2576577 882014962879780576225363 := by
  unfold tailWord_2576577
  simp only [CollatzResearch.WordTrace]
  refine ⟨93975483586509048162991985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62650322391006032108661323 93975483586509048162991985)
  ·
    refine ⟨70481612689881786122243989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93975483586509048162991985 70481612689881786122243989)
    ·
      refine ⟨3303825594838208724480187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70481612689881786122243989 3303825594838208724480187)
      ·
        refine ⟨4955738392257313086720281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303825594838208724480187 4955738392257313086720281)
        ·
          refine ⟨3716803794192984815040211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4955738392257313086720281 3716803794192984815040211)
          ·
            refine ⟨5575205691289477222560317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716803794192984815040211 5575205691289477222560317)
            ·
              refine ⟨2090702134233553958460119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5575205691289477222560317 2090702134233553958460119)
              ·
                refine ⟨3136053201350330937690179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090702134233553958460119 3136053201350330937690179)
                ·
                  refine ⟨4704079802025496406535269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136053201350330937690179 4704079802025496406535269)
                  ·
                    refine ⟨882014962879780576225363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704079802025496406535269 882014962879780576225363)
                    ·
                      rfl

theorem cell22_2576577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2576577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576577 prefixEnd_2576577 := by exact prefixLift 2576577
  have htrace : WordTrace (prefixWord ++ tailWord_2576577) baseStart_2576577 baseEnd_2576577 := by
    simpa [prefixWord, tailWord_2576577, baseEnd_2576577] using wordTrace_append hprefix tailTrace_2576577
  have hstable : (prefixWord ++ tailWord_2576577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576577).length < 2 ^ (prefixWord ++ tailWord_2576577).sum := by decide
  have hdescent : baseEnd_2576577 < baseStart_2576577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576590 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2576590 : Nat := 118140960795 + 2576590 * 2 ^ 59
def prefixEnd_2576590 : Nat := 4983230072969 + 3 ^ 40 * 2576590 * 2
def baseEnd_2576590 : Nat := 882019413045452875650323

theorem tailTrace_2576590 : CollatzResearch.WordTrace tailWord_2576590 prefixEnd_2576590 882019413045452875650323 := by
  unfold tailWord_2576590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746994716932743922901903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62650638490307967588810149 11746994716932743922901903)
  ·
    refine ⟨17620492075399115884352855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11746994716932743922901903 17620492075399115884352855)
    ·
      refine ⟨26430738113098673826529283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17620492075399115884352855 26430738113098673826529283)
      ·
        refine ⟨39646107169648010739793925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26430738113098673826529283 39646107169648010739793925)
        ·
          refine ⟨7433645094309002013711361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39646107169648010739793925 7433645094309002013711361)
          ·
            refine ⟨5575233820731751510283521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7433645094309002013711361 5575233820731751510283521)
            ·
              refine ⟨4181425365548813632712641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5575233820731751510283521 4181425365548813632712641)
              ·
                refine ⟨3136069024161610224534481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181425365548813632712641 3136069024161610224534481)
                ·
                  refine ⟨2352051768121207668400861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136069024161610224534481 2352051768121207668400861)
                  ·
                    refine ⟨882019413045452875650323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352051768121207668400861 882019413045452875650323)
                    ·
                      rfl

theorem cell22_2576590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2576590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576590 prefixEnd_2576590 := by exact prefixLift 2576590
  have htrace : WordTrace (prefixWord ++ tailWord_2576590) baseStart_2576590 baseEnd_2576590 := by
    simpa [prefixWord, tailWord_2576590, baseEnd_2576590] using wordTrace_append hprefix tailTrace_2576590
  have hstable : (prefixWord ++ tailWord_2576590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576590).length < 2 ^ (prefixWord ++ tailWord_2576590).sum := by decide
  have hdescent : baseEnd_2576590 < baseStart_2576590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576618 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2576618 : Nat := 118140960795 + 2576618 * 2 ^ 59
def prefixEnd_2576618 : Nat := 4983230072969 + 3 ^ 40 * 2576618 * 2
def baseEnd_2576618 : Nat := 882028998017670135950237

theorem tailTrace_2576618 : CollatzResearch.WordTrace tailWord_2576618 prefixEnd_2576618 882028998017670135950237 := by
  unfold tailWord_2576618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23494244744840128041308627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62651319319573674776823005 23494244744840128041308627)
  ·
    refine ⟨35241367117260192061962941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23494244744840128041308627 35241367117260192061962941)
    ·
      refine ⟨13215512668972572023236103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35241367117260192061962941 13215512668972572023236103)
      ·
        refine ⟨19823269003458858034854155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13215512668972572023236103 19823269003458858034854155)
        ·
          refine ⟨29734903505188287052281233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19823269003458858034854155 29734903505188287052281233)
          ·
            refine ⟨22301177628891215289210925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29734903505188287052281233 22301177628891215289210925)
            ·
              refine ⟨8362941610834205733454097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22301177628891215289210925 8362941610834205733454097)
              ·
                refine ⟨6272206208125654300090573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8362941610834205733454097 6272206208125654300090573)
                ·
                  refine ⟨2352077328047120362533965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6272206208125654300090573 2352077328047120362533965)
                  ·
                    refine ⟨882028998017670135950237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352077328047120362533965 882028998017670135950237)
                    ·
                      rfl

theorem cell22_2576618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2576618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576618 prefixEnd_2576618 := by exact prefixLift 2576618
  have htrace : WordTrace (prefixWord ++ tailWord_2576618) baseStart_2576618 baseEnd_2576618 := by
    simpa [prefixWord, tailWord_2576618, baseEnd_2576618] using wordTrace_append hprefix tailTrace_2576618
  have hstable : (prefixWord ++ tailWord_2576618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576618).length < 2 ^ (prefixWord ++ tailWord_2576618).sum := by decide
  have hdescent : baseEnd_2576618 < baseStart_2576618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576648 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_2576648 : Nat := 118140960795 + 2576648 * 2 ^ 59
def prefixEnd_2576648 : Nat := 4983230072969 + 3 ^ 40 * 2576648 * 2
def baseEnd_2576648 : Nat := 294013089210253352566715

theorem tailTrace_2576648 : CollatzResearch.WordTrace tailWord_2576648 prefixEnd_2576648 294013089210253352566715 := by
  unfold tailWord_2576648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46989036584625913644413299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62652048779501218192551065 46989036584625913644413299)
  ·
    refine ⟨70483554876938870466619949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46989036584625913644413299 70483554876938870466619949)
    ·
      refine ⟨26431333078852076424982481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70483554876938870466619949 26431333078852076424982481)
      ·
        refine ⟨19823499809139057318736861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26431333078852076424982481 19823499809139057318736861)
        ·
          refine ⟨7433812428427146494526323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19823499809139057318736861 7433812428427146494526323)
          ·
            refine ⟨11150718642640719741789485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433812428427146494526323 11150718642640719741789485)
            ·
              refine ⟨4181519490990269903171057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11150718642640719741789485 4181519490990269903171057)
              ·
                refine ⟨3136139618242702427378293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181519490990269903171057 3136139618242702427378293)
                ·
                  refine ⟨294013089210253352566715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3136139618242702427378293 294013089210253352566715)
                  ·
                    rfl

theorem cell22_2576648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_2576648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576648 prefixEnd_2576648 := by exact prefixLift 2576648
  have htrace : WordTrace (prefixWord ++ tailWord_2576648) baseStart_2576648 baseEnd_2576648 := by
    simpa [prefixWord, tailWord_2576648, baseEnd_2576648] using wordTrace_append hprefix tailTrace_2576648
  have hstable : (prefixWord ++ tailWord_2576648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576648).length < 2 ^ (prefixWord ++ tailWord_2576648).sum := by decide
  have hdescent : baseEnd_2576648 < baseStart_2576648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576661 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2576661 : Nat := 118140960795 + 2576661 * 2 ^ 59
def prefixEnd_2576661 : Nat := 4983230072969 + 3 ^ 40 * 2576661 * 2
def baseEnd_2576661 : Nat := 882043717796432357125105

theorem tailTrace_2576661 : CollatzResearch.WordTrace tailWord_2576661 prefixEnd_2576661 882043717796432357125105 := by
  unfold tailWord_2576661
  simp only [CollatzResearch.WordTrace]
  refine ⟨93978547318204730509049837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62652364878803153672699891 93978547318204730509049837)
  ·
    refine ⟨35241955244326773940893689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93978547318204730509049837 35241955244326773940893689)
    ·
      refine ⟨26431466433245080455670267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35241955244326773940893689 26431466433245080455670267)
      ·
        refine ⟨39647199649867620683505401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26431466433245080455670267 39647199649867620683505401)
        ·
          refine ⟨29735399737400715512629051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39647199649867620683505401 29735399737400715512629051)
          ·
            refine ⟨44603099606101073268943577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29735399737400715512629051 44603099606101073268943577)
            ·
              refine ⟨33452324704575804951707683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44603099606101073268943577 33452324704575804951707683)
              ·
                refine ⟨50178487056863707427561525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33452324704575804951707683 50178487056863707427561525)
                ·
                  refine ⟨4704233161580972571333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50178487056863707427561525 4704233161580972571333893)
                  ·
                    refine ⟨882043717796432357125105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704233161580972571333893 882043717796432357125105)
                    ·
                      rfl

theorem cell22_2576661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2576661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576661 prefixEnd_2576661 := by exact prefixLift 2576661
  have htrace : WordTrace (prefixWord ++ tailWord_2576661) baseStart_2576661 baseEnd_2576661 := by
    simpa [prefixWord, tailWord_2576661, baseEnd_2576661] using wordTrace_append hprefix tailTrace_2576661
  have hstable : (prefixWord ++ tailWord_2576661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576661).length < 2 ^ (prefixWord ++ tailWord_2576661).sum := by decide
  have hdescent : baseEnd_2576661 < baseStart_2576661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576686 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2576686 : Nat := 118140960795 + 2576686 * 2 ^ 59
def prefixEnd_2576686 : Nat := 4983230072969 + 3 ^ 40 * 2576686 * 2
def baseEnd_2576686 : Nat := 882052275807340625250029

theorem tailTrace_2576686 : CollatzResearch.WordTrace tailWord_2576686 prefixEnd_2576686 882052275807340625250029 := by
  unfold tailWord_2576686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747432392889269972338739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62652972762076106519139941 11747432392889269972338739)
  ·
    refine ⟨17621148589333904958508109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11747432392889269972338739 17621148589333904958508109)
    ·
      refine ⟨6607930721000214359440541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17621148589333904958508109 6607930721000214359440541)
      ·
        refine ⟨2477974020375080384790203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6607930721000214359440541 2477974020375080384790203)
        ·
          refine ⟨3716961030562620577185305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477974020375080384790203 3716961030562620577185305)
          ·
            refine ⟨2787720772921965432888979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3716961030562620577185305 2787720772921965432888979)
            ·
              refine ⟨4181581159382948149333469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787720772921965432888979 4181581159382948149333469)
              ·
                refine ⟨1568092934768605556000051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181581159382948149333469 1568092934768605556000051)
                ·
                  refine ⟨2352139402152908334000077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568092934768605556000051 2352139402152908334000077)
                  ·
                    refine ⟨882052275807340625250029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352139402152908334000077 882052275807340625250029)
                    ·
                      rfl

theorem cell22_2576686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2576686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576686 prefixEnd_2576686 := by exact prefixLift 2576686
  have htrace : WordTrace (prefixWord ++ tailWord_2576686) baseStart_2576686 baseEnd_2576686 := by
    simpa [prefixWord, tailWord_2576686, baseEnd_2576686] using wordTrace_append hprefix tailTrace_2576686
  have hstable : (prefixWord ++ tailWord_2576686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576686).length < 2 ^ (prefixWord ++ tailWord_2576686).sum := by decide
  have hdescent : baseEnd_2576686 < baseStart_2576686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576691 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_2576691 : Nat := 118140960795 + 2576691 * 2 ^ 59
def prefixEnd_2576691 : Nat := 4983230072969 + 3 ^ 40 * 2576691 * 2
def baseEnd_2576691 : Nat := 882053987409522278875013

theorem tailTrace_2576691 : CollatzResearch.WordTrace tailWord_2576691 prefixEnd_2576691 882053987409522278875013 := by
  unfold tailWord_2576691
  simp only [CollatzResearch.WordTrace]
  refine ⟨93979641508096045632641927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62653094338730697088427951 93979641508096045632641927)
  ·
    refine ⟨140969462262144068448962891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93979641508096045632641927 140969462262144068448962891)
    ·
      refine ⟨211454193393216102673444337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140969462262144068448962891 211454193393216102673444337)
      ·
        refine ⟨158590645044912077005083253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211454193393216102673444337 158590645044912077005083253)
        ·
          refine ⟨14867872972960507219226555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158590645044912077005083253 14867872972960507219226555)
          ·
            refine ⟨22301809459440760828839833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14867872972960507219226555 22301809459440760828839833)
            ·
              refine ⟨16726357094580570621629875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22301809459440760828839833 16726357094580570621629875)
              ·
                refine ⟨25089535641870855932444813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726357094580570621629875 25089535641870855932444813)
                ·
                  refine ⟨9408575865701570974666805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25089535641870855932444813 9408575865701570974666805)
                  ·
                    refine ⟨882053987409522278875013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9408575865701570974666805 882053987409522278875013)
                    ·
                      rfl

theorem cell22_2576691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_2576691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576691 prefixEnd_2576691 := by exact prefixLift 2576691
  have htrace : WordTrace (prefixWord ++ tailWord_2576691) baseStart_2576691 baseEnd_2576691 := by
    simpa [prefixWord, tailWord_2576691, baseEnd_2576691] using wordTrace_append hprefix tailTrace_2576691
  have hstable : (prefixWord ++ tailWord_2576691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576691).length < 2 ^ (prefixWord ++ tailWord_2576691).sum := by decide
  have hdescent : baseEnd_2576691 < baseStart_2576691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576721 : List Nat := [1, 2, 2, 1, 4, 2, 1, 9]
def baseStart_2576721 : Nat := 118140960795 + 2576721 * 2 ^ 59
def prefixEnd_2576721 : Nat := 4983230072969 + 3 ^ 40 * 2576721 * 2
def baseEnd_2576721 : Nat := 98007139669179133402769

theorem tailTrace_2576721 : CollatzResearch.WordTrace tailWord_2576721 prefixEnd_2576721 98007139669179133402769 := by
  unfold tailWord_2576721
  simp only [CollatzResearch.WordTrace]
  refine ⟨93980735697987360756234017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62653823798658240504156011 93980735697987360756234017)
  ·
    refine ⟨70485551773490520567175513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93980735697987360756234017 70485551773490520567175513)
    ·
      refine ⟨52864163830117890425381635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70485551773490520567175513 52864163830117890425381635)
      ·
        refine ⟨79296245745176835638072453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52864163830117890425381635 79296245745176835638072453)
        ·
          refine ⟨14868046077220656682138585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79296245745176835638072453 14868046077220656682138585)
          ·
            refine ⟨11151034557915492511603939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14868046077220656682138585 11151034557915492511603939)
            ·
              refine ⟨16726551836873238767405909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151034557915492511603939 16726551836873238767405909)
              ·
                refine ⟨98007139669179133402769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16726551836873238767405909 98007139669179133402769)
                ·
                  rfl

theorem cell22_2576721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 9].length) (baseStart_2576721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576721 prefixEnd_2576721 := by exact prefixLift 2576721
  have htrace : WordTrace (prefixWord ++ tailWord_2576721) baseStart_2576721 baseEnd_2576721 := by
    simpa [prefixWord, tailWord_2576721, baseEnd_2576721] using wordTrace_append hprefix tailTrace_2576721
  have hstable : (prefixWord ++ tailWord_2576721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576721).length < 2 ^ (prefixWord ++ tailWord_2576721).sum := by decide
  have hdescent : baseEnd_2576721 < baseStart_2576721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576738 : List Nat := [3, 3, 2, 1, 1, 2, 2, 8]
def baseStart_2576738 : Nat := 118140960795 + 2576738 * 2 ^ 59
def prefixEnd_2576738 : Nat := 4983230072969 + 3 ^ 40 * 2576738 * 2
def baseEnd_2576738 : Nat := 98007786274447758105541

theorem tailTrace_2576738 : CollatzResearch.WordTrace tailWord_2576738 prefixEnd_2576738 98007786274447758105541 := by
  unfold tailWord_2576738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495338934731443164900717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62654237159283848439735245 23495338934731443164900717)
  ·
    refine ⟨8810752100524291186837769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23495338934731443164900717 8810752100524291186837769)
    ·
      refine ⟨6608064075393218390128327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8810752100524291186837769 6608064075393218390128327)
      ·
        refine ⟨9912096113089827585192491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608064075393218390128327 9912096113089827585192491)
        ·
          refine ⟨14868144169634741377788737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9912096113089827585192491 14868144169634741377788737)
          ·
            refine ⟨11151108127226056033341553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14868144169634741377788737 11151108127226056033341553)
            ·
              refine ⟨8363331095419542025006165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11151108127226056033341553 8363331095419542025006165)
              ·
                refine ⟨98007786274447758105541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8363331095419542025006165 98007786274447758105541)
                ·
                  rfl

theorem cell22_2576738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_2576738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576738 prefixEnd_2576738 := by exact prefixLift 2576738
  have htrace : WordTrace (prefixWord ++ tailWord_2576738) baseStart_2576738 baseEnd_2576738 := by
    simpa [prefixWord, tailWord_2576738, baseEnd_2576738] using wordTrace_append hprefix tailTrace_2576738
  have hstable : (prefixWord ++ tailWord_2576738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576738).length < 2 ^ (prefixWord ++ tailWord_2576738).sum := by decide
  have hdescent : baseEnd_2576738 < baseStart_2576738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576858 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_2576858 : Nat := 118140960795 + 2576858 * 2 ^ 59
def prefixEnd_2576858 : Nat := 4983230072969 + 3 ^ 40 * 2576858 * 2
def baseEnd_2576858 : Nat := 882111154922389509949501

theorem tailTrace_2576858 : CollatzResearch.WordTrace tailWord_2576858 prefixEnd_2576858 882111154922389509949501 := by
  unfold tailWord_2576858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23496433124622758288492807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62657154998994022102647485 23496433124622758288492807)
  ·
    refine ⟨35244649686934137432739211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23496433124622758288492807 35244649686934137432739211)
    ·
      refine ⟨52866974530401206149108817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35244649686934137432739211 52866974530401206149108817)
      ·
        refine ⟨39650230897800904611831613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52866974530401206149108817 39650230897800904611831613)
        ·
          refine ⟨14868836586675339229436855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39650230897800904611831613 14868836586675339229436855)
          ·
            refine ⟨22303254880013008844155283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868836586675339229436855 22303254880013008844155283)
            ·
              refine ⟨33454882320019513266232925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22303254880013008844155283 33454882320019513266232925)
              ·
                refine ⟨12545580870007317474837347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33454882320019513266232925 12545580870007317474837347)
                ·
                  refine ⟨18818371305010976212256021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545580870007317474837347 18818371305010976212256021)
                  ·
                    refine ⟨882111154922389509949501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18818371305010976212256021 882111154922389509949501)
                    ·
                      rfl

theorem cell22_2576858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_2576858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576858 prefixEnd_2576858 := by exact prefixLift 2576858
  have htrace : WordTrace (prefixWord ++ tailWord_2576858) baseStart_2576858 baseEnd_2576858 := by
    simpa [prefixWord, tailWord_2576858, baseEnd_2576858] using wordTrace_append hprefix tailTrace_2576858
  have hstable : (prefixWord ++ tailWord_2576858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576858).length < 2 ^ (prefixWord ++ tailWord_2576858).sum := by decide
  have hdescent : baseEnd_2576858 < baseStart_2576858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576877 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2576877 : Nat := 118140960795 + 2576877 * 2 ^ 59
def prefixEnd_2576877 : Nat := 4983230072969 + 3 ^ 40 * 2576877 * 2
def baseEnd_2576877 : Nat := 882117659010679793724443

theorem tailTrace_2576877 : CollatzResearch.WordTrace tailWord_2576877 prefixEnd_2576877 882117659010679793724443 := by
  unfold tailWord_2576877
  simp only [CollatzResearch.WordTrace]
  refine ⟨93986425485422199398912885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62657616990281466265941923 93986425485422199398912885)
  ·
    refine ⟨8811227389258331193648083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93986425485422199398912885 8811227389258331193648083)
    ·
      refine ⟨13216841083887496790472125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8811227389258331193648083 13216841083887496790472125)
      ·
        refine ⟨4956315406457811296427047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13216841083887496790472125 4956315406457811296427047)
        ·
          refine ⟨7434473109686716944640571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956315406457811296427047 7434473109686716944640571)
          ·
            refine ⟨11151709664530075416960857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434473109686716944640571 11151709664530075416960857)
            ·
              refine ⟨8363782248397556562720643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11151709664530075416960857 8363782248397556562720643)
              ·
                refine ⟨12545673372596334844080965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363782248397556562720643 12545673372596334844080965)
                ·
                  refine ⟨2352313757361812783265181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12545673372596334844080965 2352313757361812783265181)
                  ·
                    refine ⟨882117659010679793724443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352313757361812783265181 882117659010679793724443)
                    ·
                      rfl

theorem cell22_2576877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2576877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576877 prefixEnd_2576877 := by exact prefixLift 2576877
  have htrace : WordTrace (prefixWord ++ tailWord_2576877) baseStart_2576877 baseEnd_2576877 := by
    simpa [prefixWord, tailWord_2576877, baseEnd_2576877] using wordTrace_append hprefix tailTrace_2576877
  have hstable : (prefixWord ++ tailWord_2576877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576877).length < 2 ^ (prefixWord ++ tailWord_2576877).sum := by decide
  have hdescent : baseEnd_2576877 < baseStart_2576877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576909 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2576909 : Nat := 118140960795 + 2576909 * 2 ^ 59
def prefixEnd_2576909 : Nat := 4983230072969 + 3 ^ 40 * 2576909 * 2
def baseEnd_2576909 : Nat := 882128613264642376924345

theorem tailTrace_2576909 : CollatzResearch.WordTrace tailWord_2576909 prefixEnd_2576909 882128613264642376924345 := by
  unfold tailWord_2576909
  simp only [CollatzResearch.WordTrace]
  refine ⟨93987592621306268864077781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62658395080870845909385187 93987592621306268864077781)
  ·
    refine ⟨2202834202061865676501823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 93987592621306268864077781 2202834202061865676501823)
    ·
      refine ⟨3304251303092798514752735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202834202061865676501823 3304251303092798514752735)
      ·
        refine ⟨4956376954639197772129103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304251303092798514752735 4956376954639197772129103)
        ·
          refine ⟨7434565431958796658193655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956376954639197772129103 7434565431958796658193655)
          ·
            refine ⟨11151848147938194987290483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434565431958796658193655 11151848147938194987290483)
            ·
              refine ⟨16727772221907292480935725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151848147938194987290483 16727772221907292480935725)
              ·
                refine ⟨6272914583215234680350897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16727772221907292480935725 6272914583215234680350897)
                ·
                  refine ⟨4704685937411426010263173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272914583215234680350897 4704685937411426010263173)
                  ·
                    refine ⟨882128613264642376924345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704685937411426010263173 882128613264642376924345)
                    ·
                      rfl

theorem cell22_2576909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2576909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576909 prefixEnd_2576909 := by exact prefixLift 2576909
  have htrace : WordTrace (prefixWord ++ tailWord_2576909) baseStart_2576909 baseEnd_2576909 := by
    simpa [prefixWord, tailWord_2576909, baseEnd_2576909] using wordTrace_append hprefix tailTrace_2576909
  have hstable : (prefixWord ++ tailWord_2576909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576909).length < 2 ^ (prefixWord ++ tailWord_2576909).sum := by decide
  have hdescent : baseEnd_2576909 < baseStart_2576909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576941 : List Nat := [1, 5, 4, 1, 1, 2, 1, 7]
def baseStart_2576941 : Nat := 118140960795 + 2576941 * 2 ^ 59
def prefixEnd_2576941 : Nat := 4983230072969 + 3 ^ 40 * 2576941 * 2
def baseEnd_2576941 : Nat := 98015507502067217791583

theorem tailTrace_2576941 : CollatzResearch.WordTrace tailWord_2576941 prefixEnd_2576941 98015507502067217791583 := by
  unfold tailWord_2576941
  simp only [CollatzResearch.WordTrace]
  refine ⟨93988759757190338329242677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62659173171460225552828451 93988759757190338329242677)
  ·
    refine ⟨8811446227236594218366501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93988759757190338329242677 8811446227236594218366501)
    ·
      refine ⟨1652146167606861415943719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8811446227236594218366501 1652146167606861415943719)
      ·
        refine ⟨2478219251410292123915579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652146167606861415943719 2478219251410292123915579)
        ·
          refine ⟨3717328877115438185873369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478219251410292123915579 3717328877115438185873369)
          ·
            refine ⟨2787996657836578639405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3717328877115438185873369 2787996657836578639405027)
            ·
              refine ⟨4181994986754867959107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787996657836578639405027 4181994986754867959107541)
              ·
                refine ⟨98015507502067217791583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4181994986754867959107541 98015507502067217791583)
                ·
                  rfl

theorem cell22_2576941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 7].length) (baseStart_2576941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576941 prefixEnd_2576941 := by exact prefixLift 2576941
  have htrace : WordTrace (prefixWord ++ tailWord_2576941) baseStart_2576941 baseEnd_2576941 := by
    simpa [prefixWord, tailWord_2576941, baseEnd_2576941] using wordTrace_append hprefix tailTrace_2576941
  have hstable : (prefixWord ++ tailWord_2576941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576941).length < 2 ^ (prefixWord ++ tailWord_2576941).sum := by decide
  have hdescent : baseEnd_2576941 < baseStart_2576941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576965 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2576965 : Nat := 118140960795 + 2576965 * 2 ^ 59
def prefixEnd_2576965 : Nat := 4983230072969 + 3 ^ 40 * 2576965 * 2
def baseEnd_2576965 : Nat := 882147783209076897524173

theorem tailTrace_2576965 : CollatzResearch.WordTrace tailWord_2576965 prefixEnd_2576965 882147783209076897524173 := by
  unfold tailWord_2576965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93989635109103390428116349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62659756739402260285410899 93989635109103390428116349)
  ·
    refine ⟨35246113165913771410543631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93989635109103390428116349 35246113165913771410543631)
    ·
      refine ⟨52869169748870657115815447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35246113165913771410543631 52869169748870657115815447)
      ·
        refine ⟨79303754623305985673723171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52869169748870657115815447 79303754623305985673723171)
        ·
          refine ⟨118955631934958978510584757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79303754623305985673723171 118955631934958978510584757)
          ·
            refine ⟨11152090493902404235367321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118955631934958978510584757 11152090493902404235367321)
            ·
              refine ⟨8364067870426803176525491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11152090493902404235367321 8364067870426803176525491)
              ·
                refine ⟨12546101805640204764788237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364067870426803176525491 12546101805640204764788237)
                ·
                  refine ⟨4704788177115076786795589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12546101805640204764788237 4704788177115076786795589)
                  ·
                    refine ⟨882147783209076897524173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704788177115076786795589 882147783209076897524173)
                    ·
                      rfl

theorem cell22_2576965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2576965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576965 prefixEnd_2576965 := by exact prefixLift 2576965
  have htrace : WordTrace (prefixWord ++ tailWord_2576965) baseStart_2576965 baseEnd_2576965 := by
    simpa [prefixWord, tailWord_2576965, baseEnd_2576965] using wordTrace_append hprefix tailTrace_2576965
  have hstable : (prefixWord ++ tailWord_2576965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576965).length < 2 ^ (prefixWord ++ tailWord_2576965).sum := by decide
  have hdescent : baseEnd_2576965 < baseStart_2576965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2576997 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2576997 : Nat := 118140960795 + 2576997 * 2 ^ 59
def prefixEnd_2576997 : Nat := 4983230072969 + 3 ^ 40 * 2576997 * 2
def baseEnd_2576997 : Nat := 294052912487679826908025

theorem tailTrace_2576997 : CollatzResearch.WordTrace tailWord_2576997 prefixEnd_2576997 294052912487679826908025 := by
  unfold tailWord_2576997
  simp only [CollatzResearch.WordTrace]
  refine ⟨93990802244987459893281245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62660534829991639928854163 93990802244987459893281245)
  ·
    refine ⟨35246550841870297459980467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93990802244987459893281245 35246550841870297459980467)
    ·
      refine ⟨52869826262805446189970701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35246550841870297459980467 52869826262805446189970701)
      ·
        refine ⟨19826184848552042321239013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52869826262805446189970701 19826184848552042321239013)
        ·
          refine ⟨3717409659103507935232315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19826184848552042321239013 3717409659103507935232315)
          ·
            refine ⟨5576114488655261902848473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717409659103507935232315 5576114488655261902848473)
            ·
              refine ⟨4182085866491446427136355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576114488655261902848473 4182085866491446427136355)
              ·
                refine ⟨6273128799737169640704533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182085866491446427136355 6273128799737169640704533)
                ·
                  refine ⟨294052912487679826908025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6273128799737169640704533 294052912487679826908025)
                  ·
                    rfl

theorem cell22_2576997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2576997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2576997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2576997 prefixEnd_2576997 := by exact prefixLift 2576997
  have htrace : WordTrace (prefixWord ++ tailWord_2576997) baseStart_2576997 baseEnd_2576997 := by
    simpa [prefixWord, tailWord_2576997, baseEnd_2576997] using wordTrace_append hprefix tailTrace_2576997
  have hstable : (prefixWord ++ tailWord_2576997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2576997).length < 2 ^ (prefixWord ++ tailWord_2576997).sum := by decide
  have hdescent : baseEnd_2576997 < baseStart_2576997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2576997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577025 : List Nat := [1, 2, 4, 2, 1, 1, 3, 8]
def baseStart_2577025 : Nat := 118140960795 + 2577025 * 2 ^ 59
def prefixEnd_2577025 : Nat := 4983230072969 + 3 ^ 40 * 2577025 * 2
def baseEnd_2577025 : Nat := 98018702492806304558221

theorem tailTrace_2577025 : CollatzResearch.WordTrace tailWord_2577025 prefixEnd_2577025 98018702492806304558221 := by
  unfold tailWord_2577025
  simp only [CollatzResearch.WordTrace]
  refine ⟨93991823488886020675300529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62661215659257347116867019 93991823488886020675300529)
  ·
    refine ⟨70493867616664515506475397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93991823488886020675300529 70493867616664515506475397)
    ·
      refine ⟨13217600178124596657464137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70493867616664515506475397 13217600178124596657464137)
      ·
        refine ⟨9913200133593447493098103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13217600178124596657464137 9913200133593447493098103)
        ·
          refine ⟨14869800200390171239647155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9913200133593447493098103 14869800200390171239647155)
          ·
            refine ⟨22304700300585256859470733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14869800200390171239647155 22304700300585256859470733)
            ·
              refine ⟨8364262612719471322301525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22304700300585256859470733 8364262612719471322301525)
              ·
                refine ⟨98018702492806304558221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8364262612719471322301525 98018702492806304558221)
                ·
                  rfl

theorem cell22_2577025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 8].length) (baseStart_2577025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577025 prefixEnd_2577025 := by exact prefixLift 2577025
  have htrace : WordTrace (prefixWord ++ tailWord_2577025) baseStart_2577025 baseEnd_2577025 := by
    simpa [prefixWord, tailWord_2577025, baseEnd_2577025] using wordTrace_append hprefix tailTrace_2577025
  have hstable : (prefixWord ++ tailWord_2577025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577025).length < 2 ^ (prefixWord ++ tailWord_2577025).sum := by decide
  have hdescent : baseEnd_2577025 < baseStart_2577025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577042 : List Nat := [3, 2, 3, 1, 2, 3, 8]
def baseStart_2577042 : Nat := 118140960795 + 2577042 * 2 ^ 59
def prefixEnd_2577042 : Nat := 4983230072969 + 3 ^ 40 * 2577042 * 2
def baseEnd_2577042 : Nat := 32673116366024976420331

theorem tailTrace_2577042 : CollatzResearch.WordTrace tailWord_2577042 prefixEnd_2577042 32673116366024976420331 := by
  unfold tailWord_2577042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23498110882456108144667345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62661629019882955052446253 23498110882456108144667345)
  ·
    refine ⟨17623583161842081108500509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23498110882456108144667345 17623583161842081108500509)
    ·
      refine ⟨6608843685690780415687691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17623583161842081108500509 6608843685690780415687691)
      ·
        refine ⟨9913265528536170623531537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608843685690780415687691 9913265528536170623531537)
        ·
          refine ⟨7434949146402127967648653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9913265528536170623531537 7434949146402127967648653)
          ·
            refine ⟨2788105929900797987868245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7434949146402127967648653 2788105929900797987868245)
            ·
              refine ⟨32673116366024976420331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2788105929900797987868245 32673116366024976420331)
              ·
                rfl

theorem cell22_2577042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 8].length) (baseStart_2577042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577042 prefixEnd_2577042 := by exact prefixLift 2577042
  have htrace : WordTrace (prefixWord ++ tailWord_2577042) baseStart_2577042 baseEnd_2577042 := by
    simpa [prefixWord, tailWord_2577042, baseEnd_2577042] using wordTrace_append hprefix tailTrace_2577042
  have hstable : (prefixWord ++ tailWord_2577042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577042).length < 2 ^ (prefixWord ++ tailWord_2577042).sum := by decide
  have hdescent : baseEnd_2577042 < baseStart_2577042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577044 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2577044 : Nat := 118140960795 + 2577044 * 2 ^ 59
def prefixEnd_2577044 : Nat := 4983230072969 + 3 ^ 40 * 2577044 * 2
def baseEnd_2577044 : Nat := 882174826523547024798931

theorem tailTrace_2577044 : CollatzResearch.WordTrace tailWord_2577044 prefixEnd_2577044 882174826523547024798931 := by
  unfold tailWord_2577044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46996258237908593460121093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62661677650544791280161457 46996258237908593460121093)
  ·
    refine ⟨8811798419607861273772705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46996258237908593460121093 8811798419607861273772705)
    ·
      refine ⟨6608848814705895955329529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811798419607861273772705 6608848814705895955329529)
      ·
        refine ⟨4956636611029421966497147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6608848814705895955329529 4956636611029421966497147)
        ·
          refine ⟨7434954916544132949745721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956636611029421966497147 7434954916544132949745721)
          ·
            refine ⟨5576216187408099712309291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7434954916544132949745721 5576216187408099712309291)
            ·
              refine ⟨8364324281112149568463937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576216187408099712309291 8364324281112149568463937)
              ·
                refine ⟨6273243210834112176347953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8364324281112149568463937 6273243210834112176347953)
                ·
                  refine ⟨4704932408125584132260965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6273243210834112176347953 4704932408125584132260965)
                  ·
                    refine ⟨882174826523547024798931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704932408125584132260965 882174826523547024798931)
                    ·
                      rfl

theorem cell22_2577044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2577044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577044 prefixEnd_2577044 := by exact prefixLift 2577044
  have htrace : WordTrace (prefixWord ++ tailWord_2577044) baseStart_2577044 baseEnd_2577044 := by
    simpa [prefixWord, tailWord_2577044, baseEnd_2577044] using wordTrace_append hprefix tailTrace_2577044
  have hstable : (prefixWord ++ tailWord_2577044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577044).length < 2 ^ (prefixWord ++ tailWord_2577044).sum := by decide
  have hdescent : baseEnd_2577044 < baseStart_2577044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577108 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2577108 : Nat := 118140960795 + 2577108 * 2 ^ 59
def prefixEnd_2577108 : Nat := 4983230072969 + 3 ^ 40 * 2577108 * 2
def baseEnd_2577108 : Nat := 882196735031472191198735

theorem tailTrace_2577108 : CollatzResearch.WordTrace tailWord_2577108 prefixEnd_2577108 882196735031472191198735 := by
  unfold tailWord_2577108
  simp only [CollatzResearch.WordTrace]
  refine ⟨46997425373792662925285989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62663233831723550567047985 46997425373792662925285989)
  ·
    refine ⟨8812017257586124298491123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46997425373792662925285989 8812017257586124298491123)
    ·
      refine ⟨13218025886379186447736685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812017257586124298491123 13218025886379186447736685)
      ·
        refine ⟨4956759707392194917901257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13218025886379186447736685 4956759707392194917901257)
        ·
          refine ⟨3717569780544146188425943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4956759707392194917901257 3717569780544146188425943)
          ·
            refine ⟨5576354670816219282638915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717569780544146188425943 5576354670816219282638915)
            ·
              refine ⟨8364532006224328923958373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576354670816219282638915 8364532006224328923958373)
              ·
                refine ⟨1568349751167061673242195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8364532006224328923958373 1568349751167061673242195)
                ·
                  refine ⟨2352524626750592509863293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568349751167061673242195 2352524626750592509863293)
                  ·
                    refine ⟨882196735031472191198735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2352524626750592509863293 882196735031472191198735)
                    ·
                      rfl

theorem cell22_2577108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2577108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577108 prefixEnd_2577108 := by exact prefixLift 2577108
  have htrace : WordTrace (prefixWord ++ tailWord_2577108) baseStart_2577108 baseEnd_2577108 := by
    simpa [prefixWord, tailWord_2577108, baseEnd_2577108] using wordTrace_append hprefix tailTrace_2577108
  have hstable : (prefixWord ++ tailWord_2577108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577108).length < 2 ^ (prefixWord ++ tailWord_2577108).sum := by decide
  have hdescent : baseEnd_2577108 < baseStart_2577108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577149 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2577149 : Nat := 118140960795 + 2577149 * 2 ^ 59
def prefixEnd_2577149 : Nat := 4983230072969 + 3 ^ 40 * 2577149 * 2
def baseEnd_2577149 : Nat := 294070256723120583641203

theorem tailTrace_2577149 : CollatzResearch.WordTrace tailWord_2577149 prefixEnd_2577149 294070256723120583641203 := by
  unfold tailWord_2577149
  simp only [CollatzResearch.WordTrace]
  refine ⟨93996346140436789852814501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62664230760291193235209667 93996346140436789852814501)
  ·
    refine ⟨17624314901331898097402719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93996346140436789852814501 17624314901331898097402719)
    ·
      refine ⟨26436472351997847146104079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17624314901331898097402719 26436472351997847146104079)
      ·
        refine ⟨39654708527996770719156119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26436472351997847146104079 39654708527996770719156119)
        ·
          refine ⟨59482062791995156078734179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39654708527996770719156119 59482062791995156078734179)
          ·
            refine ⟨89223094187992734118101269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59482062791995156078734179 89223094187992734118101269)
            ·
              refine ⟨4182332540062159411785997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89223094187992734118101269 4182332540062159411785997)
              ·
                refine ⟨1568374702523309779419749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4182332540062159411785997 1568374702523309779419749)
                ·
                  refine ⟨294070256723120583641203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568374702523309779419749 294070256723120583641203)
                  ·
                    rfl

theorem cell22_2577149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2577149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577149 prefixEnd_2577149 := by exact prefixLift 2577149
  have htrace : WordTrace (prefixWord ++ tailWord_2577149) baseStart_2577149 baseEnd_2577149 := by
    simpa [prefixWord, tailWord_2577149, baseEnd_2577149] using wordTrace_append hprefix tailTrace_2577149
  have hstable : (prefixWord ++ tailWord_2577149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577149).length < 2 ^ (prefixWord ++ tailWord_2577149).sum := by decide
  have hdescent : baseEnd_2577149 < baseStart_2577149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577162 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2577162 : Nat := 118140960795 + 2577162 * 2 ^ 59
def prefixEnd_2577162 : Nat := 4983230072969 + 3 ^ 40 * 2577162 * 2
def baseEnd_2577162 : Nat := 882215220335034050348569

theorem tailTrace_2577162 : CollatzResearch.WordTrace tailWord_2577162 prefixEnd_2577162 882215220335034050348569 := by
  unfold tailWord_2577162
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499205072347423268259435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62664546859593128715358493 23499205072347423268259435)
  ·
    refine ⟨35248807608521134902389153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23499205072347423268259435 35248807608521134902389153)
    ·
      refine ⟨26436605706390851176791865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35248807608521134902389153 26436605706390851176791865)
      ·
        refine ⟨19827454279793138382593899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26436605706390851176791865 19827454279793138382593899)
        ·
          refine ⟨29741181419689707573890849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827454279793138382593899 29741181419689707573890849)
          ·
            refine ⟨22305886064767280680418137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29741181419689707573890849 22305886064767280680418137)
            ·
              refine ⟨16729414548575460510313603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22305886064767280680418137 16729414548575460510313603)
              ·
                refine ⟨25094121822863190765470405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16729414548575460510313603 25094121822863190765470405)
                ·
                  refine ⟨4705147841786848268525701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25094121822863190765470405 4705147841786848268525701)
                  ·
                    refine ⟨882215220335034050348569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4705147841786848268525701 882215220335034050348569)
                    ·
                      rfl

theorem cell22_2577162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2577162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577162 prefixEnd_2577162 := by exact prefixLift 2577162
  have htrace : WordTrace (prefixWord ++ tailWord_2577162) baseStart_2577162 baseEnd_2577162 := by
    simpa [prefixWord, tailWord_2577162, baseEnd_2577162] using wordTrace_append hprefix tailTrace_2577162
  have hstable : (prefixWord ++ tailWord_2577162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577162).length < 2 ^ (prefixWord ++ tailWord_2577162).sum := by decide
  have hdescent : baseEnd_2577162 < baseStart_2577162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577192 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2577192 : Nat := 118140960795 + 2577192 * 2 ^ 59
def prefixEnd_2577192 : Nat := 4983230072969 + 3 ^ 40 * 2577192 * 2
def baseEnd_2577192 : Nat := 882225489948123972098477

theorem tailTrace_2577192 : CollatzResearch.WordTrace tailWord_2577192 prefixEnd_2577192 882225489948123972098477 := by
  unfold tailWord_2577192
  simp only [CollatzResearch.WordTrace]
  refine ⟨46998957239640504098314915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62665276319520672131086553 46998957239640504098314915)
  ·
    refine ⟨70498435859460756147472373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46998957239640504098314915 70498435859460756147472373)
    ·
      refine ⟨6609228361824445888825535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70498435859460756147472373 6609228361824445888825535)
      ·
        refine ⟨9913842542736668833238303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609228361824445888825535 9913842542736668833238303)
        ·
          refine ⟨14870763814105003249857455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9913842542736668833238303 14870763814105003249857455)
          ·
            refine ⟨22306145721157504874786183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14870763814105003249857455 22306145721157504874786183)
            ·
              refine ⟨33459218581736257312179275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22306145721157504874786183 33459218581736257312179275)
              ·
                refine ⟨50188827872604385968268913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33459218581736257312179275 50188827872604385968268913)
                ·
                  refine ⟨37641620904453289476201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50188827872604385968268913 37641620904453289476201685)
                  ·
                    refine ⟨882225489948123972098477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37641620904453289476201685 882225489948123972098477)
                    ·
                      rfl

theorem cell22_2577192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2577192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577192 prefixEnd_2577192 := by exact prefixLift 2577192
  have htrace : WordTrace (prefixWord ++ tailWord_2577192) baseStart_2577192 baseEnd_2577192 := by
    simpa [prefixWord, tailWord_2577192, baseEnd_2577192] using wordTrace_append hprefix tailTrace_2577192
  have hstable : (prefixWord ++ tailWord_2577192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577192).length < 2 ^ (prefixWord ++ tailWord_2577192).sum := by decide
  have hdescent : baseEnd_2577192 < baseStart_2577192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577237 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2577237 : Nat := 118140960795 + 2577237 * 2 ^ 59
def prefixEnd_2577237 : Nat := 4983230072969 + 3 ^ 40 * 2577237 * 2
def baseEnd_2577237 : Nat := 882240894367758854723339

theorem tailTrace_2577237 : CollatzResearch.WordTrace tailWord_2577237 prefixEnd_2577237 882240894367758854723339 := by
  unfold tailWord_2577237
  simp only [CollatzResearch.WordTrace]
  refine ⟨93999555764117980882017965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62666370509411987254678643 93999555764117980882017965)
  ·
    refine ⟨35249833411544242830756737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93999555764117980882017965 35249833411544242830756737)
    ·
      refine ⟨26437375058658182123067553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35249833411544242830756737 26437375058658182123067553)
      ·
        refine ⟨19828031293993636592300665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26437375058658182123067553 19828031293993636592300665)
        ·
          refine ⟨14871023470495227444225499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19828031293993636592300665 14871023470495227444225499)
          ·
            refine ⟨22306535205742841166338249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14871023470495227444225499 22306535205742841166338249)
            ·
              refine ⟨16729901404307130874753687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22306535205742841166338249 16729901404307130874753687)
              ·
                refine ⟨25094852106460696312130531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16729901404307130874753687 25094852106460696312130531)
                ·
                  refine ⟨37642278159691044468195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25094852106460696312130531 37642278159691044468195797)
                  ·
                    refine ⟨882240894367758854723339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37642278159691044468195797 882240894367758854723339)
                    ·
                      rfl

theorem cell22_2577237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2577237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577237 prefixEnd_2577237 := by exact prefixLift 2577237
  have htrace : WordTrace (prefixWord ++ tailWord_2577237) baseStart_2577237 baseEnd_2577237 := by
    simpa [prefixWord, tailWord_2577237, baseEnd_2577237] using wordTrace_append hprefix tailTrace_2577237
  have hstable : (prefixWord ++ tailWord_2577237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577237).length < 2 ^ (prefixWord ++ tailWord_2577237).sum := by decide
  have hdescent : baseEnd_2577237 < baseStart_2577237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577239 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 5]
def baseStart_2577239 : Nat := 118140960795 + 2577239 * 2 ^ 59
def prefixEnd_2577239 : Nat := 4983230072969 + 3 ^ 40 * 2577239 * 2
def baseEnd_2577239 : Nat := 294080526336210505391111

theorem tailTrace_2577239 : CollatzResearch.WordTrace tailWord_2577239 prefixEnd_2577239 294080526336210505391111 := by
  unfold tailWord_2577239
  simp only [CollatzResearch.WordTrace]
  refine ⟨93999628710110735223590771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62666419140073823482393847 93999628710110735223590771)
  ·
    refine ⟨140999443065166102835386157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93999628710110735223590771 140999443065166102835386157)
    ·
      refine ⟨52874791149437288563269809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140999443065166102835386157 52874791149437288563269809)
      ·
        refine ⟨39656093362077966422452357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52874791149437288563269809 39656093362077966422452357)
        ·
          refine ⟨7435517505389618704209817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39656093362077966422452357 7435517505389618704209817)
          ·
            refine ⟨5576638129042214028157363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7435517505389618704209817 5576638129042214028157363)
            ·
              refine ⟨8364957193563321042236045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576638129042214028157363 8364957193563321042236045)
              ·
                refine ⟨3136858947586245390838517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8364957193563321042236045 3136858947586245390838517)
                ·
                  refine ⟨294080526336210505391111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3136858947586245390838517 294080526336210505391111)
                  ·
                    rfl

theorem cell22_2577239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 5].length) (baseStart_2577239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577239 prefixEnd_2577239 := by exact prefixLift 2577239
  have htrace : WordTrace (prefixWord ++ tailWord_2577239) baseStart_2577239 baseEnd_2577239 := by
    simpa [prefixWord, tailWord_2577239, baseEnd_2577239] using wordTrace_append hprefix tailTrace_2577239
  have hstable : (prefixWord ++ tailWord_2577239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577239).length < 2 ^ (prefixWord ++ tailWord_2577239).sum := by decide
  have hdescent : baseEnd_2577239 < baseStart_2577239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2577297 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2577297 : Nat := 118140960795 + 2577297 * 2 ^ 59
def prefixEnd_2577297 : Nat := 4983230072969 + 3 ^ 40 * 2577297 * 2
def baseEnd_2577297 : Nat := 882261433593938698223155

theorem tailTrace_2577297 : CollatzResearch.WordTrace tailWord_2577297 prefixEnd_2577297 882261433593938698223155 := by
  unfold tailWord_2577297
  simp only [CollatzResearch.WordTrace]
  refine ⟨94001744143900611129202145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62667829429267074086134763 94001744143900611129202145)
  ·
    refine ⟨70501308107925458346901609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94001744143900611129202145 70501308107925458346901609)
    ·
      refine ⟨52875981080944093760176207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70501308107925458346901609 52875981080944093760176207)
      ·
        refine ⟨79313971621416140640264311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52875981080944093760176207 79313971621416140640264311)
        ·
          refine ⟨118970957432124210960396467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79313971621416140640264311 118970957432124210960396467)
          ·
            refine ⟨178456436148186316440594701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118970957432124210960396467 178456436148186316440594701)
            ·
              refine ⟨66921163555569868665223013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178456436148186316440594701 66921163555569868665223013)
              ·
                refine ⟨12547718166669350374729315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66921163555569868665223013 12547718166669350374729315)
                ·
                  refine ⟨18821577250004025562093973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12547718166669350374729315 18821577250004025562093973)
                  ·
                    refine ⟨882261433593938698223155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18821577250004025562093973 882261433593938698223155)
                    ·
                      rfl

theorem cell22_2577297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2577297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2577297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2577297 prefixEnd_2577297 := by exact prefixLift 2577297
  have htrace : WordTrace (prefixWord ++ tailWord_2577297) baseStart_2577297 baseEnd_2577297 := by
    simpa [prefixWord, tailWord_2577297, baseEnd_2577297] using wordTrace_append hprefix tailTrace_2577297
  have hstable : (prefixWord ++ tailWord_2577297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2577297).length < 2 ^ (prefixWord ++ tailWord_2577297).sum := by decide
  have hdescent : baseEnd_2577297 < baseStart_2577297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2577297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
