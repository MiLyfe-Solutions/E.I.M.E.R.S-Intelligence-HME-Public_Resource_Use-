import V185TrunkScan21Chunk000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_12092 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_12092 : Nat := 118140960795 + 12092 * 2 ^ 59
def prefixEnd_12092 : Nat := 4983230072969 + 3 ^ 40 * 12092 * 2
def baseEnd_12092 : Nat := 2759559144120854975287

theorem tailTrace_12092 : CollatzResearch.WordTrace tailWord_12092 prefixEnd_12092 2759559144120854975287 := by
  unfold tailWord_12092
  simp only [CollatzResearch.WordTrace]
  refine ⟨220515736100111997147265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 294020981466815996196353 220515736100111997147265)
  ·
    refine ⟨165386802075083997860449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220515736100111997147265 165386802075083997860449)
    ·
      refine ⟨124040101556312998395337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165386802075083997860449 124040101556312998395337)
      ·
        refine ⟨93030076167234748796503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124040101556312998395337 93030076167234748796503)
        ·
          refine ⟨139545114250852123194755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93030076167234748796503 139545114250852123194755)
          ·
            refine ⟨209317671376278184792133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139545114250852123194755 209317671376278184792133)
            ·
              refine ⟨39247063383052159648525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209317671376278184792133 39247063383052159648525)
              ·
                refine ⟨14717648768644559868197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39247063383052159648525 14717648768644559868197)
                ·
                  refine ⟨2759559144120854975287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14717648768644559868197 2759559144120854975287)
                  ·
                    rfl

theorem cell21_12092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_12092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12092 prefixEnd_12092 := by exact prefixLift 12092
  have htrace : WordTrace (prefixWord ++ tailWord_12092) baseStart_12092 baseEnd_12092 := by
    simpa [prefixWord, tailWord_12092, baseEnd_12092] using wordTrace_append hprefix tailTrace_12092
  have hstable : (prefixWord ++ tailWord_12092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12092).length < 2 ^ (prefixWord ++ tailWord_12092).sum := by decide
  have hdescent : baseEnd_12092 < baseStart_12092 := by decide
  rcases family_descends (prefixWord ++ tailWord_12092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12188 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_12188 : Nat := 118140960795 + 12188 * 2 ^ 59
def prefixEnd_12188 : Nat := 4983230072969 + 3 ^ 40 * 12188 * 2
def baseEnd_12188 : Nat := 2781467652046021375091

theorem tailTrace_12188 : CollatzResearch.WordTrace tailWord_12188 prefixEnd_12188 2781467652046021375091 := by
  unfold tailWord_12188
  simp only [CollatzResearch.WordTrace]
  refine ⟨222266439926216194894609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 296355253234954926526145 222266439926216194894609)
  ·
    refine ⟨166699829944662146170957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222266439926216194894609 166699829944662146170957)
    ·
      refine ⟨62512436229248304814109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166699829944662146170957 62512436229248304814109)
      ·
        refine ⟨23442163585968114305291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62512436229248304814109 23442163585968114305291)
        ·
          refine ⟨35163245378952171457937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23442163585968114305291 35163245378952171457937)
          ·
            refine ⟨26372434034214128593453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35163245378952171457937 26372434034214128593453)
            ·
              refine ⟨9889662762830298222545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26372434034214128593453 9889662762830298222545)
              ·
                refine ⟨7417247072122723666909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9889662762830298222545 7417247072122723666909)
                ·
                  refine ⟨2781467652046021375091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7417247072122723666909 2781467652046021375091)
                  ·
                    rfl

theorem cell21_12188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_12188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12188 prefixEnd_12188 := by exact prefixLift 12188
  have htrace : WordTrace (prefixWord ++ tailWord_12188) baseStart_12188 baseEnd_12188 := by
    simpa [prefixWord, tailWord_12188, baseEnd_12188] using wordTrace_append hprefix tailTrace_12188
  have hstable : (prefixWord ++ tailWord_12188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12188).length < 2 ^ (prefixWord ++ tailWord_12188).sum := by decide
  have hdescent : baseEnd_12188 < baseStart_12188 := by decide
  rcases family_descends (prefixWord ++ tailWord_12188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12199 : List Nat := [1, 1, 6, 1, 2, 2, 2, 6]
def baseStart_12199 : Nat := 118140960795 + 12199 * 2 ^ 59
def prefixEnd_12199 : Nat := 4983230072969 + 3 ^ 40 * 12199 * 2
def baseEnd_12199 : Nat := 927992667304148897245

theorem tailTrace_12199 : CollatzResearch.WordTrace tailWord_12199 prefixEnd_12199 927992667304148897245 := by
  unfold tailWord_12199
  simp only [CollatzResearch.WordTrace]
  refine ⟨444934082812581268439651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 296622721875054178959767 444934082812581268439651)
  ·
    refine ⟨667401124218871902659477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444934082812581268439651 667401124218871902659477)
    ·
      refine ⟨31284427697759620437163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 667401124218871902659477 31284427697759620437163)
      ·
        refine ⟨46926641546639430655745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31284427697759620437163 46926641546639430655745)
        ·
          refine ⟨35194981159979572991809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46926641546639430655745 35194981159979572991809)
          ·
            refine ⟨26396235869984679743857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35194981159979572991809 26396235869984679743857)
            ·
              refine ⟨19797176902488509807893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26396235869984679743857 19797176902488509807893)
              ·
                refine ⟨927992667304148897245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19797176902488509807893 927992667304148897245)
                ·
                  rfl

theorem cell21_12199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_12199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12199 prefixEnd_12199 := by exact prefixLift 12199
  have htrace : WordTrace (prefixWord ++ tailWord_12199) baseStart_12199 baseEnd_12199 := by
    simpa [prefixWord, tailWord_12199, baseEnd_12199] using wordTrace_append hprefix tailTrace_12199
  have hstable : (prefixWord ++ tailWord_12199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12199).length < 2 ^ (prefixWord ++ tailWord_12199).sum := by decide
  have hdescent : baseEnd_12199 < baseStart_12199 := by decide
  rcases family_descends (prefixWord ++ tailWord_12199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12272 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_12272 : Nat := 118140960795 + 12272 * 2 ^ 59
def prefixEnd_12272 : Nat := 4983230072969 + 3 ^ 40 * 12272 * 2
def baseEnd_12272 : Nat := 2800637596480541974919

theorem tailTrace_12272 : CollatzResearch.WordTrace tailWord_12272 prefixEnd_12272 2800637596480541974919 := by
  unfold tailWord_12272
  simp only [CollatzResearch.WordTrace]
  refine ⟨223798305774057367923535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 298397741032076490564713 223798305774057367923535)
  ·
    refine ⟨335697458661086051885303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223798305774057367923535 335697458661086051885303)
    ·
      refine ⟨503546187991629077827955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335697458661086051885303 503546187991629077827955)
      ·
        refine ⟨755319281987443616741933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503546187991629077827955 755319281987443616741933)
        ·
          refine ⟨283244730745291356278225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755319281987443616741933 283244730745291356278225)
          ·
            refine ⟨212433548058968517208669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283244730745291356278225 212433548058968517208669)
            ·
              refine ⟨79662580522113193953251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212433548058968517208669 79662580522113193953251)
              ·
                refine ⟨119493870783169790929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79662580522113193953251 119493870783169790929877)
                ·
                  refine ⟨2800637596480541974919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119493870783169790929877 2800637596480541974919)
                  ·
                    rfl

theorem cell21_12272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_12272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12272 prefixEnd_12272 := by exact prefixLift 12272
  have htrace : WordTrace (prefixWord ++ tailWord_12272) baseStart_12272 baseEnd_12272 := by
    simpa [prefixWord, tailWord_12272, baseEnd_12272] using wordTrace_append hprefix tailTrace_12272
  have hstable : (prefixWord ++ tailWord_12272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12272).length < 2 ^ (prefixWord ++ tailWord_12272).sum := by decide
  have hdescent : baseEnd_12272 < baseStart_12272 := by decide
  rcases family_descends (prefixWord ++ tailWord_12272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12393 : List Nat := [1, 2, 1, 1, 1, 5, 1, 9]
def baseStart_12393 : Nat := 118140960795 + 12393 * 2 ^ 59
def prefixEnd_12393 : Nat := 4983230072969 + 3 ^ 40 * 12393 * 2
def baseEnd_12393 : Nat := 942750481670406819335

theorem tailTrace_12393 : CollatzResearch.WordTrace tailWord_12393 prefixEnd_12393 942750481670406819335 := by
  unfold tailWord_12393
  simp only [CollatzResearch.WordTrace]
  refine ⟨452009844109752401001833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 301339896073168267334555 452009844109752401001833)
  ·
    refine ⟨339007383082314300751375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 452009844109752401001833 339007383082314300751375)
    ·
      refine ⟨508511074623471451127063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339007383082314300751375 508511074623471451127063)
      ·
        refine ⟨762766611935207176690595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508511074623471451127063 762766611935207176690595)
        ·
          refine ⟨1144149917902810765035893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762766611935207176690595 1144149917902810765035893)
          ·
            refine ⟨107264054803388509222115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1144149917902810765035893 107264054803388509222115)
            ·
              refine ⟨160896082205082763833173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107264054803388509222115 160896082205082763833173)
              ·
                refine ⟨942750481670406819335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 160896082205082763833173 942750481670406819335)
                ·
                  rfl

theorem cell21_12393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_12393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12393 prefixEnd_12393 := by exact prefixLift 12393
  have htrace : WordTrace (prefixWord ++ tailWord_12393) baseStart_12393 baseEnd_12393 := by
    simpa [prefixWord, tailWord_12393, baseEnd_12393] using wordTrace_append hprefix tailTrace_12393
  have hstable : (prefixWord ++ tailWord_12393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12393).length < 2 ^ (prefixWord ++ tailWord_12393).sum := by decide
  have hdescent : baseEnd_12393 < baseStart_12393 := by decide
  rcases family_descends (prefixWord ++ tailWord_12393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12531 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_12531 : Nat := 118140960795 + 12531 * 2 ^ 59
def prefixEnd_12531 : Nat := 4983230072969 + 3 ^ 40 * 12531 * 2
def baseEnd_12531 : Nat := 2859744925153647157723

theorem tailTrace_12531 : CollatzResearch.WordTrace tailWord_12531 prefixEnd_12531 2859744925153647157723 := by
  unfold tailWord_12531
  simp only [CollatzResearch.WordTrace]
  refine ⟨457043117609801969525447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 304695411739867979683631 457043117609801969525447)
  ·
    refine ⟨685564676414702954288171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457043117609801969525447 685564676414702954288171)
    ·
      refine ⟨1028347014622054431432257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685564676414702954288171 1028347014622054431432257)
      ·
        refine ⟨771260260966540823574193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028347014622054431432257 771260260966540823574193)
        ·
          refine ⟨578445195724905617680645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771260260966540823574193 578445195724905617680645)
          ·
            refine ⟨108458474198419803315121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578445195724905617680645 108458474198419803315121)
            ·
              refine ⟨81343855648814852486341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108458474198419803315121 81343855648814852486341)
              ·
                refine ⟨15251972934152784841189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81343855648814852486341 15251972934152784841189)
                ·
                  refine ⟨2859744925153647157723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15251972934152784841189 2859744925153647157723)
                  ·
                    rfl

theorem cell21_12531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_12531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12531 prefixEnd_12531 := by exact prefixLift 12531
  have htrace : WordTrace (prefixWord ++ tailWord_12531) baseStart_12531 baseEnd_12531 := by
    simpa [prefixWord, tailWord_12531, baseEnd_12531] using wordTrace_append hprefix tailTrace_12531
  have hstable : (prefixWord ++ tailWord_12531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12531).length < 2 ^ (prefixWord ++ tailWord_12531).sum := by decide
  have hdescent : baseEnd_12531 < baseStart_12531 := by decide
  rcases family_descends (prefixWord ++ tailWord_12531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12534 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_12534 : Nat := 118140960795 + 12534 * 2 ^ 59
def prefixEnd_12534 : Nat := 4983230072969 + 3 ^ 40 * 12534 * 2
def baseEnd_12534 : Nat := 2860429566026308607717

theorem tailTrace_12534 : CollatzResearch.WordTrace tailWord_12534 prefixEnd_12534 2860429566026308607717 := by
  unfold tailWord_12534
  simp only [CollatzResearch.WordTrace]
  refine ⟨28572033537433342617791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 304768357732622321256437 28572033537433342617791)
  ·
    refine ⟨42858050306150013926687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28572033537433342617791 42858050306150013926687)
    ·
      refine ⟨64287075459225020890031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42858050306150013926687 64287075459225020890031)
      ·
        refine ⟨96430613188837531335047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64287075459225020890031 96430613188837531335047)
        ·
          refine ⟨144645919783256297002571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96430613188837531335047 144645919783256297002571)
          ·
            refine ⟨216968879674884445503857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144645919783256297002571 216968879674884445503857)
            ·
              refine ⟨162726659756163334127893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216968879674884445503857 162726659756163334127893)
              ·
                refine ⟨7627812176070156287245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162726659756163334127893 7627812176070156287245)
                ·
                  refine ⟨2860429566026308607717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7627812176070156287245 2860429566026308607717)
                  ·
                    rfl

theorem cell21_12534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_12534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12534 prefixEnd_12534 := by exact prefixLift 12534
  have htrace : WordTrace (prefixWord ++ tailWord_12534) baseStart_12534 baseEnd_12534 := by
    simpa [prefixWord, tailWord_12534, baseEnd_12534] using wordTrace_append hprefix tailTrace_12534
  have hstable : (prefixWord ++ tailWord_12534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12534).length < 2 ^ (prefixWord ++ tailWord_12534).sum := by decide
  have hdescent : baseEnd_12534 < baseStart_12534 := by decide
  rcases family_descends (prefixWord ++ tailWord_12534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12607 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_12607 : Nat := 118140960795 + 12607 * 2 ^ 59
def prefixEnd_12607 : Nat := 4983230072969 + 3 ^ 40 * 12607 * 2
def baseEnd_12607 : Nat := 2877089160594403890901

theorem tailTrace_12607 : CollatzResearch.WordTrace tailWord_12607 prefixEnd_12607 2877089160594403890901 := by
  unfold tailWord_12607
  simp only [CollatzResearch.WordTrace]
  refine ⟨459815065334466949292075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 306543376889644632861383 459815065334466949292075)
  ·
    refine ⟨689722598001700423938113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459815065334466949292075 689722598001700423938113)
    ·
      refine ⟨517291948501275317953585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689722598001700423938113 517291948501275317953585)
      ·
        refine ⟨387968961375956488465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517291948501275317953585 387968961375956488465189)
        ·
          refine ⟨72744180257991841587223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387968961375956488465189 72744180257991841587223)
          ·
            refine ⟨109116270386987762380835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72744180257991841587223 109116270386987762380835)
            ·
              refine ⟨163674405580481643571253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109116270386987762380835 163674405580481643571253)
              ·
                refine ⟨15344475523170154084805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163674405580481643571253 15344475523170154084805)
                ·
                  refine ⟨2877089160594403890901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15344475523170154084805 2877089160594403890901)
                  ·
                    rfl

theorem cell21_12607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_12607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12607 prefixEnd_12607 := by exact prefixLift 12607
  have htrace : WordTrace (prefixWord ++ tailWord_12607) baseStart_12607 baseEnd_12607 := by
    simpa [prefixWord, tailWord_12607, baseEnd_12607] using wordTrace_append hprefix tailTrace_12607
  have hstable : (prefixWord ++ tailWord_12607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12607).length < 2 ^ (prefixWord ++ tailWord_12607).sum := by decide
  have hdescent : baseEnd_12607 < baseStart_12607 := by decide
  rcases family_descends (prefixWord ++ tailWord_12607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12666 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_12666 : Nat := 118140960795 + 12666 * 2 ^ 59
def prefixEnd_12666 : Nat := 4983230072969 + 3 ^ 40 * 12666 * 2
def baseEnd_12666 : Nat := 2890553764423412407447

theorem tailTrace_12666 : CollatzResearch.WordTrace tailWord_12666 prefixEnd_12666 2890553764423412407447 := by
  unfold tailWord_12666
  simp only [CollatzResearch.WordTrace]
  refine ⟨115491743030180006422463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 307977981413813350459901 115491743030180006422463)
  ·
    refine ⟨173237614545270009633695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115491743030180006422463 173237614545270009633695)
    ·
      refine ⟨259856421817905014450543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173237614545270009633695 259856421817905014450543)
      ·
        refine ⟨389784632726857521675815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259856421817905014450543 389784632726857521675815)
        ·
          refine ⟨584676949090286282513723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389784632726857521675815 584676949090286282513723)
          ·
            refine ⟨877015423635429423770585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584676949090286282513723 877015423635429423770585)
            ·
              refine ⟨657761567726572067827939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877015423635429423770585 657761567726572067827939)
              ·
                refine ⟨986642351589858101741909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657761567726572067827939 986642351589858101741909)
                ·
                  refine ⟨2890553764423412407447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 986642351589858101741909 2890553764423412407447)
                  ·
                    rfl

theorem cell21_12666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_12666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12666 prefixEnd_12666 := by exact prefixLift 12666
  have htrace : WordTrace (prefixWord ++ tailWord_12666) baseStart_12666 baseEnd_12666 := by
    simpa [prefixWord, tailWord_12666, baseEnd_12666] using wordTrace_append hprefix tailTrace_12666
  have hstable : (prefixWord ++ tailWord_12666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12666).length < 2 ^ (prefixWord ++ tailWord_12666).sum := by decide
  have hdescent : baseEnd_12666 < baseStart_12666 := by decide
  rcases family_descends (prefixWord ++ tailWord_12666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12717 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 4]
def baseStart_12717 : Nat := 118140960795 + 12717 * 2 ^ 59
def prefixEnd_12717 : Nat := 4983230072969 + 3 ^ 40 * 12717 * 2
def baseEnd_12717 : Nat := 2902192659258657057343

theorem tailTrace_12717 : CollatzResearch.WordTrace tailWord_12717 prefixEnd_12717 2902192659258657057343 := by
  unfold tailWord_12717
  simp only [CollatzResearch.WordTrace]
  refine ⟨463827094935955735796405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 309218063290637157197603 463827094935955735796405)
  ·
    refine ⟨43483790150245850230913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 463827094935955735796405 43483790150245850230913)
    ·
      refine ⟨32612842612684387673185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43483790150245850230913 32612842612684387673185)
      ·
        refine ⟨24459631959513290754889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32612842612684387673185 24459631959513290754889)
        ·
          refine ⟨18344723969634968066167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24459631959513290754889 18344723969634968066167)
          ·
            refine ⟨27517085954452452099251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18344723969634968066167 27517085954452452099251)
            ·
              refine ⟨41275628931678678148877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27517085954452452099251 41275628931678678148877)
              ·
                refine ⟨15478360849379504305829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41275628931678678148877 15478360849379504305829)
                ·
                  refine ⟨2902192659258657057343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15478360849379504305829 2902192659258657057343)
                  ·
                    rfl

theorem cell21_12717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_12717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12717 prefixEnd_12717 := by exact prefixLift 12717
  have htrace : WordTrace (prefixWord ++ tailWord_12717) baseStart_12717 baseEnd_12717 := by
    simpa [prefixWord, tailWord_12717, baseEnd_12717] using wordTrace_append hprefix tailTrace_12717
  have hstable : (prefixWord ++ tailWord_12717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12717).length < 2 ^ (prefixWord ++ tailWord_12717).sum := by decide
  have hdescent : baseEnd_12717 < baseStart_12717 := by decide
  rcases family_descends (prefixWord ++ tailWord_12717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12821 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 3]
def baseStart_12821 : Nat := 118140960795 + 12821 * 2 ^ 59
def prefixEnd_12821 : Nat := 4983230072969 + 3 ^ 40 * 12821 * 2
def baseEnd_12821 : Nat := 2925926876177587323797

theorem tailTrace_12821 : CollatzResearch.WordTrace tailWord_12821 prefixEnd_12821 2925926876177587323797 := by
  unfold tailWord_12821
  simp only [CollatzResearch.WordTrace]
  refine ⟨467620286559181497582317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311746857706120998388211 467620286559181497582317)
  ·
    refine ⟨175357607459693061593369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 467620286559181497582317 175357607459693061593369)
    ·
      refine ⟨131518205594769796195027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175357607459693061593369 131518205594769796195027)
      ·
        refine ⟨197277308392154694292541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131518205594769796195027 197277308392154694292541)
        ·
          refine ⟨73978990647058010359703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197277308392154694292541 73978990647058010359703)
          ·
            refine ⟨110968485970587015539555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73978990647058010359703 110968485970587015539555)
            ·
              refine ⟨166452728955880523309333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110968485970587015539555 166452728955880523309333)
              ·
                refine ⟨7802471669806899530125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166452728955880523309333 7802471669806899530125)
                ·
                  refine ⟨2925926876177587323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7802471669806899530125 2925926876177587323797)
                  ·
                    rfl

theorem cell21_12821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_12821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12821 prefixEnd_12821 := by exact prefixLift 12821
  have htrace : WordTrace (prefixWord ++ tailWord_12821) baseStart_12821 baseEnd_12821 := by
    simpa [prefixWord, tailWord_12821, baseEnd_12821] using wordTrace_append hprefix tailTrace_12821
  have hstable : (prefixWord ++ tailWord_12821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12821).length < 2 ^ (prefixWord ++ tailWord_12821).sum := by decide
  have hdescent : baseEnd_12821 < baseStart_12821 := by decide
  rcases family_descends (prefixWord ++ tailWord_12821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12925 : List Nat := [1, 4, 1, 1, 5, 9]
def baseStart_12925 : Nat := 118140960795 + 12925 * 2 ^ 59
def prefixEnd_12925 : Nat := 4983230072969 + 3 ^ 40 * 12925 * 2
def baseEnd_12925 : Nat := 109246707151722873713

theorem tailTrace_12925 : CollatzResearch.WordTrace tailWord_12925 prefixEnd_12925 109246707151722873713 := by
  unfold tailWord_12925
  simp only [CollatzResearch.WordTrace]
  refine ⟨471413478182407259368229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 314275652121604839578819 471413478182407259368229)
  ·
    refine ⟨88390027159201361131543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 471413478182407259368229 88390027159201361131543)
    ·
      refine ⟨132585040738802041697315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88390027159201361131543 132585040738802041697315)
      ·
        refine ⟨198877561108203062545973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132585040738802041697315 198877561108203062545973)
        ·
          refine ⟨18644771353894037113685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198877561108203062545973 18644771353894037113685)
          ·
            refine ⟨109246707151722873713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 18644771353894037113685 109246707151722873713)
            ·
              rfl

theorem cell21_12925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 9].length) (baseStart_12925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12925 prefixEnd_12925 := by exact prefixLift 12925
  have htrace : WordTrace (prefixWord ++ tailWord_12925) baseStart_12925 baseEnd_12925 := by
    simpa [prefixWord, tailWord_12925, baseEnd_12925] using wordTrace_append hprefix tailTrace_12925
  have hstable : (prefixWord ++ tailWord_12925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12925).length < 2 ^ (prefixWord ++ tailWord_12925).sum := by decide
  have hdescent : baseEnd_12925 < baseStart_12925 := by decide
  rcases family_descends (prefixWord ++ tailWord_12925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12956 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_12956 : Nat := 118140960795 + 12956 * 2 ^ 59
def prefixEnd_12956 : Nat := 4983230072969 + 3 ^ 40 * 12956 * 2
def baseEnd_12956 : Nat := 2956735715447352573521

theorem tailTrace_12956 : CollatzResearch.WordTrace tailWord_12956 prefixEnd_12956 2956735715447352573521 := by
  unfold tailWord_12956
  simp only [CollatzResearch.WordTrace]
  refine ⟨236272070535049776873361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 315029427380066369164481 236272070535049776873361)
  ·
    refine ⟨177204052901287332655021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236272070535049776873361 177204052901287332655021)
    ·
      refine ⟨66451519837982749745633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177204052901287332655021 66451519837982749745633)
      ·
        refine ⟨49838639878487062309225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66451519837982749745633 49838639878487062309225)
        ·
          refine ⟨37378979908865296731919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49838639878487062309225 37378979908865296731919)
          ·
            refine ⟨56068469863297945097879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37378979908865296731919 56068469863297945097879)
            ·
              refine ⟨84102704794946917646819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56068469863297945097879 84102704794946917646819)
              ·
                refine ⟨126154057192420376470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84102704794946917646819 126154057192420376470229)
                ·
                  refine ⟨2956735715447352573521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126154057192420376470229 2956735715447352573521)
                  ·
                    rfl

theorem cell21_12956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_12956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12956 prefixEnd_12956 := by exact prefixLift 12956
  have htrace : WordTrace (prefixWord ++ tailWord_12956) baseStart_12956 baseEnd_12956 := by
    simpa [prefixWord, tailWord_12956, baseEnd_12956] using wordTrace_append hprefix tailTrace_12956
  have hstable : (prefixWord ++ tailWord_12956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12956).length < 2 ^ (prefixWord ++ tailWord_12956).sum := by decide
  have hdescent : baseEnd_12956 < baseStart_12956 := by decide
  rcases family_descends (prefixWord ++ tailWord_12956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13136 : List Nat := [2, 1, 1, 1, 1, 4, 2, 9]
def baseStart_13136 : Nat := 118140960795 + 13136 * 2 ^ 59
def prefixEnd_13136 : Nat := 4983230072969 + 3 ^ 40 * 13136 * 2
def baseEnd_13136 : Nat := 999271389269013191051

theorem tailTrace_13136 : CollatzResearch.WordTrace tailWord_13136 prefixEnd_13136 999271389269013191051 := by
  unfold tailWord_13136
  simp only [CollatzResearch.WordTrace]
  refine ⟨239554640208995147649631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 319406186945326863532841 239554640208995147649631)
  ·
    refine ⟨359331960313492721474447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239554640208995147649631 359331960313492721474447)
    ·
      refine ⟨538997940470239082211671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359331960313492721474447 538997940470239082211671)
      ·
        refine ⟨808496910705358623317507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538997940470239082211671 808496910705358623317507)
        ·
          refine ⟨1212745366058037934976261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808496910705358623317507 1212745366058037934976261)
          ·
            refine ⟨227389756135882112808049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1212745366058037934976261 227389756135882112808049)
            ·
              refine ⟨170542317101911584606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227389756135882112808049 170542317101911584606037)
              ·
                refine ⟨999271389269013191051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 170542317101911584606037 999271389269013191051)
                ·
                  rfl

theorem cell21_13136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_13136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13136 prefixEnd_13136 := by exact prefixLift 13136
  have htrace : WordTrace (prefixWord ++ tailWord_13136) baseStart_13136 baseEnd_13136 := by
    simpa [prefixWord, tailWord_13136, baseEnd_13136] using wordTrace_append hprefix tailTrace_13136
  have hstable : (prefixWord ++ tailWord_13136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13136).length < 2 ^ (prefixWord ++ tailWord_13136).sum := by decide
  have hdescent : baseEnd_13136 < baseStart_13136 := by decide
  rcases family_descends (prefixWord ++ tailWord_13136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13156 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_13156 : Nat := 118140960795 + 13156 * 2 ^ 59
def prefixEnd_13156 : Nat := 4983230072969 + 3 ^ 40 * 13156 * 2
def baseEnd_13156 : Nat := 3002378440291449239779

theorem tailTrace_13156 : CollatzResearch.WordTrace tailWord_13156 prefixEnd_13156 3002378440291449239779 := by
  unfold tailWord_13156
  simp only [CollatzResearch.WordTrace]
  refine ⟨239919370172766855513661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 319892493563689140684881 239919370172766855513661)
  ·
    refine ⟨89969763814787570817623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239919370172766855513661 89969763814787570817623)
    ·
      refine ⟨134954645722181356226435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89969763814787570817623 134954645722181356226435)
      ·
        refine ⟨202431968583272034339653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134954645722181356226435 202431968583272034339653)
        ·
          refine ⟨37955994109363506438685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202431968583272034339653 37955994109363506438685)
          ·
            refine ⟨14233497791011314914507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37955994109363506438685 14233497791011314914507)
            ·
              refine ⟨21350246686516972371761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233497791011314914507 21350246686516972371761)
              ·
                refine ⟨16012685014887729278821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21350246686516972371761 16012685014887729278821)
                ·
                  refine ⟨3002378440291449239779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16012685014887729278821 3002378440291449239779)
                  ·
                    rfl

theorem cell21_13156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_13156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13156 prefixEnd_13156 := by exact prefixLift 13156
  have htrace : WordTrace (prefixWord ++ tailWord_13156) baseStart_13156 baseEnd_13156 := by
    simpa [prefixWord, tailWord_13156, baseEnd_13156] using wordTrace_append hprefix tailTrace_13156
  have hstable : (prefixWord ++ tailWord_13156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13156).length < 2 ^ (prefixWord ++ tailWord_13156).sum := by decide
  have hdescent : baseEnd_13156 < baseStart_13156 := by decide
  rcases family_descends (prefixWord ++ tailWord_13156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13305 : List Nat := [1, 2, 1, 3, 1, 3, 5, 5]
def baseStart_13305 : Nat := 118140960795 + 13305 * 2 ^ 59
def prefixEnd_13305 : Nat := 4983230072969 + 3 ^ 40 * 13305 * 2
def baseEnd_13305 : Nat := 1012127423433433752047

theorem tailTrace_13305 : CollatzResearch.WordTrace tailWord_13305 prefixEnd_13305 1012127423433433752047 := by
  unfold tailWord_13305
  simp only [CollatzResearch.WordTrace]
  refine ⟨485273216805732158201369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 323515477870488105467579 485273216805732158201369)
  ·
    refine ⟨363954912604299118651027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485273216805732158201369 363954912604299118651027)
    ·
      refine ⟨545932368906448677976541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363954912604299118651027 545932368906448677976541)
      ·
        refine ⟨204724638339918254241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545932368906448677976541 204724638339918254241203)
        ·
          refine ⟨307086957509877381361805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204724638339918254241203 307086957509877381361805)
          ·
            refine ⟨115157609066204018010677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307086957509877381361805 115157609066204018010677)
            ·
              refine ⟨10796025849956626688501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115157609066204018010677 10796025849956626688501)
              ·
                refine ⟨1012127423433433752047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10796025849956626688501 1012127423433433752047)
                ·
                  rfl

theorem cell21_13305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 5].length) (baseStart_13305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13305 prefixEnd_13305 := by exact prefixLift 13305
  have htrace : WordTrace (prefixWord ++ tailWord_13305) baseStart_13305 baseEnd_13305 := by
    simpa [prefixWord, tailWord_13305, baseEnd_13305] using wordTrace_append hprefix tailTrace_13305
  have hstable : (prefixWord ++ tailWord_13305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13305).length < 2 ^ (prefixWord ++ tailWord_13305).sum := by decide
  have hdescent : baseEnd_13305 < baseStart_13305 := by decide
  rcases family_descends (prefixWord ++ tailWord_13305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13319 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_13319 : Nat := 118140960795 + 13319 * 2 ^ 59
def prefixEnd_13319 : Nat := 4983230072969 + 3 ^ 40 * 13319 * 2
def baseEnd_13319 : Nat := 3039577261039388022779

theorem tailTrace_13319 : CollatzResearch.WordTrace tailWord_13319 prefixEnd_13319 3039577261039388022779 := by
  unfold tailWord_13319
  simp only [CollatzResearch.WordTrace]
  refine ⟨485783838755012549211011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 323855892503341699474007 485783838755012549211011)
  ·
    refine ⟨728675758132518823816517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485783838755012549211011 728675758132518823816517)
    ·
      refine ⟨136626704649847279465597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 728675758132518823816517 136626704649847279465597)
      ·
        refine ⟨51235014243692729799599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136626704649847279465597 51235014243692729799599)
        ·
          refine ⟨76852521365539094699399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51235014243692729799599 76852521365539094699399)
          ·
            refine ⟨115278782048308642049099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76852521365539094699399 115278782048308642049099)
            ·
              refine ⟨172918173072462963073649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115278782048308642049099 172918173072462963073649)
              ·
                refine ⟨129688629804347222305237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172918173072462963073649 129688629804347222305237)
                ·
                  refine ⟨3039577261039388022779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129688629804347222305237 3039577261039388022779)
                  ·
                    rfl

theorem cell21_13319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_13319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13319 prefixEnd_13319 := by exact prefixLift 13319
  have htrace : WordTrace (prefixWord ++ tailWord_13319) baseStart_13319 baseEnd_13319 := by
    simpa [prefixWord, tailWord_13319, baseEnd_13319] using wordTrace_append hprefix tailTrace_13319
  have hstable : (prefixWord ++ tailWord_13319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13319).length < 2 ^ (prefixWord ++ tailWord_13319).sum := by decide
  have hdescent : baseEnd_13319 < baseStart_13319 := by decide
  rcases family_descends (prefixWord ++ tailWord_13319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13336 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_13336 : Nat := 118140960795 + 13336 * 2 ^ 59
def prefixEnd_13336 : Nat := 4983230072969 + 3 ^ 40 * 13336 * 2
def baseEnd_13336 : Nat := 3043456892651136239411

theorem tailTrace_13336 : CollatzResearch.WordTrace tailWord_13336 prefixEnd_13336 3043456892651136239411 := by
  unfold tailWord_13336
  simp only [CollatzResearch.WordTrace]
  refine ⟨243201939846712226289931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 324269253128949635053241 243201939846712226289931)
  ·
    refine ⟨364802909770068339434897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243201939846712226289931 364802909770068339434897)
    ·
      refine ⟨273602182327551254576173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364802909770068339434897 273602182327551254576173)
      ·
        refine ⟨102600818372831720466065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273602182327551254576173 102600818372831720466065)
        ·
          refine ⟨76950613779623790349549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102600818372831720466065 76950613779623790349549)
          ·
            refine ⟨28856480167358921381081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76950613779623790349549 28856480167358921381081)
            ·
              refine ⟨21642360125519191035811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28856480167358921381081 21642360125519191035811)
              ·
                refine ⟨32463540188278786553717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21642360125519191035811 32463540188278786553717)
                ·
                  refine ⟨3043456892651136239411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32463540188278786553717 3043456892651136239411)
                  ·
                    rfl

theorem cell21_13336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_13336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13336 prefixEnd_13336 := by exact prefixLift 13336
  have htrace : WordTrace (prefixWord ++ tailWord_13336) baseStart_13336 baseEnd_13336 := by
    simpa [prefixWord, tailWord_13336, baseEnd_13336] using wordTrace_append hprefix tailTrace_13336
  have hstable : (prefixWord ++ tailWord_13336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13336).length < 2 ^ (prefixWord ++ tailWord_13336).sum := by decide
  have hdescent : baseEnd_13336 < baseStart_13336 := by decide
  rcases family_descends (prefixWord ++ tailWord_13336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13438 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_13438 : Nat := 118140960795 + 13438 * 2 ^ 59
def prefixEnd_13438 : Nat := 4983230072969 + 3 ^ 40 * 13438 * 2
def baseEnd_13438 : Nat := 3066734682321625539203

theorem tailTrace_13438 : CollatzResearch.WordTrace tailWord_13438 prefixEnd_13438 3066734682321625539203 := by
  unfold tailWord_13438
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265515665486984099121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 326749416882597248528645 61265515665486984099121)
  ·
    refine ⟨45949136749115238074341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61265515665486984099121 45949136749115238074341)
    ·
      refine ⟨8615463140459107138939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45949136749115238074341 8615463140459107138939)
      ·
        refine ⟨12923194710688660708409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615463140459107138939 12923194710688660708409)
        ·
          refine ⟨9692396033016495531307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12923194710688660708409 9692396033016495531307)
          ·
            refine ⟨14538594049524743296961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692396033016495531307 14538594049524743296961)
            ·
              refine ⟨10903945537143557472721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14538594049524743296961 10903945537143557472721)
              ·
                refine ⟨8177959152857668104541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10903945537143557472721 8177959152857668104541)
                ·
                  refine ⟨3066734682321625539203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8177959152857668104541 3066734682321625539203)
                  ·
                    rfl

theorem cell21_13438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_13438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13438 prefixEnd_13438 := by exact prefixLift 13438
  have htrace : WordTrace (prefixWord ++ tailWord_13438) baseStart_13438 baseEnd_13438 := by
    simpa [prefixWord, tailWord_13438, baseEnd_13438] using wordTrace_append hprefix tailTrace_13438
  have hstable : (prefixWord ++ tailWord_13438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13438).length < 2 ^ (prefixWord ++ tailWord_13438).sum := by decide
  have hdescent : baseEnd_13438 < baseStart_13438 := by decide
  rcases family_descends (prefixWord ++ tailWord_13438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13494 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_13494 : Nat := 118140960795 + 13494 * 2 ^ 59
def prefixEnd_13494 : Nat := 4983230072969 + 3 ^ 40 * 13494 * 2
def baseEnd_13494 : Nat := 3079514645277972605755

theorem tailTrace_13494 : CollatzResearch.WordTrace tailWord_13494 prefixEnd_13494 3079514645277972605755 := by
  unfold tailWord_13494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30760413320063589801971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 328111075414011624554357 30760413320063589801971)
  ·
    refine ⟨46140619980095384702957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30760413320063589801971 46140619980095384702957)
    ·
      refine ⟨17302732492535769263609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46140619980095384702957 17302732492535769263609)
      ·
        refine ⟨12977049369401826947707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17302732492535769263609 12977049369401826947707)
        ·
          refine ⟨19465574054102740421561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977049369401826947707 19465574054102740421561)
          ·
            refine ⟨14599180540577055316171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19465574054102740421561 14599180540577055316171)
            ·
              refine ⟨21898770810865582974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599180540577055316171 21898770810865582974257)
              ·
                refine ⟨16424078108149187230693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21898770810865582974257 16424078108149187230693)
                ·
                  refine ⟨3079514645277972605755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16424078108149187230693 3079514645277972605755)
                  ·
                    rfl

theorem cell21_13494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_13494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13494 prefixEnd_13494 := by exact prefixLift 13494
  have htrace : WordTrace (prefixWord ++ tailWord_13494) baseStart_13494 baseEnd_13494 := by
    simpa [prefixWord, tailWord_13494, baseEnd_13494] using wordTrace_append hprefix tailTrace_13494
  have hstable : (prefixWord ++ tailWord_13494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13494).length < 2 ^ (prefixWord ++ tailWord_13494).sum := by decide
  have hdescent : baseEnd_13494 < baseStart_13494 := by decide
  rcases family_descends (prefixWord ++ tailWord_13494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13505 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_13505 : Nat := 118140960795 + 13505 * 2 ^ 59
def prefixEnd_13505 : Nat := 4983230072969 + 3 ^ 40 * 13505 * 2
def baseEnd_13505 : Nat := 3082024995144397922399

theorem tailTrace_13505 : CollatzResearch.WordTrace tailWord_13505 prefixEnd_13505 3082024995144397922399 := by
  unfold tailWord_13505
  simp only [CollatzResearch.WordTrace]
  refine ⟨492567816081166315481969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 328378544054110876987979 492567816081166315481969)
  ·
    refine ⟨369425862060874736611477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 492567816081166315481969 369425862060874736611477)
    ·
      refine ⟨17316837284103503278663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369425862060874736611477 17316837284103503278663)
      ·
        refine ⟨25975255926155254917995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316837284103503278663 25975255926155254917995)
        ·
          refine ⟨38962883889232882376993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25975255926155254917995 38962883889232882376993)
          ·
            refine ⟨29222162916924661782745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38962883889232882376993 29222162916924661782745)
            ·
              refine ⟨21916622187693496337059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29222162916924661782745 21916622187693496337059)
              ·
                refine ⟨32874933281540244505589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21916622187693496337059 32874933281540244505589)
                ·
                  refine ⟨3082024995144397922399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32874933281540244505589 3082024995144397922399)
                  ·
                    rfl

theorem cell21_13505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_13505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13505 prefixEnd_13505 := by exact prefixLift 13505
  have htrace : WordTrace (prefixWord ++ tailWord_13505) baseStart_13505 baseEnd_13505 := by
    simpa [prefixWord, tailWord_13505, baseEnd_13505] using wordTrace_append hprefix tailTrace_13505
  have hstable : (prefixWord ++ tailWord_13505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13505).length < 2 ^ (prefixWord ++ tailWord_13505).sum := by decide
  have hdescent : baseEnd_13505 < baseStart_13505 := by decide
  rcases family_descends (prefixWord ++ tailWord_13505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13556 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_13556 : Nat := 118140960795 + 13556 * 2 ^ 59
def prefixEnd_13556 : Nat := 4983230072969 + 3 ^ 40 * 13556 * 2
def baseEnd_13556 : Nat := 3093663889979642572295

theorem tailTrace_13556 : CollatzResearch.WordTrace tailWord_13556 prefixEnd_13556 3093663889979642572295 := by
  unfold tailWord_13556
  simp only [CollatzResearch.WordTrace]
  refine ⟨247213969448201012794261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 329618625930934683725681 247213969448201012794261)
  ·
    refine ⟨11588154817884422474731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247213969448201012794261 11588154817884422474731)
    ·
      refine ⟨17382232226826633712097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588154817884422474731 17382232226826633712097)
      ·
        refine ⟨13036674170119975284073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17382232226826633712097 13036674170119975284073)
        ·
          refine ⟨9777505627589981463055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13036674170119975284073 9777505627589981463055)
          ·
            refine ⟨14666258441384972194583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777505627589981463055 14666258441384972194583)
            ·
              refine ⟨21999387662077458291875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14666258441384972194583 21999387662077458291875)
              ·
                refine ⟨32999081493116187437813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21999387662077458291875 32999081493116187437813)
                ·
                  refine ⟨3093663889979642572295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32999081493116187437813 3093663889979642572295)
                  ·
                    rfl

theorem cell21_13556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_13556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13556 prefixEnd_13556 := by exact prefixLift 13556
  have htrace : WordTrace (prefixWord ++ tailWord_13556) baseStart_13556 baseEnd_13556 := by
    simpa [prefixWord, tailWord_13556, baseEnd_13556] using wordTrace_append hprefix tailTrace_13556
  have hstable : (prefixWord ++ tailWord_13556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13556).length < 2 ^ (prefixWord ++ tailWord_13556).sum := by decide
  have hdescent : baseEnd_13556 < baseStart_13556 := by decide
  rcases family_descends (prefixWord ++ tailWord_13556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13561 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_13561 : Nat := 118140960795 + 13561 * 2 ^ 59
def prefixEnd_13561 : Nat := 4983230072969 + 3 ^ 40 * 13561 * 2
def baseEnd_13561 : Nat := 3094804958100744988951

theorem tailTrace_13561 : CollatzResearch.WordTrace tailWord_13561 prefixEnd_13561 3094804958100744988951 := by
  unfold tailWord_13561
  simp only [CollatzResearch.WordTrace]
  refine ⟨494610303878287879520537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 329740202585525253013691 494610303878287879520537)
  ·
    refine ⟨370957727908715909640403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 494610303878287879520537 370957727908715909640403)
    ·
      refine ⟨556436591863073864460605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370957727908715909640403 556436591863073864460605)
      ·
        refine ⟨208663721948652699172727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556436591863073864460605 208663721948652699172727)
        ·
          refine ⟨312995582922979048759091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208663721948652699172727 312995582922979048759091)
          ·
            refine ⟨469493374384468573138637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312995582922979048759091 469493374384468573138637)
            ·
              refine ⟨176060015394175714926989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469493374384468573138637 176060015394175714926989)
              ·
                refine ⟨66022505772815893097621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176060015394175714926989 66022505772815893097621)
                ·
                  refine ⟨3094804958100744988951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66022505772815893097621 3094804958100744988951)
                  ·
                    rfl

theorem cell21_13561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_13561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13561 prefixEnd_13561 := by exact prefixLift 13561
  have htrace : WordTrace (prefixWord ++ tailWord_13561) baseStart_13561 baseEnd_13561 := by
    simpa [prefixWord, tailWord_13561, baseEnd_13561] using wordTrace_append hprefix tailTrace_13561
  have hstable : (prefixWord ++ tailWord_13561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13561).length < 2 ^ (prefixWord ++ tailWord_13561).sum := by decide
  have hdescent : baseEnd_13561 < baseStart_13561 := by decide
  rcases family_descends (prefixWord ++ tailWord_13561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13570 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_13570 : Nat := 118140960795 + 13570 * 2 ^ 59
def prefixEnd_13570 : Nat := 4983230072969 + 3 ^ 40 * 13570 * 2
def baseEnd_13570 : Nat := 3096858880718729338933

theorem tailTrace_13570 : CollatzResearch.WordTrace tailWord_13570 prefixEnd_13570 3096858880718729338933 := by
  unfold tailWord_13570
  simp only [CollatzResearch.WordTrace]
  refine ⟨123734640211420604149541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 329959040563788277732109 123734640211420604149541)
  ·
    refine ⟨23200245039641363278039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123734640211420604149541 23200245039641363278039)
    ·
      refine ⟨34800367559462044917059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200245039641363278039 34800367559462044917059)
      ·
        refine ⟨52200551339193067375589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34800367559462044917059 52200551339193067375589)
        ·
          refine ⟨9787603376098700132923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52200551339193067375589 9787603376098700132923)
          ·
            refine ⟨14681405064148050199385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787603376098700132923 14681405064148050199385)
            ·
              refine ⟨11011053798111037649539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14681405064148050199385 11011053798111037649539)
              ·
                refine ⟨16516580697166556474309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11011053798111037649539 16516580697166556474309)
                ·
                  refine ⟨3096858880718729338933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16516580697166556474309 3096858880718729338933)
                  ·
                    rfl

theorem cell21_13570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_13570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13570 prefixEnd_13570 := by exact prefixLift 13570
  have htrace : WordTrace (prefixWord ++ tailWord_13570) baseStart_13570 baseEnd_13570 := by
    simpa [prefixWord, tailWord_13570, baseEnd_13570] using wordTrace_append hprefix tailTrace_13570
  have hstable : (prefixWord ++ tailWord_13570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13570).length < 2 ^ (prefixWord ++ tailWord_13570).sum := by decide
  have hdescent : baseEnd_13570 < baseStart_13570 := by decide
  rcases family_descends (prefixWord ++ tailWord_13570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13592 : List Nat := [2, 1, 2, 3, 1, 3, 2, 7]
def baseStart_13592 : Nat := 118140960795 + 13592 * 2 ^ 59
def prefixEnd_13592 : Nat := 4983230072969 + 3 ^ 40 * 13592 * 2
def baseEnd_13592 : Nat := 1033959860150526657407

theorem tailTrace_13592 : CollatzResearch.WordTrace tailWord_13592 prefixEnd_13592 1033959860150526657407 := by
  unfold tailWord_13592
  simp only [CollatzResearch.WordTrace]
  refine ⟨247870483382990086949515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 330493977843986782599353 247870483382990086949515)
  ·
    refine ⟨371805725074485130424273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247870483382990086949515 371805725074485130424273)
    ·
      refine ⟨278854293805863847818205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371805725074485130424273 278854293805863847818205)
      ·
        refine ⟨104570360177198942931827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278854293805863847818205 104570360177198942931827)
        ·
          refine ⟨156855540265798414397741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104570360177198942931827 156855540265798414397741)
          ·
            refine ⟨58820827599674405399153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156855540265798414397741 58820827599674405399153)
            ·
              refine ⟨44115620699755804049365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58820827599674405399153 44115620699755804049365)
              ·
                refine ⟨1033959860150526657407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44115620699755804049365 1033959860150526657407)
                ·
                  rfl

theorem cell21_13592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_13592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13592 prefixEnd_13592 := by exact prefixLift 13592
  have htrace : WordTrace (prefixWord ++ tailWord_13592) baseStart_13592 baseEnd_13592 := by
    simpa [prefixWord, tailWord_13592, baseEnd_13592] using wordTrace_append hprefix tailTrace_13592
  have hstable : (prefixWord ++ tailWord_13592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13592).length < 2 ^ (prefixWord ++ tailWord_13592).sum := by decide
  have hdescent : baseEnd_13592 < baseStart_13592 := by decide
  rcases family_descends (prefixWord ++ tailWord_13592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13668 : List Nat := [2, 3, 1, 1, 3, 3, 8]
def baseStart_13668 : Nat := 118140960795 + 13668 * 2 ^ 59
def prefixEnd_13668 : Nat := 4983230072969 + 3 ^ 40 * 13668 * 2
def baseEnd_13668 : Nat := 346580423988037411711

theorem tailTrace_13668 : CollatzResearch.WordTrace tailWord_13668 prefixEnd_13668 346580423988037411711 := by
  unfold tailWord_13668
  simp only [CollatzResearch.WordTrace]
  refine ⟨249256457245322576832829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 332341942993763435777105 249256457245322576832829)
  ·
    refine ⟨93471171466995966312311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249256457245322576832829 93471171466995966312311)
    ·
      refine ⟨140206757200493949468467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93471171466995966312311 140206757200493949468467)
      ·
        refine ⟨210310135800740924202701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140206757200493949468467 210310135800740924202701)
        ·
          refine ⟨78866300925277846576013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210310135800740924202701 78866300925277846576013)
          ·
            refine ⟨29574862846979192466005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78866300925277846576013 29574862846979192466005)
            ·
              refine ⟨346580423988037411711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 29574862846979192466005 346580423988037411711)
              ·
                rfl

theorem cell21_13668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 8].length) (baseStart_13668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13668 prefixEnd_13668 := by exact prefixLift 13668
  have htrace : WordTrace (prefixWord ++ tailWord_13668) baseStart_13668 baseEnd_13668 := by
    simpa [prefixWord, tailWord_13668, baseEnd_13668] using wordTrace_append hprefix tailTrace_13668
  have hstable : (prefixWord ++ tailWord_13668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13668).length < 2 ^ (prefixWord ++ tailWord_13668).sum := by decide
  have hdescent : baseEnd_13668 < baseStart_13668 := by decide
  rcases family_descends (prefixWord ++ tailWord_13668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13699 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_13699 : Nat := 118140960795 + 13699 * 2 ^ 59
def prefixEnd_13699 : Nat := 4983230072969 + 3 ^ 40 * 13699 * 2
def baseEnd_13699 : Nat := 3126298438243171688669

theorem tailTrace_13699 : CollatzResearch.WordTrace tailWord_13699 prefixEnd_13699 3126298438243171688669 := by
  unfold tailWord_13699
  simp only [CollatzResearch.WordTrace]
  refine ⟨499643577378337448044151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 333095718252224965362767 499643577378337448044151)
  ·
    refine ⟨749465366067506172066227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499643577378337448044151 749465366067506172066227)
    ·
      refine ⟨1124198049101259258099341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749465366067506172066227 1124198049101259258099341)
      ·
        refine ⟨421574268412972221787253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1124198049101259258099341 421574268412972221787253)
        ·
          refine ⟨39522587663716145792555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421574268412972221787253 39522587663716145792555)
          ·
            refine ⟨59283881495574218688833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39522587663716145792555 59283881495574218688833)
            ·
              refine ⟨44462911121680664016625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59283881495574218688833 44462911121680664016625)
              ·
                refine ⟨33347183341260498012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44462911121680664016625 33347183341260498012469)
                ·
                  refine ⟨3126298438243171688669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33347183341260498012469 3126298438243171688669)
                  ·
                    rfl

theorem cell21_13699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_13699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13699 prefixEnd_13699 := by exact prefixLift 13699
  have htrace : WordTrace (prefixWord ++ tailWord_13699) baseStart_13699 baseEnd_13699 := by
    simpa [prefixWord, tailWord_13699, baseEnd_13699] using wordTrace_append hprefix tailTrace_13699
  have hstable : (prefixWord ++ tailWord_13699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13699).length < 2 ^ (prefixWord ++ tailWord_13699).sum := by decide
  have hdescent : baseEnd_13699 < baseStart_13699 := by decide
  rcases family_descends (prefixWord ++ tailWord_13699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13730 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_13730 : Nat := 118140960795 + 13730 * 2 ^ 59
def prefixEnd_13730 : Nat := 4983230072969 + 3 ^ 40 * 13730 * 2
def baseEnd_13730 : Nat := 3133373060594006671939

theorem tailTrace_13730 : CollatzResearch.WordTrace tailWord_13730 prefixEnd_13730 3133373060594006671939 := by
  unfold tailWord_13730
  simp only [CollatzResearch.WordTrace]
  refine ⟨125193560066507435605661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 333849493510686494948429 125193560066507435605661)
  ·
    refine ⟨46947585024940288352123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125193560066507435605661 46947585024940288352123)
    ·
      refine ⟨70421377537410432528185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46947585024940288352123 70421377537410432528185)
      ·
        refine ⟨52816033153057824396139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70421377537410432528185 52816033153057824396139)
        ·
          refine ⟨79224049729586736594209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52816033153057824396139 79224049729586736594209)
          ·
            refine ⟨59418037297190052445657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79224049729586736594209 59418037297190052445657)
            ·
              refine ⟨44563527972892539334243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59418037297190052445657 44563527972892539334243)
              ·
                refine ⟨66845291959338809001365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44563527972892539334243 66845291959338809001365)
                ·
                  refine ⟨3133373060594006671939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66845291959338809001365 3133373060594006671939)
                  ·
                    rfl

theorem cell21_13730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_13730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13730 prefixEnd_13730 := by exact prefixLift 13730
  have htrace : WordTrace (prefixWord ++ tailWord_13730) baseStart_13730 baseEnd_13730 := by
    simpa [prefixWord, tailWord_13730, baseEnd_13730] using wordTrace_append hprefix tailTrace_13730
  have hstable : (prefixWord ++ tailWord_13730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13730).length < 2 ^ (prefixWord ++ tailWord_13730).sum := by decide
  have hdescent : baseEnd_13730 < baseStart_13730 := by decide
  rcases family_descends (prefixWord ++ tailWord_13730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13803 : List Nat := [1, 1, 1, 1, 2, 3, 2, 10]
def baseStart_13803 : Nat := 118140960795 + 13803 * 2 ^ 59
def prefixEnd_13803 : Nat := 4983230072969 + 3 ^ 40 * 13803 * 2
def baseEnd_13803 : Nat := 1050010885054033985041

theorem tailTrace_13803 : CollatzResearch.WordTrace tailWord_13803 prefixEnd_13803 1050010885054033985041 := by
  unfold tailWord_13803
  simp only [CollatzResearch.WordTrace]
  refine ⟨503436769001563209830063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 335624512667708806553375 503436769001563209830063)
  ·
    refine ⟨755155153502344814745095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503436769001563209830063 755155153502344814745095)
    ·
      refine ⟨1132732730253517222117643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755155153502344814745095 1132732730253517222117643)
      ·
        refine ⟨1699099095380275833176465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132732730253517222117643 1699099095380275833176465)
        ·
          refine ⟨1274324321535206874882349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1699099095380275833176465 1274324321535206874882349)
          ·
            refine ⟨477871620575702578080881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274324321535206874882349 477871620575702578080881)
            ·
              refine ⟨358403715431776933560661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477871620575702578080881 358403715431776933560661)
              ·
                refine ⟨1050010885054033985041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 358403715431776933560661 1050010885054033985041)
                ·
                  rfl

theorem cell21_13803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_13803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13803 prefixEnd_13803 := by exact prefixLift 13803
  have htrace : WordTrace (prefixWord ++ tailWord_13803) baseStart_13803 baseEnd_13803 := by
    simpa [prefixWord, tailWord_13803, baseEnd_13803] using wordTrace_append hprefix tailTrace_13803
  have hstable : (prefixWord ++ tailWord_13803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13803).length < 2 ^ (prefixWord ++ tailWord_13803).sum := by decide
  have hdescent : baseEnd_13803 < baseStart_13803 := by decide
  rcases family_descends (prefixWord ++ tailWord_13803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13806 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_13806 : Nat := 118140960795 + 13806 * 2 ^ 59
def prefixEnd_13806 : Nat := 4983230072969 + 3 ^ 40 * 13806 * 2
def baseEnd_13806 : Nat := 3150717296034763405117

theorem tailTrace_13806 : CollatzResearch.WordTrace tailWord_13806 prefixEnd_13806 3150717296034763405117 := by
  unfold tailWord_13806
  simp only [CollatzResearch.WordTrace]
  refine ⟨62943273498836840273659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 335697458660463148126181 62943273498836840273659)
  ·
    refine ⟨94414910248255260410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62943273498836840273659 94414910248255260410489)
    ·
      refine ⟨70811182686191445307867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94414910248255260410489 70811182686191445307867)
      ·
        refine ⟨106216774029287167961801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70811182686191445307867 106216774029287167961801)
        ·
          refine ⟨79662580521965375971351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106216774029287167961801 79662580521965375971351)
          ·
            refine ⟨119493870782948063957027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79662580521965375971351 119493870782948063957027)
            ·
              refine ⟨179240806174422095935541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119493870782948063957027 179240806174422095935541)
              ·
                refine ⟨16803825578852071493957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179240806174422095935541 16803825578852071493957)
                ·
                  refine ⟨3150717296034763405117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16803825578852071493957 3150717296034763405117)
                  ·
                    rfl

theorem cell21_13806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_13806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13806 prefixEnd_13806 := by exact prefixLift 13806
  have htrace : WordTrace (prefixWord ++ tailWord_13806) baseStart_13806 baseEnd_13806 := by
    simpa [prefixWord, tailWord_13806, baseEnd_13806] using wordTrace_append hprefix tailTrace_13806
  have hstable : (prefixWord ++ tailWord_13806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13806).length < 2 ^ (prefixWord ++ tailWord_13806).sum := by decide
  have hdescent : baseEnd_13806 < baseStart_13806 := by decide
  rcases family_descends (prefixWord ++ tailWord_13806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13826 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_13826 : Nat := 118140960795 + 13826 * 2 ^ 59
def prefixEnd_13826 : Nat := 4983230072969 + 3 ^ 40 * 13826 * 2
def baseEnd_13826 : Nat := 3155281568519173071743

theorem tailTrace_13826 : CollatzResearch.WordTrace tailWord_13826 prefixEnd_13826 3155281568519173071743 := by
  unfold tailWord_13826
  simp only [CollatzResearch.WordTrace]
  refine ⟨126068911979559534479333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 336183765278825425278221 126068911979559534479333)
  ·
    refine ⟨23637920996167412714875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126068911979559534479333 23637920996167412714875)
    ·
      refine ⟨35456881494251119072313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23637920996167412714875 35456881494251119072313)
      ·
        refine ⟨26592661120688339304235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35456881494251119072313 26592661120688339304235)
        ·
          refine ⟨39888991681032508956353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26592661120688339304235 39888991681032508956353)
          ·
            refine ⟨29916743760774381717265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39888991681032508956353 29916743760774381717265)
            ·
              refine ⟨22437557820580786287949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29916743760774381717265 22437557820580786287949)
              ·
                refine ⟨8414084182717794857981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22437557820580786287949 8414084182717794857981)
                ·
                  refine ⟨3155281568519173071743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8414084182717794857981 3155281568519173071743)
                  ·
                    rfl

theorem cell21_13826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_13826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13826 prefixEnd_13826 := by exact prefixLift 13826
  have htrace : WordTrace (prefixWord ++ tailWord_13826) baseStart_13826 baseEnd_13826 := by
    simpa [prefixWord, tailWord_13826, baseEnd_13826] using wordTrace_append hprefix tailTrace_13826
  have hstable : (prefixWord ++ tailWord_13826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13826).length < 2 ^ (prefixWord ++ tailWord_13826).sum := by decide
  have hdescent : baseEnd_13826 < baseStart_13826 := by decide
  rcases family_descends (prefixWord ++ tailWord_13826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13916 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_13916 : Nat := 118140960795 + 13916 * 2 ^ 59
def prefixEnd_13916 : Nat := 4983230072969 + 3 ^ 40 * 13916 * 2
def baseEnd_13916 : Nat := 3175820794699016571559

theorem tailTrace_13916 : CollatzResearch.WordTrace tailWord_13916 prefixEnd_13916 3175820794699016571559 := by
  unfold tailWord_13916
  simp only [CollatzResearch.WordTrace]
  refine ⟨253779108796091754346801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 338372145061455672462401 253779108796091754346801)
  ·
    refine ⟨190334331597068815760101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253779108796091754346801 190334331597068815760101)
    ·
      refine ⟨35687687174450402955019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190334331597068815760101 35687687174450402955019)
      ·
        refine ⟨53531530761675604432529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35687687174450402955019 53531530761675604432529)
        ·
          refine ⟨40148648071256703324397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53531530761675604432529 40148648071256703324397)
          ·
            refine ⟨15055743026721263746649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40148648071256703324397 15055743026721263746649)
            ·
              refine ⟨11291807270040947809987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055743026721263746649 11291807270040947809987)
              ·
                refine ⟨16937710905061421714981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291807270040947809987 16937710905061421714981)
                ·
                  refine ⟨3175820794699016571559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16937710905061421714981 3175820794699016571559)
                  ·
                    rfl

theorem cell21_13916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_13916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13916 prefixEnd_13916 := by exact prefixLift 13916
  have htrace : WordTrace (prefixWord ++ tailWord_13916) baseStart_13916 baseEnd_13916 := by
    simpa [prefixWord, tailWord_13916, baseEnd_13916] using wordTrace_append hprefix tailTrace_13916
  have hstable : (prefixWord ++ tailWord_13916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13916).length < 2 ^ (prefixWord ++ tailWord_13916).sum := by decide
  have hdescent : baseEnd_13916 < baseStart_13916 := by decide
  rcases family_descends (prefixWord ++ tailWord_13916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14020 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_14020 : Nat := 118140960795 + 14020 * 2 ^ 59
def prefixEnd_14020 : Nat := 4983230072969 + 3 ^ 40 * 14020 * 2
def baseEnd_14020 : Nat := 3199555011617946838013

theorem tailTrace_14020 : CollatzResearch.WordTrace tailWord_14020 prefixEnd_14020 3199555011617946838013 := by
  unfold tailWord_14020
  simp only [CollatzResearch.WordTrace]
  refine ⟨255675704607704635239757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 340900939476939513653009 255675704607704635239757)
  ·
    refine ⟨95878389227889238214909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255675704607704635239757 95878389227889238214909)
    ·
      refine ⟨35954395960458464330591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95878389227889238214909 35954395960458464330591)
      ·
        refine ⟨53931593940687696495887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35954395960458464330591 53931593940687696495887)
        ·
          refine ⟨80897390911031544743831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53931593940687696495887 80897390911031544743831)
          ·
            refine ⟨121346086366547317115747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80897390911031544743831 121346086366547317115747)
            ·
              refine ⟨182019129549820975673621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121346086366547317115747 182019129549820975673621)
              ·
                refine ⟨8532146697647858234701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182019129549820975673621 8532146697647858234701)
                ·
                  refine ⟨3199555011617946838013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8532146697647858234701 3199555011617946838013)
                  ·
                    rfl

theorem cell21_14020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_14020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14020 prefixEnd_14020 := by exact prefixLift 14020
  have htrace : WordTrace (prefixWord ++ tailWord_14020) baseStart_14020 baseEnd_14020 := by
    simpa [prefixWord, tailWord_14020, baseEnd_14020] using wordTrace_append hprefix tailTrace_14020
  have hstable : (prefixWord ++ tailWord_14020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14020).length < 2 ^ (prefixWord ++ tailWord_14020).sum := by decide
  have hdescent : baseEnd_14020 < baseStart_14020 := by decide
  rcases family_descends (prefixWord ++ tailWord_14020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14048 : List Nat := [2, 1, 1, 3, 1, 2, 6, 5]
def baseStart_14048 : Nat := 118140960795 + 14048 * 2 ^ 59
def prefixEnd_14048 : Nat := 4983230072969 + 3 ^ 40 * 14048 * 2
def baseEnd_14048 : Nat := 1068648331032040123763

theorem tailTrace_14048 : CollatzResearch.WordTrace tailWord_14048 prefixEnd_14048 1068648331032040123763 := by
  unfold tailWord_14048
  simp only [CollatzResearch.WordTrace]
  refine ⟨256186326556985026249399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 341581768742646701665865 256186326556985026249399)
  ·
    refine ⟨384279489835477539374099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256186326556985026249399 384279489835477539374099)
    ·
      refine ⟨576419234753216309061149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384279489835477539374099 576419234753216309061149)
      ·
        refine ⟨216157213032456115897931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 576419234753216309061149 216157213032456115897931)
        ·
          refine ⟨324235819548684173846897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216157213032456115897931 324235819548684173846897)
          ·
            refine ⟨243176864661513130385173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324235819548684173846897 243176864661513130385173)
            ·
              refine ⟨11398915531008427986805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243176864661513130385173 11398915531008427986805)
              ·
                refine ⟨1068648331032040123763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11398915531008427986805 1068648331032040123763)
                ·
                  rfl

theorem cell21_14048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_14048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14048 prefixEnd_14048 := by exact prefixLift 14048
  have htrace : WordTrace (prefixWord ++ tailWord_14048) baseStart_14048 baseEnd_14048 := by
    simpa [prefixWord, tailWord_14048, baseEnd_14048] using wordTrace_append hprefix tailTrace_14048
  have hstable : (prefixWord ++ tailWord_14048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14048).length < 2 ^ (prefixWord ++ tailWord_14048).sum := by decide
  have hdescent : baseEnd_14048 < baseStart_14048 := by decide
  rcases family_descends (prefixWord ++ tailWord_14048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14079 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 3]
def baseStart_14079 : Nat := 118140960795 + 14079 * 2 ^ 59
def prefixEnd_14079 : Nat := 4983230072969 + 3 ^ 40 * 14079 * 2
def baseEnd_14079 : Nat := 3213019615446955354559

theorem tailTrace_14079 : CollatzResearch.WordTrace tailWord_14079 prefixEnd_14079 3213019615446955354559 := by
  unfold tailWord_14079
  simp only [CollatzResearch.WordTrace]
  refine ⟨513503316001662346877291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342335544001108231251527 513503316001662346877291)
  ·
    refine ⟨770254974002493520315937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513503316001662346877291 770254974002493520315937)
    ·
      refine ⟨577691230501870140236953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770254974002493520315937 577691230501870140236953)
      ·
        refine ⟨433268422876402605177715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577691230501870140236953 433268422876402605177715)
        ·
          refine ⟨649902634314603907766573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433268422876402605177715 649902634314603907766573)
          ·
            refine ⟨243713487867976465412465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 649902634314603907766573 243713487867976465412465)
            ·
              refine ⟨182785115900982349059349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243713487867976465412465 182785115900982349059349)
              ·
                refine ⟨8568052307858547612157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182785115900982349059349 8568052307858547612157)
                ·
                  refine ⟨3213019615446955354559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8568052307858547612157 3213019615446955354559)
                  ·
                    rfl

theorem cell21_14079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 3].length) (baseStart_14079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14079 prefixEnd_14079 := by exact prefixLift 14079
  have htrace : WordTrace (prefixWord ++ tailWord_14079) baseStart_14079 baseEnd_14079 := by
    simpa [prefixWord, tailWord_14079, baseEnd_14079] using wordTrace_append hprefix tailTrace_14079
  have hstable : (prefixWord ++ tailWord_14079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14079).length < 2 ^ (prefixWord ++ tailWord_14079).sum := by decide
  have hdescent : baseEnd_14079 < baseStart_14079 := by decide
  rcases family_descends (prefixWord ++ tailWord_14079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14141 : List Nat := [1, 4, 1, 4, 1, 3, 1, 6]
def baseStart_14141 : Nat := 118140960795 + 14141 * 2 ^ 59
def prefixEnd_14141 : Nat := 4983230072969 + 3 ^ 40 * 14141 * 2
def baseEnd_14141 : Nat := 1075722953382875107033

theorem tailTrace_14141 : CollatzResearch.WordTrace tailWord_14141 prefixEnd_14141 1075722953382875107033 := by
  unfold tailWord_14141
  simp only [CollatzResearch.WordTrace]
  refine ⟨515764641777046935634277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 343843094518031290422851 515764641777046935634277)
  ·
    refine ⟨96705870333196300431427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 515764641777046935634277 96705870333196300431427)
    ·
      refine ⟨145058805499794450647141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96705870333196300431427 145058805499794450647141)
      ·
        refine ⟨27198526031211459496339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145058805499794450647141 27198526031211459496339)
        ·
          refine ⟨40797789046817189244509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27198526031211459496339 40797789046817189244509)
          ·
            refine ⟨15299170892556445966691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40797789046817189244509 15299170892556445966691)
            ·
              refine ⟨22948756338834668950037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15299170892556445966691 22948756338834668950037)
              ·
                refine ⟨1075722953382875107033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22948756338834668950037 1075722953382875107033)
                ·
                  rfl

theorem cell21_14141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_14141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14141 prefixEnd_14141 := by exact prefixLift 14141
  have htrace : WordTrace (prefixWord ++ tailWord_14141) baseStart_14141 baseEnd_14141 := by
    simpa [prefixWord, tailWord_14141, baseEnd_14141] using wordTrace_append hprefix tailTrace_14141
  have hstable : (prefixWord ++ tailWord_14141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14141).length < 2 ^ (prefixWord ++ tailWord_14141).sum := by decide
  have hdescent : baseEnd_14141 < baseStart_14141 := by decide
  rcases family_descends (prefixWord ++ tailWord_14141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14183 : List Nat := [1, 1, 5, 1, 2, 1, 10]
def baseStart_14183 : Nat := 118140960795 + 14183 * 2 ^ 59
def prefixEnd_14183 : Nat := 4983230072969 + 3 ^ 40 * 14183 * 2
def baseEnd_14183 : Nat := 359639314707320624557

theorem tailTrace_14183 : CollatzResearch.WordTrace tailWord_14183 prefixEnd_14183 359639314707320624557 := by
  unfold tailWord_14183
  simp only [CollatzResearch.WordTrace]
  refine ⟨517296507624888108663203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 344864338416592072442135 517296507624888108663203)
  ·
    refine ⟨775944761437332162994805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517296507624888108663203 775944761437332162994805)
    ·
      refine ⟨72744821384749890280763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 775944761437332162994805 72744821384749890280763)
      ·
        refine ⟨109117232077124835421145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72744821384749890280763 109117232077124835421145)
        ·
          refine ⟨81837924057843626565859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109117232077124835421145 81837924057843626565859)
          ·
            refine ⟨122756886086765439848789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81837924057843626565859 122756886086765439848789)
            ·
              refine ⟨359639314707320624557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 122756886086765439848789 359639314707320624557)
              ·
                rfl

theorem cell21_14183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_14183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14183 prefixEnd_14183 := by exact prefixLift 14183
  have htrace : WordTrace (prefixWord ++ tailWord_14183) baseStart_14183 baseEnd_14183 := by
    simpa [prefixWord, tailWord_14183, baseEnd_14183] using wordTrace_append hprefix tailTrace_14183
  have hstable : (prefixWord ++ tailWord_14183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14183).length < 2 ^ (prefixWord ++ tailWord_14183).sum := by decide
  have hdescent : baseEnd_14183 < baseStart_14183 := by decide
  rcases family_descends (prefixWord ++ tailWord_14183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14254 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_14254 : Nat := 118140960795 + 14254 * 2 ^ 59
def prefixEnd_14254 : Nat := 4983230072969 + 3 ^ 40 * 14254 * 2
def baseEnd_14254 : Nat := 3252956999685539937535

theorem tailTrace_14254 : CollatzResearch.WordTrace tailWord_14254 prefixEnd_14254 3252956999685539937535 := by
  unfold tailWord_14254
  simp only [CollatzResearch.WordTrace]
  refine ⟨64985761295958404312227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 346590726911778156331877 64985761295958404312227)
  ·
    refine ⟨97478641943937606468341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64985761295958404312227 97478641943937606468341)
    ·
      refine ⟨9138622682244150606407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97478641943937606468341 9138622682244150606407)
      ·
        refine ⟨13707934023366225909611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138622682244150606407 13707934023366225909611)
        ·
          refine ⟨20561901035049338864417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13707934023366225909611 20561901035049338864417)
          ·
            refine ⟨15421425776287004148313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20561901035049338864417 15421425776287004148313)
            ·
              refine ⟨11566069332215253111235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15421425776287004148313 11566069332215253111235)
              ·
                refine ⟨17349103998322879666853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11566069332215253111235 17349103998322879666853)
                ·
                  refine ⟨3252956999685539937535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17349103998322879666853 3252956999685539937535)
                  ·
                    rfl

theorem cell21_14254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_14254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14254 prefixEnd_14254 := by exact prefixLift 14254
  have htrace : WordTrace (prefixWord ++ tailWord_14254) baseStart_14254 baseEnd_14254 := by
    simpa [prefixWord, tailWord_14254, baseEnd_14254] using wordTrace_append hprefix tailTrace_14254
  have hstable : (prefixWord ++ tailWord_14254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14254).length < 2 ^ (prefixWord ++ tailWord_14254).sum := by decide
  have hdescent : baseEnd_14254 < baseStart_14254 := by decide
  rcases family_descends (prefixWord ++ tailWord_14254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14259 : List Nat := [1, 1, 1, 2, 3, 1, 6, 6]
def baseStart_14259 : Nat := 118140960795 + 14259 * 2 ^ 59
def prefixEnd_14259 : Nat := 4983230072969 + 3 ^ 40 * 14259 * 2
def baseEnd_14259 : Nat := 1084699355935547451397

theorem tailTrace_14259 : CollatzResearch.WordTrace tailWord_14259 prefixEnd_14259 1084699355935547451397 := by
  unfold tailWord_14259
  simp only [CollatzResearch.WordTrace]
  refine ⟨520068455349553088429831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 346712303566368725619887 520068455349553088429831)
  ·
    refine ⟨780102683024329632644747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520068455349553088429831 780102683024329632644747)
    ·
      refine ⟨1170154024536494448967121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780102683024329632644747 1170154024536494448967121)
      ·
        refine ⟨877615518402370836725341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170154024536494448967121 877615518402370836725341)
        ·
          refine ⟨329105819400889063772003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877615518402370836725341 329105819400889063772003)
          ·
            refine ⟨493658729101333595658005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329105819400889063772003 493658729101333595658005)
            ·
              refine ⟨23140252926625012296469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 493658729101333595658005 23140252926625012296469)
              ·
                refine ⟨1084699355935547451397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23140252926625012296469 1084699355935547451397)
                ·
                  rfl

theorem cell21_14259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_14259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14259 prefixEnd_14259 := by exact prefixLift 14259
  have htrace : WordTrace (prefixWord ++ tailWord_14259) baseStart_14259 baseEnd_14259 := by
    simpa [prefixWord, tailWord_14259, baseEnd_14259] using wordTrace_append hprefix tailTrace_14259
  have hstable : (prefixWord ++ tailWord_14259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14259).length < 2 ^ (prefixWord ++ tailWord_14259).sum := by decide
  have hdescent : baseEnd_14259 < baseStart_14259 := by decide
  rcases family_descends (prefixWord ++ tailWord_14259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14304 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_14304 : Nat := 118140960795 + 14304 * 2 ^ 59
def prefixEnd_14304 : Nat := 4983230072969 + 3 ^ 40 * 14304 * 2
def baseEnd_14304 : Nat := 3264367680896564104099

theorem tailTrace_14304 : CollatzResearch.WordTrace tailWord_14304 prefixEnd_14304 3264367680896564104099 := by
  unfold tailWord_14304
  simp only [CollatzResearch.WordTrace]
  refine ⟨260854870093262886908983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 347806493457683849211977 260854870093262886908983)
  ·
    refine ⟨391282305139894330363475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260854870093262886908983 391282305139894330363475)
    ·
      refine ⟨586923457709841495545213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391282305139894330363475 586923457709841495545213)
      ·
        refine ⟨220096296641190560829455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 586923457709841495545213 220096296641190560829455)
        ·
          refine ⟨330144444961785841244183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220096296641190560829455 330144444961785841244183)
          ·
            refine ⟨495216667442678761866275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330144444961785841244183 495216667442678761866275)
            ·
              refine ⟨742825001164018142799413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495216667442678761866275 742825001164018142799413)
              ·
                refine ⟨69639843859126700887445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 742825001164018142799413 69639843859126700887445)
                ·
                  refine ⟨3264367680896564104099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69639843859126700887445 3264367680896564104099)
                  ·
                    rfl

theorem cell21_14304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_14304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14304 prefixEnd_14304 := by exact prefixLift 14304
  have htrace : WordTrace (prefixWord ++ tailWord_14304) baseStart_14304 baseEnd_14304 := by
    simpa [prefixWord, tailWord_14304, baseEnd_14304] using wordTrace_append hprefix tailTrace_14304
  have hstable : (prefixWord ++ tailWord_14304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14304).length < 2 ^ (prefixWord ++ tailWord_14304).sum := by decide
  have hdescent : baseEnd_14304 < baseStart_14304 := by decide
  rcases family_descends (prefixWord ++ tailWord_14304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14400 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_14400 : Nat := 118140960795 + 14400 * 2 ^ 59
def prefixEnd_14400 : Nat := 4983230072969 + 3 ^ 40 * 14400 * 2
def baseEnd_14400 : Nat := 3286276188821730503903

theorem tailTrace_14400 : CollatzResearch.WordTrace tailWord_14400 prefixEnd_14400 3286276188821730503903 := by
  unfold tailWord_14400
  simp only [CollatzResearch.WordTrace]
  refine ⟨262605573919367084656327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 350140765225822779541769 262605573919367084656327)
  ·
    refine ⟨393908360879050626984491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262605573919367084656327 393908360879050626984491)
    ·
      refine ⟨590862541318575940476737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393908360879050626984491 590862541318575940476737)
      ·
        refine ⟨443146905988931955357553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590862541318575940476737 443146905988931955357553)
        ·
          refine ⟨332360179491698966518165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443146905988931955357553 332360179491698966518165)
          ·
            refine ⟨15579383413673389055539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332360179491698966518165 15579383413673389055539)
            ·
              refine ⟨23369075120510083583309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15579383413673389055539 23369075120510083583309)
              ·
                refine ⟨8763403170191281343741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23369075120510083583309 8763403170191281343741)
                ·
                  refine ⟨3286276188821730503903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8763403170191281343741 3286276188821730503903)
                  ·
                    rfl

theorem cell21_14400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_14400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14400 prefixEnd_14400 := by exact prefixLift 14400
  have htrace : WordTrace (prefixWord ++ tailWord_14400) baseStart_14400 baseEnd_14400 := by
    simpa [prefixWord, tailWord_14400, baseEnd_14400] using wordTrace_append hprefix tailTrace_14400
  have hstable : (prefixWord ++ tailWord_14400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14400).length < 2 ^ (prefixWord ++ tailWord_14400).sum := by decide
  have hdescent : baseEnd_14400 < baseStart_14400 := by decide
  rcases family_descends (prefixWord ++ tailWord_14400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14428 : List Nat := [2, 2, 4, 1, 1, 3, 2, 6]
def baseStart_14428 : Nat := 118140960795 + 14428 * 2 ^ 59
def prefixEnd_14428 : Nat := 4983230072969 + 3 ^ 40 * 14428 * 2
def baseEnd_14428 : Nat := 1097555390099968012393

theorem tailTrace_14428 : CollatzResearch.WordTrace tailWord_14428 prefixEnd_14428 1097555390099968012393 := by
  unfold tailWord_14428
  simp only [CollatzResearch.WordTrace]
  refine ⟨263116195868647475665969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 350821594491529967554625 263116195868647475665969)
  ·
    refine ⟨197337146901485606749477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263116195868647475665969 197337146901485606749477)
    ·
      refine ⟨37000715044028551265527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197337146901485606749477 37000715044028551265527)
      ·
        refine ⟨55501072566042826898291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37000715044028551265527 55501072566042826898291)
        ·
          refine ⟨83251608849064240347437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55501072566042826898291 83251608849064240347437)
          ·
            refine ⟨31219353318399090130289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83251608849064240347437 31219353318399090130289)
            ·
              refine ⟨23414514988799317597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31219353318399090130289 23414514988799317597717)
              ·
                refine ⟨1097555390099968012393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23414514988799317597717 1097555390099968012393)
                ·
                  rfl

theorem cell21_14428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_14428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14428 prefixEnd_14428 := by exact prefixLift 14428
  have htrace : WordTrace (prefixWord ++ tailWord_14428) baseStart_14428 baseEnd_14428 := by
    simpa [prefixWord, tailWord_14428, baseEnd_14428] using wordTrace_append hprefix tailTrace_14428
  have hstable : (prefixWord ++ tailWord_14428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14428).length < 2 ^ (prefixWord ++ tailWord_14428).sum := by decide
  have hdescent : baseEnd_14428 < baseStart_14428 := by decide
  rcases family_descends (prefixWord ++ tailWord_14428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14473 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_14473 : Nat := 118140960795 + 14473 * 2 ^ 59
def prefixEnd_14473 : Nat := 4983230072969 + 3 ^ 40 * 14473 * 2
def baseEnd_14473 : Nat := 3302935783389825787087

theorem tailTrace_14473 : CollatzResearch.WordTrace tailWord_14473 prefixEnd_14473 3302935783389825787087 := by
  unfold tailWord_14473
  simp only [CollatzResearch.WordTrace]
  refine ⟨527873676574267636720073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 351915784382845091146715 527873676574267636720073)
  ·
    refine ⟨395905257430700727540055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527873676574267636720073 395905257430700727540055)
    ·
      refine ⟨593857886146051091310083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395905257430700727540055 593857886146051091310083)
      ·
        refine ⟨890786829219076636965125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593857886146051091310083 890786829219076636965125)
        ·
          refine ⟨167022530478576869430961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 890786829219076636965125 167022530478576869430961)
          ·
            refine ⟨125266897858932652073221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167022530478576869430961 125266897858932652073221)
            ·
              refine ⟨23487543348549872263729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125266897858932652073221 23487543348549872263729)
              ·
                refine ⟨17615657511412404197797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23487543348549872263729 17615657511412404197797)
                ·
                  refine ⟨3302935783389825787087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17615657511412404197797 3302935783389825787087)
                  ·
                    rfl

theorem cell21_14473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_14473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14473 prefixEnd_14473 := by exact prefixLift 14473
  have htrace : WordTrace (prefixWord ++ tailWord_14473) baseStart_14473 baseEnd_14473 := by
    simpa [prefixWord, tailWord_14473, baseEnd_14473] using wordTrace_append hprefix tailTrace_14473
  have hstable : (prefixWord ++ tailWord_14473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14473).length < 2 ^ (prefixWord ++ tailWord_14473).sum := by decide
  have hdescent : baseEnd_14473 < baseStart_14473 := by decide
  rcases family_descends (prefixWord ++ tailWord_14473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14510 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_14510 : Nat := 118140960795 + 14510 * 2 ^ 59
def prefixEnd_14510 : Nat := 4983230072969 + 3 ^ 40 * 14510 * 2
def baseEnd_14510 : Nat := 3311379687485983670345

theorem tailTrace_14510 : CollatzResearch.WordTrace tailWord_14510 prefixEnd_14510 3311379687485983670345 := by
  unfold tailWord_14510
  simp only [CollatzResearch.WordTrace]
  refine ⟨66152897180027869477123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 352815451626815303877989 66152897180027869477123)
  ·
    refine ⟨99229345770041804215685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66152897180027869477123 99229345770041804215685)
    ·
      refine ⟨18605502331882838290441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99229345770041804215685 18605502331882838290441)
      ·
        refine ⟨13954126748912128717831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18605502331882838290441 13954126748912128717831)
        ·
          refine ⟨20931190123368193076747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954126748912128717831 20931190123368193076747)
          ·
            refine ⟨31396785185052289615121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20931190123368193076747 31396785185052289615121)
            ·
              refine ⟨23547588888789217211341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31396785185052289615121 23547588888789217211341)
              ·
                refine ⟨8830345833295956454253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23547588888789217211341 8830345833295956454253)
                ·
                  refine ⟨3311379687485983670345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830345833295956454253 3311379687485983670345)
                  ·
                    rfl

theorem cell21_14510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_14510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14510 prefixEnd_14510 := by exact prefixLift 14510
  have htrace : WordTrace (prefixWord ++ tailWord_14510) baseStart_14510 baseEnd_14510 := by
    simpa [prefixWord, tailWord_14510, baseEnd_14510] using wordTrace_append hprefix tailTrace_14510
  have hstable : (prefixWord ++ tailWord_14510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14510).length < 2 ^ (prefixWord ++ tailWord_14510).sum := by decide
  have hdescent : baseEnd_14510 < baseStart_14510 := by decide
  rcases family_descends (prefixWord ++ tailWord_14510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14577 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_14577 : Nat := 118140960795 + 14577 * 2 ^ 59
def prefixEnd_14577 : Nat := 4983230072969 + 3 ^ 40 * 14577 * 2
def baseEnd_14577 : Nat := 3326670000308756053541

theorem tailTrace_14577 : CollatzResearch.WordTrace tailWord_14577 prefixEnd_14577 3326670000308756053541 := by
  unfold tailWord_14577
  simp only [CollatzResearch.WordTrace]
  refine ⟨531666868197493398505985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 354444578798328932337323 531666868197493398505985)
  ·
    refine ⟨398750151148120048879489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531666868197493398505985 398750151148120048879489)
    ·
      refine ⟨299062613361090036659617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398750151148120048879489 299062613361090036659617)
      ·
        refine ⟨224296960020817527494713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299062613361090036659617 224296960020817527494713)
        ·
          refine ⟨168222720015613145621035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224296960020817527494713 168222720015613145621035)
          ·
            refine ⟨252334080023419718431553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168222720015613145621035 252334080023419718431553)
            ·
              refine ⟨189250560017564788823665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252334080023419718431553 189250560017564788823665)
              ·
                refine ⟨141937920013173591617749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189250560017564788823665 141937920013173591617749)
                ·
                  refine ⟨3326670000308756053541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141937920013173591617749 3326670000308756053541)
                  ·
                    rfl

theorem cell21_14577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_14577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14577 prefixEnd_14577 := by exact prefixLift 14577
  have htrace : WordTrace (prefixWord ++ tailWord_14577) baseStart_14577 baseEnd_14577 := by
    simpa [prefixWord, tailWord_14577, baseEnd_14577] using wordTrace_append hprefix tailTrace_14577
  have hstable : (prefixWord ++ tailWord_14577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14577).length < 2 ^ (prefixWord ++ tailWord_14577).sum := by decide
  have hdescent : baseEnd_14577 < baseStart_14577 := by decide
  rcases family_descends (prefixWord ++ tailWord_14577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14642 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_14642 : Nat := 118140960795 + 14642 * 2 ^ 59
def prefixEnd_14642 : Nat := 4983230072969 + 3 ^ 40 * 14642 * 2
def baseEnd_14642 : Nat := 3341503885883087470075

theorem tailTrace_14642 : CollatzResearch.WordTrace tailWord_14642 prefixEnd_14642 3341503885883087470075 := by
  unfold tailWord_14642
  simp only [CollatzResearch.WordTrace]
  refine ⟨133509403240502374905545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 356025075308006333081453 133509403240502374905545)
  ·
    refine ⟨100132052430376781179159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133509403240502374905545 100132052430376781179159)
    ·
      refine ⟨150198078645565171768739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100132052430376781179159 150198078645565171768739)
      ·
        refine ⟨225297117968347757653109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150198078645565171768739 225297117968347757653109)
        ·
          refine ⟨21121604809532602279979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225297117968347757653109 21121604809532602279979)
          ·
            refine ⟨31682407214298903419969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21121604809532602279979 31682407214298903419969)
            ·
              refine ⟨23761805410724177564977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31682407214298903419969 23761805410724177564977)
              ·
                refine ⟨17821354058043133173733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23761805410724177564977 17821354058043133173733)
                ·
                  refine ⟨3341503885883087470075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17821354058043133173733 3341503885883087470075)
                  ·
                    rfl

theorem cell21_14642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_14642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14642 prefixEnd_14642 := by exact prefixLift 14642
  have htrace : WordTrace (prefixWord ++ tailWord_14642) baseStart_14642 baseEnd_14642 := by
    simpa [prefixWord, tailWord_14642, baseEnd_14642] using wordTrace_append hprefix tailTrace_14642
  have hstable : (prefixWord ++ tailWord_14642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14642).length < 2 ^ (prefixWord ++ tailWord_14642).sum := by decide
  have hdescent : baseEnd_14642 < baseStart_14642 := by decide
  rcases family_descends (prefixWord ++ tailWord_14642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14732 : List Nat := [2, 2, 1, 2, 1, 6, 2, 5]
def baseStart_14732 : Nat := 118140960795 + 14732 * 2 ^ 59
def prefixEnd_14732 : Nat := 4983230072969 + 3 ^ 40 * 14732 * 2
def baseEnd_14732 : Nat := 1120681037354310323297

theorem tailTrace_14732 : CollatzResearch.WordTrace tailWord_14732 prefixEnd_14732 1120681037354310323297 := by
  unfold tailWord_14732
  simp only [CollatzResearch.WordTrace]
  refine ⟨268660091317977435199225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 358213455090636580265633 268660091317977435199225)
  ·
    refine ⟨201495068488483076399419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268660091317977435199225 201495068488483076399419)
    ·
      refine ⟨302242602732724614599129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201495068488483076399419 302242602732724614599129)
      ·
        refine ⟨226681952049543460949347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302242602732724614599129 226681952049543460949347)
        ·
          refine ⟨340022928074315191424021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226681952049543460949347 340022928074315191424021)
          ·
            refine ⟨15938574753483524598001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340022928074315191424021 15938574753483524598001)
            ·
              refine ⟨11953931065112643448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15938574753483524598001 11953931065112643448501)
              ·
                refine ⟨1120681037354310323297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11953931065112643448501 1120681037354310323297)
                ·
                  rfl

theorem cell21_14732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_14732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14732 prefixEnd_14732 := by exact prefixLift 14732
  have htrace : WordTrace (prefixWord ++ tailWord_14732) baseStart_14732 baseEnd_14732 := by
    simpa [prefixWord, tailWord_14732, baseEnd_14732] using wordTrace_append hprefix tailTrace_14732
  have hstable : (prefixWord ++ tailWord_14732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14732).length < 2 ^ (prefixWord ++ tailWord_14732).sum := by decide
  have hdescent : baseEnd_14732 < baseStart_14732 := by decide
  rcases family_descends (prefixWord ++ tailWord_14732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14777 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_14777 : Nat := 118140960795 + 14777 * 2 ^ 59
def prefixEnd_14777 : Nat := 4983230072969 + 3 ^ 40 * 14777 * 2
def baseEnd_14777 : Nat := 3372312725152852719799

theorem tailTrace_14777 : CollatzResearch.WordTrace tailWord_14777 prefixEnd_14777 3372312725152852719799 := by
  unfold tailWord_14777
  simp only [CollatzResearch.WordTrace]
  refine ⟨538961467472927555786585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 359307644981951703857723 538961467472927555786585)
  ·
    refine ⟨404221100604695666839939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538961467472927555786585 404221100604695666839939)
    ·
      refine ⟨606331650907043500259909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404221100604695666839939 606331650907043500259909)
      ·
        refine ⟨113687184545070656298733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 606331650907043500259909 113687184545070656298733)
        ·
          refine ⟨42632694204401496112025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113687184545070656298733 42632694204401496112025)
          ·
            refine ⟨31974520653301122084019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42632694204401496112025 31974520653301122084019)
            ·
              refine ⟨47961780979951683126029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31974520653301122084019 47961780979951683126029)
              ·
                refine ⟨17985667867481881172261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47961780979951683126029 17985667867481881172261)
                ·
                  refine ⟨3372312725152852719799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17985667867481881172261 3372312725152852719799)
                  ·
                    rfl

theorem cell21_14777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_14777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14777 prefixEnd_14777 := by exact prefixLift 14777
  have htrace : WordTrace (prefixWord ++ tailWord_14777) baseStart_14777 baseEnd_14777 := by
    simpa [prefixWord, tailWord_14777, baseEnd_14777] using wordTrace_append hprefix tailTrace_14777
  have hstable : (prefixWord ++ tailWord_14777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14777).length < 2 ^ (prefixWord ++ tailWord_14777).sum := by decide
  have hdescent : baseEnd_14777 < baseStart_14777 := by decide
  rcases family_descends (prefixWord ++ tailWord_14777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14926 : List Nat := [4, 1, 1, 1, 1, 2, 11]
def baseStart_14926 : Nat := 118140960795 + 14926 * 2 ^ 59
def prefixEnd_14926 : Nat := 4983230072969 + 3 ^ 40 * 14926 * 2
def baseEnd_14926 : Nat := 378479617240189415129

theorem tailTrace_14926 : CollatzResearch.WordTrace tailWord_14926 prefixEnd_14926 378479617240189415129 := by
  unfold tailWord_14926
  simp only [CollatzResearch.WordTrace]
  refine ⟨68049492991640750370079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 362930629288750668640421 68049492991640750370079)
  ·
    refine ⟨102074239487461125555119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68049492991640750370079 102074239487461125555119)
    ·
      refine ⟨153111359231191688332679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102074239487461125555119 153111359231191688332679)
      ·
        refine ⟨229667038846787532499019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153111359231191688332679 229667038846787532499019)
        ·
          refine ⟨344500558270181298748529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229667038846787532499019 344500558270181298748529)
          ·
            refine ⟨258375418702635974061397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344500558270181298748529 258375418702635974061397)
            ·
              refine ⟨378479617240189415129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 258375418702635974061397 378479617240189415129)
              ·
                rfl

theorem cell21_14926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 11].length) (baseStart_14926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14926 prefixEnd_14926 := by exact prefixLift 14926
  have htrace : WordTrace (prefixWord ++ tailWord_14926) baseStart_14926 baseEnd_14926 := by
    simpa [prefixWord, tailWord_14926, baseEnd_14926] using wordTrace_append hprefix tailTrace_14926
  have hstable : (prefixWord ++ tailWord_14926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14926).length < 2 ^ (prefixWord ++ tailWord_14926).sum := by decide
  have hdescent : baseEnd_14926 < baseStart_14926 := by decide
  rcases family_descends (prefixWord ++ tailWord_14926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14932 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_14932 : Nat := 118140960795 + 14932 * 2 ^ 59
def prefixEnd_14932 : Nat := 4983230072969 + 3 ^ 40 * 14932 * 2
def baseEnd_14932 : Nat := 3407685836907027636149

theorem tailTrace_14932 : CollatzResearch.WordTrace tailWord_14932 prefixEnd_14932 3407685836907027636149 := by
  unfold tailWord_14932
  simp only [CollatzResearch.WordTrace]
  refine ⟨272307390955694513839525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 363076521274259351786033 272307390955694513839525)
  ·
    refine ⟨51057635804192721344911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272307390955694513839525 51057635804192721344911)
    ·
      refine ⟨76586453706289082017367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51057635804192721344911 76586453706289082017367)
      ·
        refine ⟨114879680559433623026051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76586453706289082017367 114879680559433623026051)
        ·
          refine ⟨172319520839150434539077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114879680559433623026051 172319520839150434539077)
          ·
            refine ⟨32309910157340706476077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172319520839150434539077 32309910157340706476077)
            ·
              refine ⟨12116216309002764928529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32309910157340706476077 12116216309002764928529)
              ·
                refine ⟨9087162231752073696397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116216309002764928529 9087162231752073696397)
                ·
                  refine ⟨3407685836907027636149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9087162231752073696397 3407685836907027636149)
                  ·
                    rfl

theorem cell21_14932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_14932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14932 prefixEnd_14932 := by exact prefixLift 14932
  have htrace : WordTrace (prefixWord ++ tailWord_14932) baseStart_14932 baseEnd_14932 := by
    simpa [prefixWord, tailWord_14932, baseEnd_14932] using wordTrace_append hprefix tailTrace_14932
  have hstable : (prefixWord ++ tailWord_14932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14932).length < 2 ^ (prefixWord ++ tailWord_14932).sum := by decide
  have hdescent : baseEnd_14932 < baseStart_14932 := by decide
  rcases family_descends (prefixWord ++ tailWord_14932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14971 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_14971 : Nat := 118140960795 + 14971 * 2 ^ 59
def prefixEnd_14971 : Nat := 4983230072969 + 3 ^ 40 * 14971 * 2
def baseEnd_14971 : Nat := 3416586168251626486069

theorem tailTrace_14971 : CollatzResearch.WordTrace tailWord_14971 prefixEnd_14971 3416586168251626486069 := by
  unfold tailWord_14971
  simp only [CollatzResearch.WordTrace]
  refine ⟨546037228770098688348767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 364024819180065792232511 546037228770098688348767)
  ·
    refine ⟨819055843155148032523151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546037228770098688348767 819055843155148032523151)
    ·
      refine ⟨1228583764732722048784727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819055843155148032523151 1228583764732722048784727)
      ·
        refine ⟨1842875647099083073177091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228583764732722048784727 1842875647099083073177091)
        ·
          refine ⟨2764313470648624609765637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842875647099083073177091 2764313470648624609765637)
          ·
            refine ⟨518308775746617114331057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2764313470648624609765637 518308775746617114331057)
            ·
              refine ⟨388731581809962835748293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518308775746617114331057 388731581809962835748293)
              ·
                refine ⟨72887171589368031702805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388731581809962835748293 72887171589368031702805)
                ·
                  refine ⟨3416586168251626486069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72887171589368031702805 3416586168251626486069)
                  ·
                    rfl

theorem cell21_14971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_14971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_14971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_14971 prefixEnd_14971 := by exact prefixLift 14971
  have htrace : WordTrace (prefixWord ++ tailWord_14971) baseStart_14971 baseEnd_14971 := by
    simpa [prefixWord, tailWord_14971, baseEnd_14971] using wordTrace_append hprefix tailTrace_14971
  have hstable : (prefixWord ++ tailWord_14971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14971).length < 2 ^ (prefixWord ++ tailWord_14971).sum := by decide
  have hdescent : baseEnd_14971 < baseStart_14971 := by decide
  rcases family_descends (prefixWord ++ tailWord_14971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15050 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_15050 : Nat := 118140960795 + 15050 * 2 ^ 59
def prefixEnd_15050 : Nat := 4983230072969 + 3 ^ 40 * 15050 * 2
def baseEnd_15050 : Nat := 3434615044565044669241

theorem tailTrace_15050 : CollatzResearch.WordTrace tailWord_15050 prefixEnd_15050 3434615044565044669241 := by
  unfold tailWord_15050
  simp only [CollatzResearch.WordTrace]
  refine ⟨137229648870973795118651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 365945730322596786983069 137229648870973795118651)
  ·
    refine ⟨205844473306460692677977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137229648870973795118651 205844473306460692677977)
    ·
      refine ⟨154383354979845519508483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205844473306460692677977 154383354979845519508483)
      ·
        refine ⟨231575032469768279262725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154383354979845519508483 231575032469768279262725)
        ·
          refine ⟨43420318588081552361761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231575032469768279262725 43420318588081552361761)
          ·
            refine ⟨32565238941061164271321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43420318588081552361761 32565238941061164271321)
            ·
              refine ⟨24423929205795873203491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32565238941061164271321 24423929205795873203491)
              ·
                refine ⟨36635893808693809805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24423929205795873203491 36635893808693809805237)
                ·
                  refine ⟨3434615044565044669241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36635893808693809805237 3434615044565044669241)
                  ·
                    rfl

theorem cell21_15050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_15050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15050 prefixEnd_15050 := by exact prefixLift 15050
  have htrace : WordTrace (prefixWord ++ tailWord_15050) baseStart_15050 baseEnd_15050 := by
    simpa [prefixWord, tailWord_15050, baseEnd_15050] using wordTrace_append hprefix tailTrace_15050
  have hstable : (prefixWord ++ tailWord_15050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15050).length < 2 ^ (prefixWord ++ tailWord_15050).sum := by decide
  have hdescent : baseEnd_15050 < baseStart_15050 := by decide
  rcases family_descends (prefixWord ++ tailWord_15050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15157 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_15157 : Nat := 118140960795 + 15157 * 2 ^ 59
def prefixEnd_15157 : Nat := 4983230072969 + 3 ^ 40 * 15157 * 2
def baseEnd_15157 : Nat := 3459033902356636385689

theorem tailTrace_15157 : CollatzResearch.WordTrace tailWord_15157 prefixEnd_15157 3459033902356636385689 := by
  unfold tailWord_15157
  simp only [CollatzResearch.WordTrace]
  refine ⟨552821206096252454619725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 368547470730834969746483 552821206096252454619725)
  ·
    refine ⟨207307952286094670482397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 552821206096252454619725 207307952286094670482397)
    ·
      refine ⟨77740482107285501430899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207307952286094670482397 77740482107285501430899)
      ·
        refine ⟨116610723160928252146349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77740482107285501430899 116610723160928252146349)
        ·
          refine ⟨43729021185348094554881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116610723160928252146349 43729021185348094554881)
          ·
            refine ⟨32796765889011070916161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43729021185348094554881 32796765889011070916161)
            ·
              refine ⟨24597574416758303187121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32796765889011070916161 24597574416758303187121)
              ·
                refine ⟨18448180812568727390341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24597574416758303187121 18448180812568727390341)
                ·
                  refine ⟨3459033902356636385689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18448180812568727390341 3459033902356636385689)
                  ·
                    rfl

theorem cell21_15157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_15157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15157 prefixEnd_15157 := by exact prefixLift 15157
  have htrace : WordTrace (prefixWord ++ tailWord_15157) baseStart_15157 baseEnd_15157 := by
    simpa [prefixWord, tailWord_15157, baseEnd_15157] using wordTrace_append hprefix tailTrace_15157
  have hstable : (prefixWord ++ tailWord_15157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15157).length < 2 ^ (prefixWord ++ tailWord_15157).sum := by decide
  have hdescent : baseEnd_15157 < baseStart_15157 := by decide
  rcases family_descends (prefixWord ++ tailWord_15157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15168 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_15168 : Nat := 118140960795 + 15168 * 2 ^ 59
def prefixEnd_15168 : Nat := 4983230072969 + 3 ^ 40 * 15168 * 2
def baseEnd_15168 : Nat := 3461544252223061702333

theorem tailTrace_15168 : CollatzResearch.WordTrace tailWord_15168 prefixEnd_15168 3461544252223061702333 := by
  unfold tailWord_15168
  simp only [CollatzResearch.WordTrace]
  refine ⟨276611204528200666635079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 368814939370934222180105 276611204528200666635079)
  ·
    refine ⟨414916806792300999952619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276611204528200666635079 414916806792300999952619)
    ·
      refine ⟨622375210188451499928929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414916806792300999952619 622375210188451499928929)
      ·
        refine ⟨466781407641338624946697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622375210188451499928929 466781407641338624946697)
        ·
          refine ⟨350086055731003968710023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466781407641338624946697 350086055731003968710023)
          ·
            refine ⟨525129083596505953065035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350086055731003968710023 525129083596505953065035)
            ·
              refine ⟨787693625394758929597553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525129083596505953065035 787693625394758929597553)
              ·
                refine ⟨590770219046069197198165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787693625394758929597553 590770219046069197198165)
                ·
                  refine ⟨3461544252223061702333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 590770219046069197198165 3461544252223061702333)
                  ·
                    rfl

theorem cell21_15168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_15168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15168 prefixEnd_15168 := by exact prefixLift 15168
  have htrace : WordTrace (prefixWord ++ tailWord_15168) baseStart_15168 baseEnd_15168 := by
    simpa [prefixWord, tailWord_15168, baseEnd_15168] using wordTrace_append hprefix tailTrace_15168
  have hstable : (prefixWord ++ tailWord_15168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15168).length < 2 ^ (prefixWord ++ tailWord_15168).sum := by decide
  have hdescent : baseEnd_15168 < baseStart_15168 := by decide
  rcases family_descends (prefixWord ++ tailWord_15168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15188 : List Nat := [2, 4, 1, 1, 4, 1, 3, 5]
def baseStart_15188 : Nat := 118140960795 + 15188 * 2 ^ 59
def prefixEnd_15188 : Nat := 4983230072969 + 3 ^ 40 * 15188 * 2
def baseEnd_15188 : Nat := 1155369508235823789653

theorem tailTrace_15188 : CollatzResearch.WordTrace tailWord_15188 prefixEnd_15188 1155369508235823789653 := by
  unfold tailWord_15188
  simp only [CollatzResearch.WordTrace]
  refine ⟨276975934491972374499109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 369301245989296499332145 276975934491972374499109)
  ·
    refine ⟨51932987717244820218583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276975934491972374499109 51932987717244820218583)
    ·
      refine ⟨77899481575867230327875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51932987717244820218583 77899481575867230327875)
      ·
        refine ⟨116849222363800845491813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77899481575867230327875 116849222363800845491813)
        ·
          refine ⟨21909229193212658529715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116849222363800845491813 21909229193212658529715)
          ·
            refine ⟨32863843789818987794573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21909229193212658529715 32863843789818987794573)
            ·
              refine ⟨12323941421182120422965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32863843789818987794573 12323941421182120422965)
              ·
                refine ⟨1155369508235823789653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12323941421182120422965 1155369508235823789653)
                ·
                  rfl

theorem cell21_15188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_15188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15188 prefixEnd_15188 := by exact prefixLift 15188
  have htrace : WordTrace (prefixWord ++ tailWord_15188) baseStart_15188 baseEnd_15188 := by
    simpa [prefixWord, tailWord_15188, baseEnd_15188] using wordTrace_append hprefix tailTrace_15188
  have hstable : (prefixWord ++ tailWord_15188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15188).length < 2 ^ (prefixWord ++ tailWord_15188).sum := by decide
  have hdescent : baseEnd_15188 < baseStart_15188 := by decide
  rcases family_descends (prefixWord ++ tailWord_15188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15199 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_15199 : Nat := 118140960795 + 15199 * 2 ^ 59
def prefixEnd_15199 : Nat := 4983230072969 + 3 ^ 40 * 15199 * 2
def baseEnd_15199 : Nat := 3468618874573896685603

theorem tailTrace_15199 : CollatzResearch.WordTrace tailWord_15199 prefixEnd_15199 3468618874573896685603 := by
  unfold tailWord_15199
  simp only [CollatzResearch.WordTrace]
  refine ⟨554353071944093627648651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 369568714629395751765767 554353071944093627648651)
  ·
    refine ⟨831529607916140441472977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554353071944093627648651 831529607916140441472977)
    ·
      refine ⟨623647205937105331104733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831529607916140441472977 623647205937105331104733)
      ·
        refine ⟨233867702226414499164275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623647205937105331104733 233867702226414499164275)
        ·
          refine ⟨350801553339621748746413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233867702226414499164275 350801553339621748746413)
          ·
            refine ⟨131550582502358155779905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350801553339621748746413 131550582502358155779905)
            ·
              refine ⟨98662936876768616834929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131550582502358155779905 98662936876768616834929)
              ·
                refine ⟨73997202657576462626197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98662936876768616834929 73997202657576462626197)
                ·
                  refine ⟨3468618874573896685603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73997202657576462626197 3468618874573896685603)
                  ·
                    rfl

theorem cell21_15199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_15199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15199 prefixEnd_15199 := by exact prefixLift 15199
  have htrace : WordTrace (prefixWord ++ tailWord_15199) baseStart_15199 baseEnd_15199 := by
    simpa [prefixWord, tailWord_15199, baseEnd_15199] using wordTrace_append hprefix tailTrace_15199
  have hstable : (prefixWord ++ tailWord_15199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15199).length < 2 ^ (prefixWord ++ tailWord_15199).sum := by decide
  have hdescent : baseEnd_15199 < baseStart_15199 := by decide
  rcases family_descends (prefixWord ++ tailWord_15199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15216 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_15216 : Nat := 118140960795 + 15216 * 2 ^ 59
def prefixEnd_15216 : Nat := 4983230072969 + 3 ^ 40 * 15216 * 2
def baseEnd_15216 : Nat := 3472498506185644902235

theorem tailTrace_15216 : CollatzResearch.WordTrace tailWord_15216 prefixEnd_15216 3472498506185644902235 := by
  unfold tailWord_15216
  simp only [CollatzResearch.WordTrace]
  refine ⟨277486556441252765508751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 369982075255003687345001 277486556441252765508751)
  ·
    refine ⟨416229834661879148263127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277486556441252765508751 416229834661879148263127)
    ·
      refine ⟨624344751992818722394691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416229834661879148263127 624344751992818722394691)
      ·
        refine ⟨936517127989228083592037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624344751992818722394691 936517127989228083592037)
        ·
          refine ⟨175596961497980265673507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 936517127989228083592037 175596961497980265673507)
          ·
            refine ⟨263395442246970398510261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175596961497980265673507 263395442246970398510261)
            ·
              refine ⟨24693322710653474860337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263395442246970398510261 24693322710653474860337)
              ·
                refine ⟨18519992032990106145253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24693322710653474860337 18519992032990106145253)
                ·
                  refine ⟨3472498506185644902235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18519992032990106145253 3472498506185644902235)
                  ·
                    rfl

theorem cell21_15216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_15216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15216 prefixEnd_15216 := by exact prefixLift 15216
  have htrace : WordTrace (prefixWord ++ tailWord_15216) baseStart_15216 baseEnd_15216 := by
    simpa [prefixWord, tailWord_15216, baseEnd_15216] using wordTrace_append hprefix tailTrace_15216
  have hstable : (prefixWord ++ tailWord_15216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15216).length < 2 ^ (prefixWord ++ tailWord_15216).sum := by decide
  have hdescent : baseEnd_15216 < baseStart_15216 := by decide
  rcases family_descends (prefixWord ++ tailWord_15216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15402 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_15402 : Nat := 118140960795 + 15402 * 2 ^ 59
def prefixEnd_15402 : Nat := 4983230072969 + 3 ^ 40 * 15402 * 2
def baseEnd_15402 : Nat := 3514946240290654801855

theorem tailTrace_15402 : CollatzResearch.WordTrace tailWord_15402 prefixEnd_15402 3514946240290654801855 := by
  unfold tailWord_15402
  simp only [CollatzResearch.WordTrace]
  refine ⟨140439272552164824322115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 374504726805772864858973 140439272552164824322115)
  ·
    refine ⟨210658908828247236483173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140439272552164824322115 210658908828247236483173)
    ·
      refine ⟨39498545405296356840595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210658908828247236483173 39498545405296356840595)
      ·
        refine ⟨59247818107944535260893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39498545405296356840595 59247818107944535260893)
        ·
          refine ⟨22217931790479200722835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59247818107944535260893 22217931790479200722835)
          ·
            refine ⟨33326897685718801084253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22217931790479200722835 33326897685718801084253)
            ·
              refine ⟨12497586632144550406595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33326897685718801084253 12497586632144550406595)
              ·
                refine ⟨18746379948216825609893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12497586632144550406595 18746379948216825609893)
                ·
                  refine ⟨3514946240290654801855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18746379948216825609893 3514946240290654801855)
                  ·
                    rfl

theorem cell21_15402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_15402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15402 prefixEnd_15402 := by exact prefixLift 15402
  have htrace : WordTrace (prefixWord ++ tailWord_15402) baseStart_15402 baseEnd_15402 := by
    simpa [prefixWord, tailWord_15402, baseEnd_15402] using wordTrace_append hprefix tailTrace_15402
  have hstable : (prefixWord ++ tailWord_15402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15402).length < 2 ^ (prefixWord ++ tailWord_15402).sum := by decide
  have hdescent : baseEnd_15402 < baseStart_15402 := by decide
  rcases family_descends (prefixWord ++ tailWord_15402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15441 : List Nat := [1, 2, 2, 1, 3, 1, 11]
def baseStart_15441 : Nat := 118140960795 + 15441 * 2 ^ 59
def prefixEnd_15441 : Nat := 4983230072969 + 3 ^ 40 * 15441 * 2
def baseEnd_15441 : Nat := 391538507959472627975

theorem tailTrace_15441 : CollatzResearch.WordTrace tailWord_15441 prefixEnd_15441 391538507959472627975 := by
  unfold tailWord_15441
  simp only [CollatzResearch.WordTrace]
  refine ⟨563179537067368957958177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 375453024711579305305451 563179537067368957958177)
  ·
    refine ⟨422384652800526718468633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 563179537067368957958177 422384652800526718468633)
    ·
      refine ⟨316788489600395038851475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422384652800526718468633 316788489600395038851475)
      ·
        refine ⟨475182734400592558277213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316788489600395038851475 475182734400592558277213)
        ·
          refine ⟨178193525400222209353955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475182734400592558277213 178193525400222209353955)
          ·
            refine ⟨267290288100333314030933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178193525400222209353955 267290288100333314030933)
            ·
              refine ⟨391538507959472627975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 267290288100333314030933 391538507959472627975)
              ·
                rfl

theorem cell21_15441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 11].length) (baseStart_15441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15441 prefixEnd_15441 := by exact prefixLift 15441
  have htrace : WordTrace (prefixWord ++ tailWord_15441) baseStart_15441 baseEnd_15441 := by
    simpa [prefixWord, tailWord_15441, baseEnd_15441] using wordTrace_append hprefix tailTrace_15441
  have hstable : (prefixWord ++ tailWord_15441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15441).length < 2 ^ (prefixWord ++ tailWord_15441).sum := by decide
  have hdescent : baseEnd_15441 < baseStart_15441 := by decide
  rcases family_descends (prefixWord ++ tailWord_15441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15472 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_15472 : Nat := 118140960795 + 15472 * 2 ^ 59
def prefixEnd_15472 : Nat := 4983230072969 + 3 ^ 40 * 15472 * 2
def baseEnd_15472 : Nat := 3530921193986088635045

theorem tailTrace_15472 : CollatzResearch.WordTrace tailWord_15472 prefixEnd_15472 3530921193986088635045 := by
  unfold tailWord_15472
  simp only [CollatzResearch.WordTrace]
  refine ⟨282155099977530626168335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 376206799970040834891113 282155099977530626168335)
  ·
    refine ⟨423232649966295939252503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282155099977530626168335 423232649966295939252503)
    ·
      refine ⟨634848974949443908878755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423232649966295939252503 634848974949443908878755)
      ·
        refine ⟨952273462424165863318133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634848974949443908878755 952273462424165863318133)
        ·
          refine ⟨89275637102265549686075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 952273462424165863318133 89275637102265549686075)
          ·
            refine ⟨133913455653398324529113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89275637102265549686075 133913455653398324529113)
            ·
              refine ⟨100435091740048743396835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133913455653398324529113 100435091740048743396835)
              ·
                refine ⟨150652637610073115095253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100435091740048743396835 150652637610073115095253)
                ·
                  refine ⟨3530921193986088635045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150652637610073115095253 3530921193986088635045)
                  ·
                    rfl

theorem cell21_15472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_15472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15472 prefixEnd_15472 := by exact prefixLift 15472
  have htrace : WordTrace (prefixWord ++ tailWord_15472) baseStart_15472 baseEnd_15472 := by
    simpa [prefixWord, tailWord_15472, baseEnd_15472] using wordTrace_append hprefix tailTrace_15472
  have hstable : (prefixWord ++ tailWord_15472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15472).length < 2 ^ (prefixWord ++ tailWord_15472).sum := by decide
  have hdescent : baseEnd_15472 < baseStart_15472 := by decide
  rcases family_descends (prefixWord ++ tailWord_15472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15554 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_15554 : Nat := 118140960795 + 15554 * 2 ^ 59
def prefixEnd_15554 : Nat := 4983230072969 + 3 ^ 40 * 15554 * 2
def baseEnd_15554 : Nat := 3549634711172168268211

theorem tailTrace_15554 : CollatzResearch.WordTrace tailWord_15554 prefixEnd_15554 3549634711172168268211 := by
  unfold tailWord_15554
  simp only [CollatzResearch.WordTrace]
  refine ⟨141825246414497314205429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 378200657105326171214477 141825246414497314205429)
  ·
    refine ⟨13296116851359123206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141825246414497314205429 13296116851359123206759)
    ·
      refine ⟨19944175277038684810139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13296116851359123206759 19944175277038684810139)
      ·
        refine ⟨29916262915558027215209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19944175277038684810139 29916262915558027215209)
        ·
          refine ⟨22437197186668520411407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29916262915558027215209 22437197186668520411407)
          ·
            refine ⟨33655795780002780617111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22437197186668520411407 33655795780002780617111)
            ·
              refine ⟨50483693670004170925667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33655795780002780617111 50483693670004170925667)
              ·
                refine ⟨75725540505006256388501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50483693670004170925667 75725540505006256388501)
                ·
                  refine ⟨3549634711172168268211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75725540505006256388501 3549634711172168268211)
                  ·
                    rfl

theorem cell21_15554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_15554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15554 prefixEnd_15554 := by exact prefixLift 15554
  have htrace : WordTrace (prefixWord ++ tailWord_15554) baseStart_15554 baseEnd_15554 := by
    simpa [prefixWord, tailWord_15554, baseEnd_15554] using wordTrace_append hprefix tailTrace_15554
  have hstable : (prefixWord ++ tailWord_15554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15554).length < 2 ^ (prefixWord ++ tailWord_15554).sum := by decide
  have hdescent : baseEnd_15554 < baseStart_15554 := by decide
  rcases family_descends (prefixWord ++ tailWord_15554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15599 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 3]
def baseStart_15599 : Nat := 118140960795 + 15599 * 2 ^ 59
def prefixEnd_15599 : Nat := 4983230072969 + 3 ^ 40 * 15599 * 2
def baseEnd_15599 : Nat := 3559904324262090018119

theorem tailTrace_15599 : CollatzResearch.WordTrace tailWord_15599 prefixEnd_15599 3559904324262090018119 := by
  unfold tailWord_15599
  simp only [CollatzResearch.WordTrace]
  refine ⟨568942270494961942209851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 379294846996641294806567 568942270494961942209851)
  ·
    refine ⟨853413405742442913314777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 568942270494961942209851 853413405742442913314777)
    ·
      refine ⟨640060054306832184986083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 853413405742442913314777 640060054306832184986083)
      ·
        refine ⟨960090081460248277479125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640060054306832184986083 960090081460248277479125)
        ·
          refine ⟨22502111284224569003417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 960090081460248277479125 22502111284224569003417)
          ·
            refine ⟨16876583463168426752563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22502111284224569003417 16876583463168426752563)
            ·
              refine ⟨25314875194752640128845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876583463168426752563 25314875194752640128845)
              ·
                refine ⟨9493078198032240048317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25314875194752640128845 9493078198032240048317)
                ·
                  refine ⟨3559904324262090018119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9493078198032240048317 3559904324262090018119)
                  ·
                    rfl

theorem cell21_15599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].length) (baseStart_15599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15599 prefixEnd_15599 := by exact prefixLift 15599
  have htrace : WordTrace (prefixWord ++ tailWord_15599) baseStart_15599 baseEnd_15599 := by
    simpa [prefixWord, tailWord_15599, baseEnd_15599] using wordTrace_append hprefix tailTrace_15599
  have hstable : (prefixWord ++ tailWord_15599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15599).length < 2 ^ (prefixWord ++ tailWord_15599).sum := by decide
  have hdescent : baseEnd_15599 < baseStart_15599 := by decide
  rcases family_descends (prefixWord ++ tailWord_15599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15669 : List Nat := [1, 3, 3, 1, 2, 11]
def baseStart_15669 : Nat := 118140960795 + 15669 * 2 ^ 59
def prefixEnd_15669 : Nat := 4983230072969 + 3 ^ 40 * 15669 * 2
def baseEnd_15669 : Nat := 132439973257686068567

theorem tailTrace_15669 : CollatzResearch.WordTrace tailWord_15669 prefixEnd_15669 132439973257686068567 := by
  unfold tailWord_15669
  simp only [CollatzResearch.WordTrace]
  refine ⟨571495380241363897258061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 380996920160909264838707 571495380241363897258061)
  ·
    refine ⟨214310767590511461471773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 571495380241363897258061 214310767590511461471773)
    ·
      refine ⟨80366537846441798051915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214310767590511461471773 80366537846441798051915)
      ·
        refine ⟨120549806769662697077873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80366537846441798051915 120549806769662697077873)
        ·
          refine ⟨90412355077247022808405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120549806769662697077873 90412355077247022808405)
          ·
            refine ⟨132439973257686068567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 90412355077247022808405 132439973257686068567)
            ·
              rfl

theorem cell21_15669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 11].length) (baseStart_15669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15669 prefixEnd_15669 := by exact prefixLift 15669
  have htrace : WordTrace (prefixWord ++ tailWord_15669) baseStart_15669 baseEnd_15669 := by
    simpa [prefixWord, tailWord_15669, baseEnd_15669] using wordTrace_append hprefix tailTrace_15669
  have hstable : (prefixWord ++ tailWord_15669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15669).length < 2 ^ (prefixWord ++ tailWord_15669).sum := by decide
  have hdescent : baseEnd_15669 < baseStart_15669 := by decide
  rcases family_descends (prefixWord ++ tailWord_15669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15709 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 3]
def baseStart_15709 : Nat := 118140960795 + 15709 * 2 ^ 59
def prefixEnd_15709 : Nat := 4983230072969 + 3 ^ 40 * 15709 * 2
def baseEnd_15709 : Nat := 3585007822926343184561

theorem tailTrace_15709 : CollatzResearch.WordTrace tailWord_15709 prefixEnd_15709 3585007822926343184561 := by
  unfold tailWord_15709
  simp only [CollatzResearch.WordTrace]
  refine ⟨572954300096450728714181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 381969533397633819142787 572954300096450728714181)
  ·
    refine ⟨107428931268084511633909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 572954300096450728714181 107428931268084511633909)
    ·
      refine ⟨10071462306382922965679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107428931268084511633909 10071462306382922965679)
      ·
        refine ⟨15107193459574384448519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071462306382922965679 15107193459574384448519)
        ·
          refine ⟨22660790189361576672779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107193459574384448519 22660790189361576672779)
          ·
            refine ⟨33991185284042365009169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22660790189361576672779 33991185284042365009169)
            ·
              refine ⟨25493388963031773756877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33991185284042365009169 25493388963031773756877)
              ·
                refine ⟨9560020861136915158829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25493388963031773756877 9560020861136915158829)
                ·
                  refine ⟨3585007822926343184561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9560020861136915158829 3585007822926343184561)
                  ·
                    rfl

theorem cell21_15709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_15709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15709 prefixEnd_15709 := by exact prefixLift 15709
  have htrace : WordTrace (prefixWord ++ tailWord_15709) baseStart_15709 baseEnd_15709 := by
    simpa [prefixWord, tailWord_15709, baseEnd_15709] using wordTrace_append hprefix tailTrace_15709
  have hstable : (prefixWord ++ tailWord_15709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15709).length < 2 ^ (prefixWord ++ tailWord_15709).sum := by decide
  have hdescent : baseEnd_15709 < baseStart_15709 := by decide
  rcases family_descends (prefixWord ++ tailWord_15709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15768 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_15768 : Nat := 118140960795 + 15768 * 2 ^ 59
def prefixEnd_15768 : Nat := 4983230072969 + 3 ^ 40 * 15768 * 2
def baseEnd_15768 : Nat := 3598472426755351701107

theorem tailTrace_15768 : CollatzResearch.WordTrace tailWord_15768 prefixEnd_15768 3598472426755351701107 := by
  unfold tailWord_15768
  simp only [CollatzResearch.WordTrace]
  refine ⟨287553103441351902555979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 383404137921802536741305 287553103441351902555979)
  ·
    refine ⟨431329655162027853833969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287553103441351902555979 431329655162027853833969)
    ·
      refine ⟨323497241371520890375477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431329655162027853833969 323497241371520890375477)
      ·
        refine ⟨30327866378580083472701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323497241371520890375477 30327866378580083472701)
        ·
          refine ⟨11372949891967531302263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30327866378580083472701 11372949891967531302263)
          ·
            refine ⟨17059424837951296953395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372949891967531302263 17059424837951296953395)
            ·
              refine ⟨25589137256926945430093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059424837951296953395 25589137256926945430093)
              ·
                refine ⟨9595926471347604536285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25589137256926945430093 9595926471347604536285)
                ·
                  refine ⟨3598472426755351701107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9595926471347604536285 3598472426755351701107)
                  ·
                    rfl

theorem cell21_15768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_15768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15768 prefixEnd_15768 := by exact prefixLift 15768
  have htrace : WordTrace (prefixWord ++ tailWord_15768) baseStart_15768 baseEnd_15768 := by
    simpa [prefixWord, tailWord_15768, baseEnd_15768] using wordTrace_append hprefix tailTrace_15768
  have hstable : (prefixWord ++ tailWord_15768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15768).length < 2 ^ (prefixWord ++ tailWord_15768).sum := by decide
  have hdescent : baseEnd_15768 < baseStart_15768 := by decide
  rcases family_descends (prefixWord ++ tailWord_15768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15928 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_15928 : Nat := 118140960795 + 15928 * 2 ^ 59
def prefixEnd_15928 : Nat := 4983230072969 + 3 ^ 40 * 15928 * 2
def baseEnd_15928 : Nat := 3634986606630629034113

theorem tailTrace_15928 : CollatzResearch.WordTrace tailWord_15928 prefixEnd_15928 3634986606630629034113 := by
  unfold tailWord_15928
  simp only [CollatzResearch.WordTrace]
  refine ⟨290470943151525565468219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 387294590868700753957625 290470943151525565468219)
  ·
    refine ⟨435706414727288348202329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290470943151525565468219 435706414727288348202329)
    ·
      refine ⟨326779811045466261151747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435706414727288348202329 326779811045466261151747)
      ·
        refine ⟨490169716568199391727621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326779811045466261151747 490169716568199391727621)
        ·
          refine ⟨91906821856537385948929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490169716568199391727621 91906821856537385948929)
          ·
            refine ⟨68930116392403039461697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91906821856537385948929 68930116392403039461697)
            ·
              refine ⟨51697587294302279596273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68930116392403039461697 51697587294302279596273)
              ·
                refine ⟨38773190470726709697205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51697587294302279596273 38773190470726709697205)
                ·
                  refine ⟨3634986606630629034113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38773190470726709697205 3634986606630629034113)
                  ·
                    rfl

theorem cell21_15928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_15928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15928 prefixEnd_15928 := by exact prefixLift 15928
  have htrace : WordTrace (prefixWord ++ tailWord_15928) baseStart_15928 baseEnd_15928 := by
    simpa [prefixWord, tailWord_15928, baseEnd_15928] using wordTrace_append hprefix tailTrace_15928
  have hstable : (prefixWord ++ tailWord_15928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15928).length < 2 ^ (prefixWord ++ tailWord_15928).sum := by decide
  have hdescent : baseEnd_15928 < baseStart_15928 := by decide
  rcases family_descends (prefixWord ++ tailWord_15928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15973 : List Nat := [1, 3, 1, 3, 3, 1, 1, 8]
def baseStart_15973 : Nat := 118140960795 + 15973 * 2 ^ 59
def prefixEnd_15973 : Nat := 4983230072969 + 3 ^ 40 * 15973 * 2
def baseEnd_15973 : Nat := 1215085406573516928007

theorem tailTrace_15973 : CollatzResearch.WordTrace tailWord_15973 prefixEnd_15973 1215085406573516928007 := by
  unfold tailWord_15973
  simp only [CollatzResearch.WordTrace]
  refine ⟨582583171140023816324573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 388388780760015877549715 582583171140023816324573)
  ·
    refine ⟨218468689177508931121715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 582583171140023816324573 218468689177508931121715)
    ·
      refine ⟨327703033766263396682573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218468689177508931121715 327703033766263396682573)
      ·
        refine ⟨122888637662348773755965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327703033766263396682573 122888637662348773755965)
        ·
          refine ⟨46083239123380790158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122888637662348773755965 46083239123380790158487)
          ·
            refine ⟨69124858685071185237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46083239123380790158487 69124858685071185237731)
            ·
              refine ⟨103687288027606777856597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69124858685071185237731 103687288027606777856597)
              ·
                refine ⟨1215085406573516928007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 103687288027606777856597 1215085406573516928007)
                ·
                  rfl

theorem cell21_15973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_15973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15973 prefixEnd_15973 := by exact prefixLift 15973
  have htrace : WordTrace (prefixWord ++ tailWord_15973) baseStart_15973 baseEnd_15973 := by
    simpa [prefixWord, tailWord_15973, baseEnd_15973] using wordTrace_append hprefix tailTrace_15973
  have hstable : (prefixWord ++ tailWord_15973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15973).length < 2 ^ (prefixWord ++ tailWord_15973).sum := by decide
  have hdescent : baseEnd_15973 < baseStart_15973 := by decide
  rcases family_descends (prefixWord ++ tailWord_15973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15976 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_15976 : Nat := 118140960795 + 15976 * 2 ^ 59
def prefixEnd_15976 : Nat := 4983230072969 + 3 ^ 40 * 15976 * 2
def baseEnd_15976 : Nat := 3645940860593212234015

theorem tailTrace_15976 : CollatzResearch.WordTrace tailWord_15976 prefixEnd_15976 3645940860593212234015 := by
  unfold tailWord_15976
  simp only [CollatzResearch.WordTrace]
  refine ⟨291346295064577664341891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 388461726752770219122521 291346295064577664341891)
  ·
    refine ⟨437019442596866496512837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291346295064577664341891 437019442596866496512837)
    ·
      refine ⟨81941145486912468096157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437019442596866496512837 81941145486912468096157)
      ·
        refine ⟨30727929557592175536059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81941145486912468096157 30727929557592175536059)
        ·
          refine ⟨46091894336388263304089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30727929557592175536059 46091894336388263304089)
          ·
            refine ⟨34568920752291197478067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46091894336388263304089 34568920752291197478067)
            ·
              refine ⟨51853381128436796217101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34568920752291197478067 51853381128436796217101)
              ·
                refine ⟨19445017923163798581413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51853381128436796217101 19445017923163798581413)
                ·
                  refine ⟨3645940860593212234015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19445017923163798581413 3645940860593212234015)
                  ·
                    rfl

theorem cell21_15976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_15976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15976 prefixEnd_15976 := by exact prefixLift 15976
  have htrace : WordTrace (prefixWord ++ tailWord_15976) baseStart_15976 baseEnd_15976 := by
    simpa [prefixWord, tailWord_15976, baseEnd_15976] using wordTrace_append hprefix tailTrace_15976
  have hstable : (prefixWord ++ tailWord_15976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15976).length < 2 ^ (prefixWord ++ tailWord_15976).sum := by decide
  have hdescent : baseEnd_15976 < baseStart_15976 := by decide
  rcases family_descends (prefixWord ++ tailWord_15976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15990 : List Nat := [5, 1, 1, 2, 2, 1, 2, 7]
def baseStart_15990 : Nat := 118140960795 + 15990 * 2 ^ 59
def prefixEnd_15990 : Nat := 4983230072969 + 3 ^ 40 * 15990 * 2
def baseEnd_15990 : Nat := 1216378617110766333551

theorem tailTrace_15990 : CollatzResearch.WordTrace tailWord_15990 prefixEnd_15990 1216378617110766333551 := by
  unfold tailWord_15990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450200754902232480839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 388802141385623813128949 36450200754902232480839)
  ·
    refine ⟨54675301132353348721259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36450200754902232480839 54675301132353348721259)
    ·
      refine ⟨82012951698530023081889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54675301132353348721259 82012951698530023081889)
      ·
        refine ⟨61509713773897517311417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82012951698530023081889 61509713773897517311417)
        ·
          refine ⟨46132285330423137983563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61509713773897517311417 46132285330423137983563)
          ·
            refine ⟨69198427995634706975345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46132285330423137983563 69198427995634706975345)
            ·
              refine ⟨51898820996726030231509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69198427995634706975345 51898820996726030231509)
              ·
                refine ⟨1216378617110766333551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51898820996726030231509 1216378617110766333551)
                ·
                  rfl

theorem cell21_15990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_15990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_15990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_15990 prefixEnd_15990 := by exact prefixLift 15990
  have htrace : WordTrace (prefixWord ++ tailWord_15990) baseStart_15990 baseEnd_15990 := by
    simpa [prefixWord, tailWord_15990, baseEnd_15990] using wordTrace_append hprefix tailTrace_15990
  have hstable : (prefixWord ++ tailWord_15990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15990).length < 2 ^ (prefixWord ++ tailWord_15990).sum := by decide
  have hdescent : baseEnd_15990 < baseStart_15990 := by decide
  rcases family_descends (prefixWord ++ tailWord_15990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16063 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_16063 : Nat := 118140960795 + 16063 * 2 ^ 59
def prefixEnd_16063 : Nat := 4983230072969 + 3 ^ 40 * 16063 * 2
def baseEnd_16063 : Nat := 3665795445900394283837

theorem tailTrace_16063 : CollatzResearch.WordTrace tailWord_16063 prefixEnd_16063 3665795445900394283837 := by
  unfold tailWord_16063
  simp only [CollatzResearch.WordTrace]
  refine ⟨585865740813969187100843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 390577160542646124733895 585865740813969187100843)
  ·
    refine ⟨878798611220953780651265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585865740813969187100843 878798611220953780651265)
    ·
      refine ⟨659098958415715335488449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 878798611220953780651265 659098958415715335488449)
      ·
        refine ⟨494324218811786501616337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659098958415715335488449 494324218811786501616337)
        ·
          refine ⟨370743164108839876212253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494324218811786501616337 370743164108839876212253)
          ·
            refine ⟨139028686540814953579595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370743164108839876212253 139028686540814953579595)
            ·
              refine ⟨208543029811222430369393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139028686540814953579595 208543029811222430369393)
              ·
                refine ⟨156407272358416822777045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208543029811222430369393 156407272358416822777045)
                ·
                  refine ⟨3665795445900394283837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 156407272358416822777045 3665795445900394283837)
                  ·
                    rfl

theorem cell21_16063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_16063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16063 prefixEnd_16063 := by exact prefixLift 16063
  have htrace : WordTrace (prefixWord ++ tailWord_16063) baseStart_16063 baseEnd_16063 := by
    simpa [prefixWord, tailWord_16063, baseEnd_16063] using wordTrace_append hprefix tailTrace_16063
  have hstable : (prefixWord ++ tailWord_16063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16063).length < 2 ^ (prefixWord ++ tailWord_16063).sum := by decide
  have hdescent : baseEnd_16063 < baseStart_16063 := by decide
  rcases family_descends (prefixWord ++ tailWord_16063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16134 : List Nat := [6, 2, 2, 1, 1, 1, 2, 6]
def baseStart_16134 : Nat := 118140960795 + 16134 * 2 ^ 59
def prefixEnd_16134 : Nat := 4983230072969 + 3 ^ 40 * 16134 * 2
def baseEnd_16134 : Nat := 1227332871073349533453

theorem tailTrace_16134 : CollatzResearch.WordTrace tailWord_16134 prefixEnd_16134 1227332871073349533453 := by
  unfold tailWord_16134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389228861148384779233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 392303549037832208623637 18389228861148384779233)
  ·
    refine ⟨13791921645861288584425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18389228861148384779233 13791921645861288584425)
    ·
      refine ⟨10343941234395966438319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13791921645861288584425 10343941234395966438319)
      ·
        refine ⟨15515911851593949657479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343941234395966438319 15515911851593949657479)
        ·
          refine ⟨23273867777390924486219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515911851593949657479 23273867777390924486219)
          ·
            refine ⟨34910801666086386729329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23273867777390924486219 34910801666086386729329)
            ·
              refine ⟨26183101249564790046997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34910801666086386729329 26183101249564790046997)
              ·
                refine ⟨1227332871073349533453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26183101249564790046997 1227332871073349533453)
                ·
                  rfl

theorem cell21_16134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_16134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16134 prefixEnd_16134 := by exact prefixLift 16134
  have htrace : WordTrace (prefixWord ++ tailWord_16134) baseStart_16134 baseEnd_16134 := by
    simpa [prefixWord, tailWord_16134, baseEnd_16134] using wordTrace_append hprefix tailTrace_16134
  have hstable : (prefixWord ++ tailWord_16134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16134).length < 2 ^ (prefixWord ++ tailWord_16134).sum := by decide
  have hdescent : baseEnd_16134 < baseStart_16134 := by decide
  rcases family_descends (prefixWord ++ tailWord_16134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16184 : List Nat := [2, 1, 2, 1, 3, 12]
def baseStart_16184 : Nat := 118140960795 + 16184 * 2 ^ 59
def prefixEnd_16184 : Nat := 4983230072969 + 3 ^ 40 * 16184 * 2
def baseEnd_16184 : Nat := 136792936830780472849

theorem tailTrace_16184 : CollatzResearch.WordTrace tailWord_16184 prefixEnd_16184 136792936830780472849 := by
  unfold tailWord_16184
  simp only [CollatzResearch.WordTrace]
  refine ⟨295139486687803426127803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 393519315583737901503737 295139486687803426127803)
  ·
    refine ⟨442709230031705139191705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295139486687803426127803 442709230031705139191705)
    ·
      refine ⟨332031922523778854393779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442709230031705139191705 332031922523778854393779)
      ·
        refine ⟨498047883785668281590669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332031922523778854393779 498047883785668281590669)
        ·
          refine ⟨186767956419625605596501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498047883785668281590669 186767956419625605596501)
          ·
            refine ⟨136792936830780472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 186767956419625605596501 136792936830780472849)
            ·
              rfl

theorem cell21_16184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 12].length) (baseStart_16184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16184 prefixEnd_16184 := by exact prefixLift 16184
  have htrace : WordTrace (prefixWord ++ tailWord_16184) baseStart_16184 baseEnd_16184 := by
    simpa [prefixWord, tailWord_16184, baseEnd_16184] using wordTrace_append hprefix tailTrace_16184
  have hstable : (prefixWord ++ tailWord_16184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16184).length < 2 ^ (prefixWord ++ tailWord_16184).sum := by decide
  have hdescent : baseEnd_16184 < baseStart_16184 := by decide
  rcases family_descends (prefixWord ++ tailWord_16184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16190 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_16190 : Nat := 118140960795 + 16190 * 2 ^ 59
def prefixEnd_16190 : Nat := 4983230072969 + 3 ^ 40 * 16190 * 2
def baseEnd_16190 : Nat := 3694778576176395666911

theorem tailTrace_16190 : CollatzResearch.WordTrace tailWord_16190 prefixEnd_16190 3694778576176395666911 := by
  unfold tailWord_16190
  simp only [CollatzResearch.WordTrace]
  refine ⟨73812226419233734621753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 393665207569246584649349 73812226419233734621753)
  ·
    refine ⟨55359169814425300966315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73812226419233734621753 55359169814425300966315)
    ·
      refine ⟨83038754721637951449473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55359169814425300966315 83038754721637951449473)
      ·
        refine ⟨62279066041228463587105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83038754721637951449473 62279066041228463587105)
        ·
          refine ⟨46709299530921347690329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62279066041228463587105 46709299530921347690329)
          ·
            refine ⟨35031974648191010767747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46709299530921347690329 35031974648191010767747)
            ·
              refine ⟨52547961972286516151621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35031974648191010767747 52547961972286516151621)
              ·
                refine ⟨9852742869803721778429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52547961972286516151621 9852742869803721778429)
                ·
                  refine ⟨3694778576176395666911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9852742869803721778429 3694778576176395666911)
                  ·
                    rfl

theorem cell21_16190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_16190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16190 prefixEnd_16190 := by exact prefixLift 16190
  have htrace : WordTrace (prefixWord ++ tailWord_16190) baseStart_16190 baseEnd_16190 := by
    simpa [prefixWord, tailWord_16190, baseEnd_16190] using wordTrace_append hprefix tailTrace_16190
  have hstable : (prefixWord ++ tailWord_16190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16190).length < 2 ^ (prefixWord ++ tailWord_16190).sum := by decide
  have hdescent : baseEnd_16190 < baseStart_16190 := by decide
  rcases family_descends (prefixWord ++ tailWord_16190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16336 : List Nat := [2, 1, 1, 1, 1, 2, 6, 7]
def baseStart_16336 : Nat := 118140960795 + 16336 * 2 ^ 59
def prefixEnd_16336 : Nat := 4983230072969 + 3 ^ 40 * 16336 * 2
def baseEnd_16336 : Nat := 1242699255104195411093

theorem tailTrace_16336 : CollatzResearch.WordTrace tailWord_16336 prefixEnd_16336 1242699255104195411093 := by
  unfold tailWord_16336
  simp only [CollatzResearch.WordTrace]
  refine ⟨297911434412468405894431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 397215245883291207859241 297911434412468405894431)
  ·
    refine ⟨446867151618702608841647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297911434412468405894431 446867151618702608841647)
    ·
      refine ⟨670300727428053913262471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446867151618702608841647 670300727428053913262471)
      ·
        refine ⟨1005451091142080869893707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670300727428053913262471 1005451091142080869893707)
        ·
          refine ⟨1508176636713121304840561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005451091142080869893707 1508176636713121304840561)
          ·
            refine ⟨1131132477534840978630421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508176636713121304840561 1131132477534840978630421)
            ·
              refine ⟨53021834884445670873301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1131132477534840978630421 53021834884445670873301)
              ·
                refine ⟨1242699255104195411093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53021834884445670873301 1242699255104195411093)
                ·
                  rfl

theorem cell21_16336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_16336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16336 prefixEnd_16336 := by exact prefixLift 16336
  have htrace : WordTrace (prefixWord ++ tailWord_16336) baseStart_16336 baseEnd_16336 := by
    simpa [prefixWord, tailWord_16336, baseEnd_16336] using wordTrace_append hprefix tailTrace_16336
  have hstable : (prefixWord ++ tailWord_16336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16336).length < 2 ^ (prefixWord ++ tailWord_16336).sum := by decide
  have hdescent : baseEnd_16336 < baseStart_16336 := by decide
  rcases family_descends (prefixWord ++ tailWord_16336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16359 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 3]
def baseStart_16359 : Nat := 118140960795 + 16359 * 2 ^ 59
def prefixEnd_16359 : Nat := 4983230072969 + 3 ^ 40 * 16359 * 2
def baseEnd_16359 : Nat := 3733346678669657349899

theorem tailTrace_16359 : CollatzResearch.WordTrace tailWord_16359 prefixEnd_16359 3733346678669657349899 := by
  unfold tailWord_16359
  simp only [CollatzResearch.WordTrace]
  refine ⟨596661747741611739876131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 397774498494407826584087 596661747741611739876131)
  ·
    refine ⟨894992621612417609814197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596661747741611739876131 894992621612417609814197)
    ·
      refine ⟨83905558276164150920081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 894992621612417609814197 83905558276164150920081)
      ·
        refine ⟨62929168707123113190061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83905558276164150920081 62929168707123113190061)
        ·
          refine ⟨23598438265171167446273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62929168707123113190061 23598438265171167446273)
          ·
            refine ⟨17698828698878375584705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23598438265171167446273 17698828698878375584705)
            ·
              refine ⟨13274121524158781688529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17698828698878375584705 13274121524158781688529)
              ·
                refine ⟨9955591143119086266397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274121524158781688529 9955591143119086266397)
                ·
                  refine ⟨3733346678669657349899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9955591143119086266397 3733346678669657349899)
                  ·
                    rfl

theorem cell21_16359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 3].length) (baseStart_16359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16359 prefixEnd_16359 := by exact prefixLift 16359
  have htrace : WordTrace (prefixWord ++ tailWord_16359) baseStart_16359 baseEnd_16359 := by
    simpa [prefixWord, tailWord_16359, baseEnd_16359] using wordTrace_append hprefix tailTrace_16359
  have hstable : (prefixWord ++ tailWord_16359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16359).length < 2 ^ (prefixWord ++ tailWord_16359).sum := by decide
  have hdescent : baseEnd_16359 < baseStart_16359 := by decide
  rcases family_descends (prefixWord ++ tailWord_16359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16367 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_16367 : Nat := 118140960795 + 16367 * 2 ^ 59
def prefixEnd_16367 : Nat := 4983230072969 + 3 ^ 40 * 16367 * 2
def baseEnd_16367 : Nat := 3735172387663421216549

theorem tailTrace_16367 : CollatzResearch.WordTrace tailWord_16367 prefixEnd_16367 3735172387663421216549 := by
  unfold tailWord_16367
  simp only [CollatzResearch.WordTrace]
  refine ⟨596953531712629106167355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 397969021141752737444903 596953531712629106167355)
  ·
    refine ⟨895430297568943659251033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596953531712629106167355 895430297568943659251033)
    ·
      refine ⟨671572723176707744438275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895430297568943659251033 671572723176707744438275)
      ·
        refine ⟨1007359084765061616657413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671572723176707744438275 1007359084765061616657413)
        ·
          refine ⟨188879828393449053123265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1007359084765061616657413 188879828393449053123265)
          ·
            refine ⟨141659871295086789842449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188879828393449053123265 141659871295086789842449)
            ·
              refine ⟨106244903471315092381837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141659871295086789842449 106244903471315092381837)
              ·
                refine ⟨39841838801743159643189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106244903471315092381837 39841838801743159643189)
                ·
                  refine ⟨3735172387663421216549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39841838801743159643189 3735172387663421216549)
                  ·
                    rfl

theorem cell21_16367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_16367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16367 prefixEnd_16367 := by exact prefixLift 16367
  have htrace : WordTrace (prefixWord ++ tailWord_16367) baseStart_16367 baseEnd_16367 := by
    simpa [prefixWord, tailWord_16367, baseEnd_16367] using wordTrace_append hprefix tailTrace_16367
  have hstable : (prefixWord ++ tailWord_16367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16367).length < 2 ^ (prefixWord ++ tailWord_16367).sum := by decide
  have hdescent : baseEnd_16367 < baseStart_16367 := by decide
  rcases family_descends (prefixWord ++ tailWord_16367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16398 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_16398 : Nat := 118140960795 + 16398 * 2 ^ 59
def prefixEnd_16398 : Nat := 4983230072969 + 3 ^ 40 * 16398 * 2
def baseEnd_16398 : Nat := 3742247010014256199819

theorem tailTrace_16398 : CollatzResearch.WordTrace tailWord_16398 prefixEnd_16398 3742247010014256199819 := by
  unfold tailWord_16398
  simp only [CollatzResearch.WordTrace]
  refine ⟨74760524325040175068231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 398722796400214267030565 74760524325040175068231)
  ·
    refine ⟨112140786487560262602347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74760524325040175068231 112140786487560262602347)
    ·
      refine ⟨168211179731340393903521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112140786487560262602347 168211179731340393903521)
      ·
        refine ⟨126158384798505295427641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168211179731340393903521 126158384798505295427641)
        ·
          refine ⟨94618788598878971570731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126158384798505295427641 94618788598878971570731)
          ·
            refine ⟨141928182898318457356097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94618788598878971570731 141928182898318457356097)
            ·
              refine ⟨106446137173738843017073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141928182898318457356097 106446137173738843017073)
              ·
                refine ⟨79834602880304132262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106446137173738843017073 79834602880304132262805)
                ·
                  refine ⟨3742247010014256199819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79834602880304132262805 3742247010014256199819)
                  ·
                    rfl

theorem cell21_16398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_16398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16398 prefixEnd_16398 := by exact prefixLift 16398
  have htrace : WordTrace (prefixWord ++ tailWord_16398) baseStart_16398 baseEnd_16398 := by
    simpa [prefixWord, tailWord_16398, baseEnd_16398] using wordTrace_append hprefix tailTrace_16398
  have hstable : (prefixWord ++ tailWord_16398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16398).length < 2 ^ (prefixWord ++ tailWord_16398).sum := by decide
  have hdescent : baseEnd_16398 < baseStart_16398 := by decide
  rcases family_descends (prefixWord ++ tailWord_16398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16446 : List Nat := [4, 2, 1, 3, 2, 1, 1, 7]
def baseStart_16446 : Nat := 118140960795 + 16446 * 2 ^ 59
def prefixEnd_16446 : Nat := 4983230072969 + 3 ^ 40 * 16446 * 2
def baseEnd_16446 : Nat := 1251067087992279799907

theorem tailTrace_16446 : CollatzResearch.WordTrace tailWord_16446 prefixEnd_16446 1251067087992279799907 := by
  unfold tailWord_16446
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979362303303199786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 399889932284283732195461 74979362303303199786649)
  ·
    refine ⟨56234521727477399839987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74979362303303199786649 56234521727477399839987)
    ·
      refine ⟨84351782591216099759981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56234521727477399839987 84351782591216099759981)
      ·
        refine ⟨31631918471706037409993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84351782591216099759981 31631918471706037409993)
        ·
          refine ⟨23723938853779528057495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31631918471706037409993 23723938853779528057495)
          ·
            refine ⟨35585908280669292086243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23723938853779528057495 35585908280669292086243)
            ·
              refine ⟨53378862421003938129365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35585908280669292086243 53378862421003938129365)
              ·
                refine ⟨1251067087992279799907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53378862421003938129365 1251067087992279799907)
                ·
                  rfl

theorem cell21_16446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_16446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16446 prefixEnd_16446 := by exact prefixLift 16446
  have htrace : WordTrace (prefixWord ++ tailWord_16446) baseStart_16446 baseEnd_16446 := by
    simpa [prefixWord, tailWord_16446, baseEnd_16446] using wordTrace_append hprefix tailTrace_16446
  have hstable : (prefixWord ++ tailWord_16446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16446).length < 2 ^ (prefixWord ++ tailWord_16446).sum := by decide
  have hdescent : baseEnd_16446 < baseStart_16446 := by decide
  rcases family_descends (prefixWord ++ tailWord_16446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16457 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_16457 : Nat := 118140960795 + 16457 * 2 ^ 59
def prefixEnd_16457 : Nat := 4983230072969 + 3 ^ 40 * 16457 * 2
def baseEnd_16457 : Nat := 3755711613843264716365

theorem tailTrace_16457 : CollatzResearch.WordTrace tailWord_16457 prefixEnd_16457 3755711613843264716365 := by
  unfold tailWord_16457
  simp only [CollatzResearch.WordTrace]
  refine ⟨600236101386574476943625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 400157400924382984629083 600236101386574476943625)
  ·
    refine ⟨450177076039930857707719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 600236101386574476943625 450177076039930857707719)
    ·
      refine ⟨675265614059896286561579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450177076039930857707719 675265614059896286561579)
      ·
        refine ⟨1012898421089844429842369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675265614059896286561579 1012898421089844429842369)
        ·
          refine ⟨759673815817383322381777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012898421089844429842369 759673815817383322381777)
          ·
            refine ⟨569755361863037491786333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759673815817383322381777 569755361863037491786333)
            ·
              refine ⟨213658260698639059419875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569755361863037491786333 213658260698639059419875)
              ·
                refine ⟨320487391047958589129813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213658260698639059419875 320487391047958589129813)
                ·
                  refine ⟨3755711613843264716365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 320487391047958589129813 3755711613843264716365)
                  ·
                    rfl

theorem cell21_16457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_16457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16457 prefixEnd_16457 := by exact prefixLift 16457
  have htrace : WordTrace (prefixWord ++ tailWord_16457) baseStart_16457 baseEnd_16457 := by
    simpa [prefixWord, tailWord_16457, baseEnd_16457] using wordTrace_append hprefix tailTrace_16457
  have hstable : (prefixWord ++ tailWord_16457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16457).length < 2 ^ (prefixWord ++ tailWord_16457).sum := by decide
  have hdescent : baseEnd_16457 < baseStart_16457 := by decide
  rcases family_descends (prefixWord ++ tailWord_16457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16474 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_16474 : Nat := 118140960795 + 16474 * 2 ^ 59
def prefixEnd_16474 : Nat := 4983230072969 + 3 ^ 40 * 16474 * 2
def baseEnd_16474 : Nat := 3759591245455012932997

theorem tailTrace_16474 : CollatzResearch.WordTrace tailWord_16474 prefixEnd_16474 3759591245455012932997 := by
  unfold tailWord_16474
  simp only [CollatzResearch.WordTrace]
  refine ⟨150214035581246595078119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 400570761549990920208317 150214035581246595078119)
  ·
    refine ⟨225321053371869892617179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150214035581246595078119 225321053371869892617179)
    ·
      refine ⟨337981580057804838925769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225321053371869892617179 337981580057804838925769)
      ·
        refine ⟨253486185043353629194327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337981580057804838925769 253486185043353629194327)
        ·
          refine ⟨380229277565030443791491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253486185043353629194327 380229277565030443791491)
          ·
            refine ⟨570343916347545665687237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380229277565030443791491 570343916347545665687237)
            ·
              refine ⟨106939484315164812316357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570343916347545665687237 106939484315164812316357)
              ·
                refine ⟨20051153309093402309317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106939484315164812316357 20051153309093402309317)
                ·
                  refine ⟨3759591245455012932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20051153309093402309317 3759591245455012932997)
                  ·
                    rfl

theorem cell21_16474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_16474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16474 prefixEnd_16474 := by exact prefixLift 16474
  have htrace : WordTrace (prefixWord ++ tailWord_16474) baseStart_16474 baseEnd_16474 := by
    simpa [prefixWord, tailWord_16474, baseEnd_16474] using wordTrace_append hprefix tailTrace_16474
  have hstable : (prefixWord ++ tailWord_16474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16474).length < 2 ^ (prefixWord ++ tailWord_16474).sum := by decide
  have hdescent : baseEnd_16474 < baseStart_16474 := by decide
  rcases family_descends (prefixWord ++ tailWord_16474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16477 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_16477 : Nat := 118140960795 + 16477 * 2 ^ 59
def prefixEnd_16477 : Nat := 4983230072969 + 3 ^ 40 * 16477 * 2
def baseEnd_16477 : Nat := 3760275886327674382991

theorem tailTrace_16477 : CollatzResearch.WordTrace tailWord_16477 prefixEnd_16477 3760275886327674382991 := by
  unfold tailWord_16477
  simp only [CollatzResearch.WordTrace]
  refine ⟨600965561314117892671685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 400643707542745261781123 600965561314117892671685)
  ·
    refine ⟨112681042746397104875941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 600965561314117892671685 112681042746397104875941)
    ·
      refine ⟨21127695514949457164239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112681042746397104875941 21127695514949457164239)
      ·
        refine ⟨31691543272424185746359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21127695514949457164239 31691543272424185746359)
        ·
          refine ⟨47537314908636278619539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31691543272424185746359 47537314908636278619539)
          ·
            refine ⟨71305972362954417929309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47537314908636278619539 71305972362954417929309)
            ·
              refine ⟨26739739636107906723491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71305972362954417929309 26739739636107906723491)
              ·
                refine ⟨40109609454161860085237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26739739636107906723491 40109609454161860085237)
                ·
                  refine ⟨3760275886327674382991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40109609454161860085237 3760275886327674382991)
                  ·
                    rfl

theorem cell21_16477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_16477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16477 prefixEnd_16477 := by exact prefixLift 16477
  have htrace : WordTrace (prefixWord ++ tailWord_16477) baseStart_16477 baseEnd_16477 := by
    simpa [prefixWord, tailWord_16477, baseEnd_16477] using wordTrace_append hprefix tailTrace_16477
  have hstable : (prefixWord ++ tailWord_16477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16477).length < 2 ^ (prefixWord ++ tailWord_16477).sum := by decide
  have hdescent : baseEnd_16477 < baseStart_16477 := by decide
  rcases family_descends (prefixWord ++ tailWord_16477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16626 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_16626 : Nat := 118140960795 + 16626 * 2 ^ 59
def prefixEnd_16626 : Nat := 4983230072969 + 3 ^ 40 * 16626 * 2
def baseEnd_16626 : Nat := 3794279716336526399353

theorem tailTrace_16626 : CollatzResearch.WordTrace tailWord_16626 prefixEnd_16626 3794279716336526399353 := by
  unfold tailWord_16626
  simp only [CollatzResearch.WordTrace]
  refine ⟨151600009443579084961433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 404266691849544226563821 151600009443579084961433)
  ·
    refine ⟨113700007082684313721075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151600009443579084961433 113700007082684313721075)
    ·
      refine ⟨170550010624026470581613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113700007082684313721075 170550010624026470581613)
      ·
        refine ⟨63956253984009926468105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170550010624026470581613 63956253984009926468105)
        ·
          refine ⟨47967190488007444851079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63956253984009926468105 47967190488007444851079)
          ·
            refine ⟨71950785732011167276619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47967190488007444851079 71950785732011167276619)
            ·
              refine ⟨107926178598016750914929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71950785732011167276619 107926178598016750914929)
              ·
                refine ⟨80944633948512563186197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107926178598016750914929 80944633948512563186197)
                ·
                  refine ⟨3794279716336526399353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80944633948512563186197 3794279716336526399353)
                  ·
                    rfl

theorem cell21_16626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_16626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16626 prefixEnd_16626 := by exact prefixLift 16626
  have htrace : WordTrace (prefixWord ++ tailWord_16626) baseStart_16626 baseEnd_16626 := by
    simpa [prefixWord, tailWord_16626, baseEnd_16626] using wordTrace_append hprefix tailTrace_16626
  have hstable : (prefixWord ++ tailWord_16626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16626).length < 2 ^ (prefixWord ++ tailWord_16626).sum := by decide
  have hdescent : baseEnd_16626 < baseStart_16626 := by decide
  rcases family_descends (prefixWord ++ tailWord_16626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16798 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_16798 : Nat := 118140960795 + 16798 * 2 ^ 59
def prefixEnd_16798 : Nat := 4983230072969 + 3 ^ 40 * 16798 * 2
def baseEnd_16798 : Nat := 3833532459702449532335

theorem tailTrace_16798 : CollatzResearch.WordTrace tailWord_16798 prefixEnd_16798 3833532459702449532335 := by
  unfold tailWord_16798
  simp only [CollatzResearch.WordTrace]
  refine ⟨76584174143898714388381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 408448928767459810071365 76584174143898714388381)
  ·
    refine ⟨28719065303962017895643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76584174143898714388381 28719065303962017895643)
    ·
      refine ⟨43078597955943026843465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28719065303962017895643 43078597955943026843465)
      ·
        refine ⟨32308948466957270132599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43078597955943026843465 32308948466957270132599)
        ·
          refine ⟨48463422700435905198899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32308948466957270132599 48463422700435905198899)
          ·
            refine ⟨72695134050653857798349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48463422700435905198899 72695134050653857798349)
            ·
              refine ⟨27260675268995196674381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72695134050653857798349 27260675268995196674381)
              ·
                refine ⟨10222753225873198752893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27260675268995196674381 10222753225873198752893)
                ·
                  refine ⟨3833532459702449532335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10222753225873198752893 3833532459702449532335)
                  ·
                    rfl

theorem cell21_16798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_16798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16798 prefixEnd_16798 := by exact prefixLift 16798
  have htrace : WordTrace (prefixWord ++ tailWord_16798) baseStart_16798 baseEnd_16798 := by
    simpa [prefixWord, tailWord_16798, baseEnd_16798] using wordTrace_append hprefix tailTrace_16798
  have hstable : (prefixWord ++ tailWord_16798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16798).length < 2 ^ (prefixWord ++ tailWord_16798).sum := by decide
  have hdescent : baseEnd_16798 < baseStart_16798 := by decide
  rcases family_descends (prefixWord ++ tailWord_16798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16823 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_16823 : Nat := 118140960795 + 16823 * 2 ^ 59
def prefixEnd_16823 : Nat := 4983230072969 + 3 ^ 40 * 16823 * 2
def baseEnd_16823 : Nat := 3839237800307961615617

theorem tailTrace_16823 : CollatzResearch.WordTrace tailWord_16823 prefixEnd_16823 3839237800307961615617 := by
  unfold tailWord_16823
  simp only [CollatzResearch.WordTrace]
  refine ⟨613585218060618984767123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 409056812040412656511415 613585218060618984767123)
  ·
    refine ⟨920377827090928477150685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613585218060618984767123 920377827090928477150685)
    ·
      refine ⟨345141685159098178931507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 920377827090928477150685 345141685159098178931507)
      ·
        refine ⟨517712527738647268397261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345141685159098178931507 517712527738647268397261)
        ·
          refine ⟨194142197901992725648973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517712527738647268397261 194142197901992725648973)
          ·
            refine ⟨72803324213247272118365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194142197901992725648973 72803324213247272118365)
            ·
              refine ⟨27301246579967727044387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72803324213247272118365 27301246579967727044387)
              ·
                refine ⟨40951869869951590566581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27301246579967727044387 40951869869951590566581)
                ·
                  refine ⟨3839237800307961615617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40951869869951590566581 3839237800307961615617)
                  ·
                    rfl

theorem cell21_16823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_16823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16823 prefixEnd_16823 := by exact prefixLift 16823
  have htrace : WordTrace (prefixWord ++ tailWord_16823) baseStart_16823 baseEnd_16823 := by
    simpa [prefixWord, tailWord_16823, baseEnd_16823] using wordTrace_append hprefix tailTrace_16823
  have hstable : (prefixWord ++ tailWord_16823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16823).length < 2 ^ (prefixWord ++ tailWord_16823).sum := by decide
  have hdescent : baseEnd_16823 < baseStart_16823 := by decide
  rcases family_descends (prefixWord ++ tailWord_16823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16874 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_16874 : Nat := 118140960795 + 16874 * 2 ^ 59
def prefixEnd_16874 : Nat := 4983230072969 + 3 ^ 40 * 16874 * 2
def baseEnd_16874 : Nat := 3850876695143206265513

theorem tailTrace_16874 : CollatzResearch.WordTrace tailWord_16874 prefixEnd_16874 3850876695143206265513 := by
  unfold tailWord_16874
  simp only [CollatzResearch.WordTrace]
  refine ⟨153861335218963673718419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 410296893917236463249117 153861335218963673718419)
  ·
    refine ⟨230792002828445510577629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153861335218963673718419 230792002828445510577629)
    ·
      refine ⟨86547001060667066466611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230792002828445510577629 86547001060667066466611)
      ·
        refine ⟨129820501591000599699917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86547001060667066466611 129820501591000599699917)
        ·
          refine ⟨48682688096625224887469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129820501591000599699917 48682688096625224887469)
          ·
            refine ⟨18256008036234459332801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48682688096625224887469 18256008036234459332801)
            ·
              refine ⟨13692006027175844499601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18256008036234459332801 13692006027175844499601)
              ·
                refine ⟨10269004520381883374701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13692006027175844499601 10269004520381883374701)
                ·
                  refine ⟨3850876695143206265513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10269004520381883374701 3850876695143206265513)
                  ·
                    rfl

theorem cell21_16874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_16874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16874 prefixEnd_16874 := by exact prefixLift 16874
  have htrace : WordTrace (prefixWord ++ tailWord_16874) baseStart_16874 baseEnd_16874 := by
    simpa [prefixWord, tailWord_16874, baseEnd_16874] using wordTrace_append hprefix tailTrace_16874
  have hstable : (prefixWord ++ tailWord_16874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16874).length < 2 ^ (prefixWord ++ tailWord_16874).sum := by decide
  have hdescent : baseEnd_16874 < baseStart_16874 := by decide
  rcases family_descends (prefixWord ++ tailWord_16874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16961 : List Nat := [1, 2, 5, 1, 1, 2, 4, 5]
def baseStart_16961 : Nat := 118140960795 + 16961 * 2 ^ 59
def prefixEnd_16961 : Nat := 4983230072969 + 3 ^ 40 * 16961 * 2
def baseEnd_16961 : Nat := 1290243760150129438445

theorem tailTrace_16961 : CollatzResearch.WordTrace tailWord_16961 prefixEnd_16961 1290243760150129438445 := by
  unfold tailWord_16961
  simp only [CollatzResearch.WordTrace]
  refine ⟨618618491560668553290737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 412412327707112368860491 618618491560668553290737)
  ·
    refine ⟨463963868670501414968053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618618491560668553290737 463963868670501414968053)
    ·
      refine ⟨43496612687859507653255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 463963868670501414968053 43496612687859507653255)
      ·
        refine ⟨65244919031789261479883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43496612687859507653255 65244919031789261479883)
        ·
          refine ⟨97867378547683892219825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65244919031789261479883 97867378547683892219825)
          ·
            refine ⟨73400533910762919164869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97867378547683892219825 73400533910762919164869)
            ·
              refine ⟨13762600108268047343413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73400533910762919164869 13762600108268047343413)
              ·
                refine ⟨1290243760150129438445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13762600108268047343413 1290243760150129438445)
                ·
                  rfl

theorem cell21_16961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].length) (baseStart_16961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_16961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_16961 prefixEnd_16961 := by exact prefixLift 16961
  have htrace : WordTrace (prefixWord ++ tailWord_16961) baseStart_16961 baseEnd_16961 := by
    simpa [prefixWord, tailWord_16961, baseEnd_16961] using wordTrace_append hprefix tailTrace_16961
  have hstable : (prefixWord ++ tailWord_16961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16961).length < 2 ^ (prefixWord ++ tailWord_16961).sum := by decide
  have hdescent : baseEnd_16961 < baseStart_16961 := by decide
  rcases family_descends (prefixWord ++ tailWord_16961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17116 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_17116 : Nat := 118140960795 + 17116 * 2 ^ 59
def prefixEnd_17116 : Nat := 4983230072969 + 3 ^ 40 * 17116 * 2
def baseEnd_17116 : Nat := 3906104392204563231685

theorem tailTrace_17116 : CollatzResearch.WordTrace tailWord_17116 prefixEnd_17116 3906104392204563231685 := by
  unfold tailWord_17116
  simp only [CollatzResearch.WordTrace]
  refine ⟨312135902999565012591601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 416181203999420016788801 312135902999565012591601)
  ·
    refine ⟨234101927249673759443701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 312135902999565012591601 234101927249673759443701)
    ·
      refine ⟨21947055679656914947847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 234101927249673759443701 21947055679656914947847)
      ·
        refine ⟨32920583519485372421771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21947055679656914947847 32920583519485372421771)
        ·
          refine ⟨49380875279228058632657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32920583519485372421771 49380875279228058632657)
          ·
            refine ⟨37035656459421043974493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49380875279228058632657 37035656459421043974493)
            ·
              refine ⟨13888371172282891490435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37035656459421043974493 13888371172282891490435)
              ·
                refine ⟨20832556758424337235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13888371172282891490435 20832556758424337235653)
                ·
                  refine ⟨3906104392204563231685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20832556758424337235653 3906104392204563231685)
                  ·
                    rfl

theorem cell21_17116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_17116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17116 prefixEnd_17116 := by exact prefixLift 17116
  have htrace : WordTrace (prefixWord ++ tailWord_17116) baseStart_17116 baseEnd_17116 := by
    simpa [prefixWord, tailWord_17116, baseEnd_17116] using wordTrace_append hprefix tailTrace_17116
  have hstable : (prefixWord ++ tailWord_17116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17116).length < 2 ^ (prefixWord ++ tailWord_17116).sum := by decide
  have hdescent : baseEnd_17116 < baseStart_17116 := by decide
  rcases family_descends (prefixWord ++ tailWord_17116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17200 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_17200 : Nat := 118140960795 + 17200 * 2 ^ 59
def prefixEnd_17200 : Nat := 4983230072969 + 3 ^ 40 * 17200 * 2
def baseEnd_17200 : Nat := 3925274336639083831513

theorem tailTrace_17200 : CollatzResearch.WordTrace tailWord_17200 prefixEnd_17200 3925274336639083831513 := by
  unfold tailWord_17200
  simp only [CollatzResearch.WordTrace]
  refine ⟨313667768847406185620527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 418223691796541580827369 313667768847406185620527)
  ·
    refine ⟨470501653271109278430791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 313667768847406185620527 470501653271109278430791)
    ·
      refine ⟨705752479906663917646187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470501653271109278430791 705752479906663917646187)
      ·
        refine ⟨1058628719859995876469281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705752479906663917646187 1058628719859995876469281)
        ·
          refine ⟨793971539894996907351961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058628719859995876469281 793971539894996907351961)
          ·
            refine ⟨595478654921247680513971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793971539894996907351961 595478654921247680513971)
            ·
              refine ⟨893217982381871520770957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595478654921247680513971 893217982381871520770957)
              ·
                refine ⟨334956743393201820289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893217982381871520770957 334956743393201820289109)
                ·
                  refine ⟨3925274336639083831513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 334956743393201820289109 3925274336639083831513)
                  ·
                    rfl

theorem cell21_17200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_17200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17200 prefixEnd_17200 := by exact prefixLift 17200
  have htrace : WordTrace (prefixWord ++ tailWord_17200) baseStart_17200 baseEnd_17200 := by
    simpa [prefixWord, tailWord_17200, baseEnd_17200] using wordTrace_append hprefix tailTrace_17200
  have hstable : (prefixWord ++ tailWord_17200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17200).length < 2 ^ (prefixWord ++ tailWord_17200).sum := by decide
  have hdescent : baseEnd_17200 < baseStart_17200 := by decide
  rcases family_descends (prefixWord ++ tailWord_17200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17248 : List Nat := [2, 1, 1, 3, 3, 1, 5, 5]
def baseStart_17248 : Nat := 118140960795 + 17248 * 2 ^ 59
def prefixEnd_17248 : Nat := 4983230072969 + 3 ^ 40 * 17248 * 2
def baseEnd_17248 : Nat := 1312076196867222343805

theorem tailTrace_17248 : CollatzResearch.WordTrace tailWord_17248 prefixEnd_17248 1312076196867222343805 := by
  unfold tailWord_17248
  simp only [CollatzResearch.WordTrace]
  refine ⟨314543120760458284494199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 419390827680611045992265 314543120760458284494199)
  ·
    refine ⟨471814681140687426741299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 314543120760458284494199 471814681140687426741299)
    ·
      refine ⟨707722021711031140111949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471814681140687426741299 707722021711031140111949)
      ·
        refine ⟨265395758141636677541981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 707722021711031140111949 265395758141636677541981)
        ·
          refine ⟨99523409303113754078243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265395758141636677541981 99523409303113754078243)
          ·
            refine ⟨149285113954670631117365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99523409303113754078243 149285113954670631117365)
            ·
              refine ⟨13995479433250371667253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149285113954670631117365 13995479433250371667253)
              ·
                refine ⟨1312076196867222343805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13995479433250371667253 1312076196867222343805)
                ·
                  rfl

theorem cell21_17248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_17248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17248 prefixEnd_17248 := by exact prefixLift 17248
  have htrace : WordTrace (prefixWord ++ tailWord_17248) baseStart_17248 baseEnd_17248 := by
    simpa [prefixWord, tailWord_17248, baseEnd_17248] using wordTrace_append hprefix tailTrace_17248
  have hstable : (prefixWord ++ tailWord_17248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17248).length < 2 ^ (prefixWord ++ tailWord_17248).sum := by decide
  have hdescent : baseEnd_17248 < baseStart_17248 := by decide
  rcases family_descends (prefixWord ++ tailWord_17248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17279 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 3]
def baseStart_17279 : Nat := 118140960795 + 17279 * 2 ^ 59
def prefixEnd_17279 : Nat := 4983230072969 + 3 ^ 40 * 17279 * 2
def baseEnd_17279 : Nat := 3943303212952502014685

theorem tailTrace_17279 : CollatzResearch.WordTrace tailWord_17279 prefixEnd_17279 3943303212952502014685 := by
  unfold tailWord_17279
  simp only [CollatzResearch.WordTrace]
  refine ⟨630216904408608863366891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 420144602939072575577927 630216904408608863366891)
  ·
    refine ⟨945325356612913295050337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630216904408608863366891 945325356612913295050337)
    ·
      refine ⟨708994017459684971287753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945325356612913295050337 708994017459684971287753)
      ·
        refine ⟨531745513094763728465815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708994017459684971287753 531745513094763728465815)
        ·
          refine ⟨797618269642145592698723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531745513094763728465815 797618269642145592698723)
          ·
            refine ⟨1196427404463218389048085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797618269642145592698723 1196427404463218389048085)
            ·
              refine ⟨56082534584213361986629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1196427404463218389048085 56082534584213361986629)
              ·
                refine ⟨10515475234540005372493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56082534584213361986629 10515475234540005372493)
                ·
                  refine ⟨3943303212952502014685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10515475234540005372493 3943303212952502014685)
                  ·
                    rfl

theorem cell21_17279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].length) (baseStart_17279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17279 prefixEnd_17279 := by exact prefixLift 17279
  have htrace : WordTrace (prefixWord ++ tailWord_17279) baseStart_17279 baseEnd_17279 := by
    simpa [prefixWord, tailWord_17279, baseEnd_17279] using wordTrace_append hprefix tailTrace_17279
  have hstable : (prefixWord ++ tailWord_17279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17279).length < 2 ^ (prefixWord ++ tailWord_17279).sum := by decide
  have hdescent : baseEnd_17279 < baseStart_17279 := by decide
  rcases family_descends (prefixWord ++ tailWord_17279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17313 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 3]
def baseStart_17313 : Nat := 118140960795 + 17313 * 2 ^ 59
def prefixEnd_17313 : Nat := 4983230072969 + 3 ^ 40 * 17313 * 2
def baseEnd_17313 : Nat := 3951062476175998447949

theorem tailTrace_17313 : CollatzResearch.WordTrace tailWord_17313 prefixEnd_17313 3951062476175998447949 := by
  unfold tailWord_17313
  simp only [CollatzResearch.WordTrace]
  refine ⟨631456986285432670104593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 420971324190288446736395 631456986285432670104593)
  ·
    refine ⟨473592739714074502578445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 631456986285432670104593 473592739714074502578445)
    ·
      refine ⟨177597277392777938466917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 473592739714074502578445 177597277392777938466917)
      ·
        refine ⟨33299489511145863462547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177597277392777938466917 33299489511145863462547)
        ·
          refine ⟨49949234266718795193821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299489511145863462547 49949234266718795193821)
          ·
            refine ⟨18730962850019548197683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49949234266718795193821 18730962850019548197683)
            ·
              refine ⟨28096444275029322296525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18730962850019548197683 28096444275029322296525)
              ·
                refine ⟨10536166603135995861197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28096444275029322296525 10536166603135995861197)
                ·
                  refine ⟨3951062476175998447949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10536166603135995861197 3951062476175998447949)
                  ·
                    rfl

theorem cell21_17313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_17313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17313 prefixEnd_17313 := by exact prefixLift 17313
  have htrace : WordTrace (prefixWord ++ tailWord_17313) baseStart_17313 baseEnd_17313 := by
    simpa [prefixWord, tailWord_17313, baseEnd_17313] using wordTrace_append hprefix tailTrace_17313
  have hstable : (prefixWord ++ tailWord_17313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17313).length < 2 ^ (prefixWord ++ tailWord_17313).sum := by decide
  have hdescent : baseEnd_17313 < baseStart_17313 := by decide
  rcases family_descends (prefixWord ++ tailWord_17313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17383 : List Nat := [1, 1, 5, 2, 2, 10]
def baseStart_17383 : Nat := 118140960795 + 17383 * 2 ^ 59
def prefixEnd_17383 : Nat := 4983230072969 + 3 ^ 40 * 17383 * 2
def baseEnd_17383 : Nat := 146927312217460454857

theorem tailTrace_17383 : CollatzResearch.WordTrace tailWord_17383 prefixEnd_17383 146927312217460454857 := by
  unfold tailWord_17383
  simp only [CollatzResearch.WordTrace]
  refine ⟨634010096031834625152803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 422673397354556416768535 634010096031834625152803)
  ·
    refine ⟨951015144047751937729205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634010096031834625152803 951015144047751937729205)
    ·
      refine ⟨89157669754476744162113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 951015144047751937729205 89157669754476744162113)
      ·
        refine ⟨66868252315857558121585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89157669754476744162113 66868252315857558121585)
        ·
          refine ⟨50151189236893168591189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66868252315857558121585 50151189236893168591189)
          ·
            refine ⟨146927312217460454857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 50151189236893168591189 146927312217460454857)
            ·
              rfl

theorem cell21_17383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 10].length) (baseStart_17383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17383 prefixEnd_17383 := by exact prefixLift 17383
  have htrace : WordTrace (prefixWord ++ tailWord_17383) baseStart_17383 baseEnd_17383 := by
    simpa [prefixWord, tailWord_17383, baseEnd_17383] using wordTrace_append hprefix tailTrace_17383
  have hstable : (prefixWord ++ tailWord_17383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17383).length < 2 ^ (prefixWord ++ tailWord_17383).sum := by decide
  have hdescent : baseEnd_17383 < baseStart_17383 := by decide
  rcases family_descends (prefixWord ++ tailWord_17383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17386 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_17386 : Nat := 118140960795 + 17386 * 2 ^ 59
def prefixEnd_17386 : Nat := 4983230072969 + 3 ^ 40 * 17386 * 2
def baseEnd_17386 : Nat := 3967722070744093731133

theorem tailTrace_17386 : CollatzResearch.WordTrace tailWord_17386 prefixEnd_17386 3967722070744093731133 := by
  unfold tailWord_17386
  simp only [CollatzResearch.WordTrace]
  refine ⟨158529878755241534378003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 422746343347310758341341 158529878755241534378003)
  ·
    refine ⟨237794818132862301567005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158529878755241534378003 237794818132862301567005)
    ·
      refine ⟨89173056799823363087627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237794818132862301567005 89173056799823363087627)
      ·
        refine ⟨133759585199735044631441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89173056799823363087627 133759585199735044631441)
        ·
          refine ⟨100319688899801283473581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133759585199735044631441 100319688899801283473581)
          ·
            refine ⟨37619883337425481302593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100319688899801283473581 37619883337425481302593)
            ·
              refine ⟨28214912503069110976945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37619883337425481302593 28214912503069110976945)
              ·
                refine ⟨21161184377301833232709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28214912503069110976945 21161184377301833232709)
                ·
                  refine ⟨3967722070744093731133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21161184377301833232709 3967722070744093731133)
                  ·
                    rfl

theorem cell21_17386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_17386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17386 prefixEnd_17386 := by exact prefixLift 17386
  have htrace : WordTrace (prefixWord ++ tailWord_17386) baseStart_17386 baseEnd_17386 := by
    simpa [prefixWord, tailWord_17386, baseEnd_17386] using wordTrace_append hprefix tailTrace_17386
  have hstable : (prefixWord ++ tailWord_17386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17386).length < 2 ^ (prefixWord ++ tailWord_17386).sum := by decide
  have hdescent : baseEnd_17386 < baseStart_17386 := by decide
  rcases family_descends (prefixWord ++ tailWord_17386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17504 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_17504 : Nat := 118140960795 + 17504 * 2 ^ 59
def prefixEnd_17504 : Nat := 4983230072969 + 3 ^ 40 * 17504 * 2
def baseEnd_17504 : Nat := 3994651278402110764225

theorem tailTrace_17504 : CollatzResearch.WordTrace tailWord_17504 prefixEnd_17504 3994651278402110764225 := by
  unfold tailWord_17504
  simp only [CollatzResearch.WordTrace]
  refine ⟨319211664296736145153783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 425615552395648193538377 319211664296736145153783)
  ·
    refine ⟨478817496445104217730675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319211664296736145153783 478817496445104217730675)
    ·
      refine ⟨718226244667656326596013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478817496445104217730675 718226244667656326596013)
      ·
        refine ⟨269334841750371122473505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 718226244667656326596013 269334841750371122473505)
        ·
          refine ⟨202001131312778341855129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269334841750371122473505 202001131312778341855129)
          ·
            refine ⟨151500848484583756391347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202001131312778341855129 151500848484583756391347)
            ·
              refine ⟨227251272726875634587021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151500848484583756391347 227251272726875634587021)
              ·
                refine ⟨85219227272578362970133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227251272726875634587021 85219227272578362970133)
                ·
                  refine ⟨3994651278402110764225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85219227272578362970133 3994651278402110764225)
                  ·
                    rfl

theorem cell21_17504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_17504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17504 prefixEnd_17504 := by exact prefixLift 17504
  have htrace : WordTrace (prefixWord ++ tailWord_17504) baseStart_17504 baseEnd_17504 := by
    simpa [prefixWord, tailWord_17504, baseEnd_17504] using wordTrace_append hprefix tailTrace_17504
  have hstable : (prefixWord ++ tailWord_17504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17504).length < 2 ^ (prefixWord ++ tailWord_17504).sum := by decide
  have hdescent : baseEnd_17504 < baseStart_17504 := by decide
  rcases family_descends (prefixWord ++ tailWord_17504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17600 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_17600 : Nat := 118140960795 + 17600 * 2 ^ 59
def prefixEnd_17600 : Nat := 4983230072969 + 3 ^ 40 * 17600 * 2
def baseEnd_17600 : Nat := 4016559786327277164029

theorem tailTrace_17600 : CollatzResearch.WordTrace tailWord_17600 prefixEnd_17600 4016559786327277164029 := by
  unfold tailWord_17600
  simp only [CollatzResearch.WordTrace]
  refine ⟨320962368122840342901127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 427949824163787123868169 320962368122840342901127)
  ·
    refine ⟨481443552184260514351691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320962368122840342901127 481443552184260514351691)
    ·
      refine ⟨722165328276390771527537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481443552184260514351691 722165328276390771527537)
      ·
        refine ⟨541623996207293078645653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722165328276390771527537 541623996207293078645653)
        ·
          refine ⟨25388624822216863061515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 541623996207293078645653 25388624822216863061515)
          ·
            refine ⟨38082937233325294592273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25388624822216863061515 38082937233325294592273)
            ·
              refine ⟨28562202924993970944205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38082937233325294592273 28562202924993970944205)
              ·
                refine ⟨10710826096872739104077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28562202924993970944205 10710826096872739104077)
                ·
                  refine ⟨4016559786327277164029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10710826096872739104077 4016559786327277164029)
                  ·
                    rfl

theorem cell21_17600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_17600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17600 prefixEnd_17600 := by exact prefixLift 17600
  have htrace : WordTrace (prefixWord ++ tailWord_17600) baseStart_17600 baseEnd_17600 := by
    simpa [prefixWord, tailWord_17600, baseEnd_17600] using wordTrace_append hprefix tailTrace_17600
  have hstable : (prefixWord ++ tailWord_17600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17600).length < 2 ^ (prefixWord ++ tailWord_17600).sum := by decide
  have hdescent : baseEnd_17600 < baseStart_17600 := by decide
  rcases family_descends (prefixWord ++ tailWord_17600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17606 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_17606 : Nat := 118140960795 + 17606 * 2 ^ 59
def prefixEnd_17606 : Nat := 4983230072969 + 3 ^ 40 * 17606 * 2
def baseEnd_17606 : Nat := 4017929068072600064017

theorem tailTrace_17606 : CollatzResearch.WordTrace tailWord_17606 prefixEnd_17606 4017929068072600064017 := by
  unfold tailWord_17606
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066986694498240953771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 428095716149295807013781 20066986694498240953771)
  ·
    refine ⟨30100480041747361430657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066986694498240953771 30100480041747361430657)
    ·
      refine ⟨22575360031310521072993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30100480041747361430657 22575360031310521072993)
      ·
        refine ⟨16931520023482890804745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22575360031310521072993 16931520023482890804745)
        ·
          refine ⟨12698640017612168103559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16931520023482890804745 12698640017612168103559)
          ·
            refine ⟨19047960026418252155339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12698640017612168103559 19047960026418252155339)
            ·
              refine ⟨28571940039627378233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19047960026418252155339 28571940039627378233009)
              ·
                refine ⟨21428955029720533674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28571940039627378233009 21428955029720533674757)
                ·
                  refine ⟨4017929068072600064017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21428955029720533674757 4017929068072600064017)
                  ·
                    rfl

theorem cell21_17606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_17606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17606 prefixEnd_17606 := by exact prefixLift 17606
  have htrace : WordTrace (prefixWord ++ tailWord_17606) baseStart_17606 baseEnd_17606 := by
    simpa [prefixWord, tailWord_17606, baseEnd_17606] using wordTrace_append hprefix tailTrace_17606
  have hstable : (prefixWord ++ tailWord_17606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17606).length < 2 ^ (prefixWord ++ tailWord_17606).sum := by decide
  have hdescent : baseEnd_17606 < baseStart_17606 := by decide
  rcases family_descends (prefixWord ++ tailWord_17606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17642 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_17642 : Nat := 118140960795 + 17642 * 2 ^ 59
def prefixEnd_17642 : Nat := 4983230072969 + 3 ^ 40 * 17642 * 2
def baseEnd_17642 : Nat := 4026144758544537463943

theorem tailTrace_17642 : CollatzResearch.WordTrace tailWord_17642 prefixEnd_17642 4026144758544537463943 := by
  unfold tailWord_17642
  simp only [CollatzResearch.WordTrace]
  refine ⟨160864150523380464707795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 428971068062347905887453 160864150523380464707795)
  ·
    refine ⟨241296225785070697061693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160864150523380464707795 241296225785070697061693)
    ·
      refine ⟨90486084669401511398135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241296225785070697061693 90486084669401511398135)
      ·
        refine ⟨135729127004102267097203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90486084669401511398135 135729127004102267097203)
        ·
          refine ⟨203593690506153400645805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135729127004102267097203 203593690506153400645805)
          ·
            refine ⟨76347633939807525242177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203593690506153400645805 76347633939807525242177)
            ·
              refine ⟨57260725454855643931633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76347633939807525242177 57260725454855643931633)
              ·
                refine ⟨42945544091141732948725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57260725454855643931633 42945544091141732948725)
                ·
                  refine ⟨4026144758544537463943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42945544091141732948725 4026144758544537463943)
                  ·
                    rfl

theorem cell21_17642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_17642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17642 prefixEnd_17642 := by exact prefixLift 17642
  have htrace : WordTrace (prefixWord ++ tailWord_17642) baseStart_17642 baseEnd_17642 := by
    simpa [prefixWord, tailWord_17642, baseEnd_17642] using wordTrace_append hprefix tailTrace_17642
  have hstable : (prefixWord ++ tailWord_17642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17642).length < 2 ^ (prefixWord ++ tailWord_17642).sum := by decide
  have hdescent : baseEnd_17642 < baseStart_17642 := by decide
  rcases family_descends (prefixWord ++ tailWord_17642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17645 : List Nat := [1, 5, 1, 2, 2, 3, 2, 5]
def baseStart_17645 : Nat := 118140960795 + 17645 * 2 ^ 59
def prefixEnd_17645 : Nat := 4983230072969 + 3 ^ 40 * 17645 * 2
def baseEnd_17645 : Nat := 1342276466472399637979

theorem tailTrace_17645 : CollatzResearch.WordTrace tailWord_17645 prefixEnd_17645 1342276466472399637979 := by
  unfold tailWord_17645
  simp only [CollatzResearch.WordTrace]
  refine ⟨643566021082653371190389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 429044014055102247460259 643566021082653371190389)
  ·
    refine ⟨60334314476498753549099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 643566021082653371190389 60334314476498753549099)
    ·
      refine ⟨90501471714748130323649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60334314476498753549099 90501471714748130323649)
      ·
        refine ⟨67876103786061097742737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90501471714748130323649 67876103786061097742737)
        ·
          refine ⟨50907077839545823307053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67876103786061097742737 50907077839545823307053)
          ·
            refine ⟨19090154189829683740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50907077839545823307053 19090154189829683740145)
            ·
              refine ⟨14317615642372262805109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19090154189829683740145 14317615642372262805109)
              ·
                refine ⟨1342276466472399637979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14317615642372262805109 1342276466472399637979)
                ·
                  rfl

theorem cell21_17645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].length) (baseStart_17645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17645 prefixEnd_17645 := by exact prefixLift 17645
  have htrace : WordTrace (prefixWord ++ tailWord_17645) baseStart_17645 baseEnd_17645 := by
    simpa [prefixWord, tailWord_17645, baseEnd_17645] using wordTrace_append hprefix tailTrace_17645
  have hstable : (prefixWord ++ tailWord_17645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17645).length < 2 ^ (prefixWord ++ tailWord_17645).sum := by decide
  have hdescent : baseEnd_17645 < baseStart_17645 := by decide
  rcases family_descends (prefixWord ++ tailWord_17645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17676 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_17676 : Nat := 118140960795 + 17676 * 2 ^ 59
def prefixEnd_17676 : Nat := 4983230072969 + 3 ^ 40 * 17676 * 2
def baseEnd_17676 : Nat := 4033904021768033897207

theorem tailTrace_17676 : CollatzResearch.WordTrace tailWord_17676 prefixEnd_17676 4033904021768033897207 := by
  unfold tailWord_17676
  simp only [CollatzResearch.WordTrace]
  refine ⟨322348341985172832784441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 429797789313563777045921 322348341985172832784441)
  ·
    refine ⟨241761256488879624588331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322348341985172832784441 241761256488879624588331)
    ·
      refine ⟨362641884733319436882497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241761256488879624588331 362641884733319436882497)
      ·
        refine ⟨271981413549989577661873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362641884733319436882497 271981413549989577661873)
        ·
          refine ⟨203986060162492183246405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271981413549989577661873 203986060162492183246405)
          ·
            refine ⟨38247386280467284358701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203986060162492183246405 38247386280467284358701)
            ·
              refine ⟨14342769855175231634513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38247386280467284358701 14342769855175231634513)
              ·
                refine ⟨10757077391381423725885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14342769855175231634513 10757077391381423725885)
                ·
                  refine ⟨4033904021768033897207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10757077391381423725885 4033904021768033897207)
                  ·
                    rfl

theorem cell21_17676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_17676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17676 prefixEnd_17676 := by exact prefixLift 17676
  have htrace : WordTrace (prefixWord ++ tailWord_17676) baseStart_17676 baseEnd_17676 := by
    simpa [prefixWord, tailWord_17676, baseEnd_17676] using wordTrace_append hprefix tailTrace_17676
  have hstable : (prefixWord ++ tailWord_17676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17676).length < 2 ^ (prefixWord ++ tailWord_17676).sum := by decide
  have hdescent : baseEnd_17676 < baseStart_17676 := by decide
  rcases family_descends (prefixWord ++ tailWord_17676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17687 : List Nat := [1, 1, 3, 4, 1, 1, 4, 6]
def baseStart_17687 : Nat := 118140960795 + 17687 * 2 ^ 59
def prefixEnd_17687 : Nat := 4983230072969 + 3 ^ 40 * 17687 * 2
def baseEnd_17687 : Nat := 1345471457211486404617

theorem tailTrace_17687 : CollatzResearch.WordTrace tailWord_17687 prefixEnd_17687 1345471457211486404617 := by
  unfold tailWord_17687
  simp only [CollatzResearch.WordTrace]
  refine ⟨645097886930494544219315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 430065257953663029479543 645097886930494544219315)
  ·
    refine ⟨967646830395741816328973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645097886930494544219315 967646830395741816328973)
    ·
      refine ⟨362867561398403181123365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 967646830395741816328973 362867561398403181123365)
      ·
        refine ⟨68037667762200596460631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362867561398403181123365 68037667762200596460631)
        ·
          refine ⟨102056501643300894690947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68037667762200596460631 102056501643300894690947)
          ·
            refine ⟨153084752464951342036421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102056501643300894690947 153084752464951342036421)
            ·
              refine ⟨28703391087178376631829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153084752464951342036421 28703391087178376631829)
              ·
                refine ⟨1345471457211486404617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28703391087178376631829 1345471457211486404617)
                ·
                  rfl

theorem cell21_17687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_17687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17687 prefixEnd_17687 := by exact prefixLift 17687
  have htrace : WordTrace (prefixWord ++ tailWord_17687) baseStart_17687 baseEnd_17687 := by
    simpa [prefixWord, tailWord_17687, baseEnd_17687] using wordTrace_append hprefix tailTrace_17687
  have hstable : (prefixWord ++ tailWord_17687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17687).length < 2 ^ (prefixWord ++ tailWord_17687).sum := by decide
  have hdescent : baseEnd_17687 < baseStart_17687 := by decide
  rcases family_descends (prefixWord ++ tailWord_17687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17690 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_17690 : Nat := 118140960795 + 17690 * 2 ^ 59
def prefixEnd_17690 : Nat := 4983230072969 + 3 ^ 40 * 17690 * 2
def baseEnd_17690 : Nat := 4037099012507120663845

theorem tailTrace_17690 : CollatzResearch.WordTrace tailWord_17690 prefixEnd_17690 4037099012507120663845 := by
  unfold tailWord_17690
  simp only [CollatzResearch.WordTrace]
  refine ⟨161301826479906514144631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 430138203946417371052349 161301826479906514144631)
  ·
    refine ⟨241952739719859771216947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161301826479906514144631 241952739719859771216947)
    ·
      refine ⟨362929109579789656825421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241952739719859771216947 362929109579789656825421)
      ·
        refine ⟨136098416092421121309533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362929109579789656825421 136098416092421121309533)
        ·
          refine ⟨51036906034657920491075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136098416092421121309533 51036906034657920491075)
          ·
            refine ⟨76555359051986880736613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51036906034657920491075 76555359051986880736613)
            ·
              refine ⟨14354129822247540138115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76555359051986880736613 14354129822247540138115)
              ·
                refine ⟨21531194733371310207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14354129822247540138115 21531194733371310207173)
                ·
                  refine ⟨4037099012507120663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21531194733371310207173 4037099012507120663845)
                  ·
                    rfl

theorem cell21_17690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_17690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17690 prefixEnd_17690 := by exact prefixLift 17690
  have htrace : WordTrace (prefixWord ++ tailWord_17690) baseStart_17690 baseEnd_17690 := by
    simpa [prefixWord, tailWord_17690, baseEnd_17690] using wordTrace_append hprefix tailTrace_17690
  have hstable : (prefixWord ++ tailWord_17690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17690).length < 2 ^ (prefixWord ++ tailWord_17690).sum := by decide
  have hdescent : baseEnd_17690 < baseStart_17690 := by decide
  rcases family_descends (prefixWord ++ tailWord_17690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17735 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 3]
def baseStart_17735 : Nat := 118140960795 + 17735 * 2 ^ 59
def prefixEnd_17735 : Nat := 4983230072969 + 3 ^ 40 * 17735 * 2
def baseEnd_17735 : Nat := 4047368625597042413753

theorem tailTrace_17735 : CollatzResearch.WordTrace tailWord_17735 prefixEnd_17735 4047368625597042413753 := by
  unfold tailWord_17735
  simp only [CollatzResearch.WordTrace]
  refine ⟨646848590756598741966659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 431232393837732494644439 646848590756598741966659)
  ·
    refine ⟨970272886134898112949989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646848590756598741966659 970272886134898112949989)
    ·
      refine ⟨181926166150293396178123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 970272886134898112949989 181926166150293396178123)
      ·
        refine ⟨272889249225440094267185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181926166150293396178123 272889249225440094267185)
        ·
          refine ⟨204666936919080070700389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272889249225440094267185 204666936919080070700389)
          ·
            refine ⟨38375050672327513256323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204666936919080070700389 38375050672327513256323)
            ·
              refine ⟨57562576008491269884485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38375050672327513256323 57562576008491269884485)
              ·
                refine ⟨10792983001592113103341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57562576008491269884485 10792983001592113103341)
                ·
                  refine ⟨4047368625597042413753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10792983001592113103341 4047368625597042413753)
                  ·
                    rfl

theorem cell21_17735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].length) (baseStart_17735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17735 prefixEnd_17735 := by exact prefixLift 17735
  have htrace : WordTrace (prefixWord ++ tailWord_17735) baseStart_17735 baseEnd_17735 := by
    simpa [prefixWord, tailWord_17735, baseEnd_17735] using wordTrace_append hprefix tailTrace_17735
  have hstable : (prefixWord ++ tailWord_17735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17735).length < 2 ^ (prefixWord ++ tailWord_17735).sum := by decide
  have hdescent : baseEnd_17735 < baseStart_17735 := by decide
  rcases family_descends (prefixWord ++ tailWord_17735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17749 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_17749 : Nat := 118140960795 + 17749 * 2 ^ 59
def prefixEnd_17749 : Nat := 4983230072969 + 3 ^ 40 * 17749 * 2
def baseEnd_17749 : Nat := 4050563616336129180391

theorem tailTrace_17749 : CollatzResearch.WordTrace tailWord_17749 prefixEnd_17749 4050563616336129180391 := by
  unfold tailWord_17749
  simp only [CollatzResearch.WordTrace]
  refine ⟨647359212705879132976301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 431572808470586088650867 647359212705879132976301)
  ·
    refine ⟨242759704764704674866113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 647359212705879132976301 242759704764704674866113)
    ·
      refine ⟨182069778573528506149585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242759704764704674866113 182069778573528506149585)
      ·
        refine ⟨136552333930146379612189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182069778573528506149585 136552333930146379612189)
        ·
          refine ⟨51207125223804892354571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136552333930146379612189 51207125223804892354571)
          ·
            refine ⟨76810687835707338531857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51207125223804892354571 76810687835707338531857)
            ·
              refine ⟨57608015876780503898893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76810687835707338531857 57608015876780503898893)
              ·
                refine ⟨21603005953792688962085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57608015876780503898893 21603005953792688962085)
                ·
                  refine ⟨4050563616336129180391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21603005953792688962085 4050563616336129180391)
                  ·
                    rfl

theorem cell21_17749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_17749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17749 prefixEnd_17749 := by exact prefixLift 17749
  have htrace : WordTrace (prefixWord ++ tailWord_17749) baseStart_17749 baseEnd_17749 := by
    simpa [prefixWord, tailWord_17749, baseEnd_17749] using wordTrace_append hprefix tailTrace_17749
  have hstable : (prefixWord ++ tailWord_17749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17749).length < 2 ^ (prefixWord ++ tailWord_17749).sum := by decide
  have hdescent : baseEnd_17749 < baseStart_17749 := by decide
  rcases family_descends (prefixWord ++ tailWord_17749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17898 : List Nat := [3, 1, 3, 1, 13]
def baseStart_17898 : Nat := 118140960795 + 17898 * 2 ^ 59
def prefixEnd_17898 : Nat := 4983230072969 + 3 ^ 40 * 17898 * 2
def baseEnd_17898 : Nat := 50426758596851619713

theorem tailTrace_17898 : CollatzResearch.WordTrace tailWord_17898 prefixEnd_17898 50426758596851619713 := by
  unfold tailWord_17898
  simp only [CollatzResearch.WordTrace]
  refine ⟨163198422291519395037587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 435195792777385053433565 163198422291519395037587)
  ·
    refine ⟨244797633437279092556381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163198422291519395037587 244797633437279092556381)
    ·
      refine ⟨91799112538979659708643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244797633437279092556381 91799112538979659708643)
      ·
        refine ⟨137698668808469489562965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91799112538979659708643 137698668808469489562965)
        ·
          refine ⟨50426758596851619713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 137698668808469489562965 50426758596851619713)
          ·
            rfl

theorem cell21_17898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 13].length) (baseStart_17898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17898 prefixEnd_17898 := by exact prefixLift 17898
  have htrace : WordTrace (prefixWord ++ tailWord_17898) baseStart_17898 baseEnd_17898 := by
    simpa [prefixWord, tailWord_17898, baseEnd_17898] using wordTrace_append hprefix tailTrace_17898
  have hstable : (prefixWord ++ tailWord_17898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17898).length < 2 ^ (prefixWord ++ tailWord_17898).sum := by decide
  have hdescent : baseEnd_17898 < baseStart_17898 := by decide
  rcases family_descends (prefixWord ++ tailWord_17898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17904 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_17904 : Nat := 118140960795 + 17904 * 2 ^ 59
def prefixEnd_17904 : Nat := 4983230072969 + 3 ^ 40 * 17904 * 2
def baseEnd_17904 : Nat := 4085936728090304096741

theorem tailTrace_17904 : CollatzResearch.WordTrace tailWord_17904 prefixEnd_17904 4085936728090304096741 := by
  unfold tailWord_17904
  simp only [CollatzResearch.WordTrace]
  refine ⟨326506263572170302434383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 435341684762893736579177 326506263572170302434383)
  ·
    refine ⟨489759395358255453651575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326506263572170302434383 489759395358255453651575)
    ·
      refine ⟨734639093037383180477363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489759395358255453651575 734639093037383180477363)
      ·
        refine ⟨1101958639556074770716045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734639093037383180477363 1101958639556074770716045)
        ·
          refine ⟨413234489833528039018517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1101958639556074770716045 413234489833528039018517)
          ·
            refine ⟨19370366710946626828993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 413234489833528039018517 19370366710946626828993)
            ·
              refine ⟨14527775033209970121745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19370366710946626828993 14527775033209970121745)
              ·
                refine ⟨10895831274907477591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14527775033209970121745 10895831274907477591309)
                ·
                  refine ⟨4085936728090304096741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10895831274907477591309 4085936728090304096741)
                  ·
                    rfl

theorem cell21_17904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_17904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17904 prefixEnd_17904 := by exact prefixLift 17904
  have htrace : WordTrace (prefixWord ++ tailWord_17904) baseStart_17904 baseEnd_17904 := by
    simpa [prefixWord, tailWord_17904, baseEnd_17904] using wordTrace_append hprefix tailTrace_17904
  have hstable : (prefixWord ++ tailWord_17904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17904).length < 2 ^ (prefixWord ++ tailWord_17904).sum := by decide
  have hdescent : baseEnd_17904 < baseStart_17904 := by decide
  rcases family_descends (prefixWord ++ tailWord_17904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17929 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_17929 : Nat := 118140960795 + 17929 * 2 ^ 59
def prefixEnd_17929 : Nat := 4983230072969 + 3 ^ 40 * 17929 * 2
def baseEnd_17929 : Nat := 4091642068695816180023

theorem tailTrace_17929 : CollatzResearch.WordTrace tailWord_17929 prefixEnd_17929 4091642068695816180023 := by
  unfold tailWord_17929
  simp only [CollatzResearch.WordTrace]
  refine ⟨653924352053769874528841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435949568035846583019227 653924352053769874528841)
  ·
    refine ⟨490443264040327405896631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653924352053769874528841 490443264040327405896631)
    ·
      refine ⟨735664896060491108844947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490443264040327405896631 735664896060491108844947)
      ·
        refine ⟨1103497344090736663267421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735664896060491108844947 1103497344090736663267421)
        ·
          refine ⟨413811504034026248725283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1103497344090736663267421 413811504034026248725283)
          ·
            refine ⟨620717256051039373087925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413811504034026248725283 620717256051039373087925)
            ·
              refine ⟨58192242754784941226993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 620717256051039373087925 58192242754784941226993)
              ·
                refine ⟨43644182066088705920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58192242754784941226993 43644182066088705920245)
                ·
                  refine ⟨4091642068695816180023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43644182066088705920245 4091642068695816180023)
                  ·
                    rfl

theorem cell21_17929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_17929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17929 prefixEnd_17929 := by exact prefixLift 17929
  have htrace : WordTrace (prefixWord ++ tailWord_17929) baseStart_17929 baseEnd_17929 := by
    simpa [prefixWord, tailWord_17929, baseEnd_17929] using wordTrace_append hprefix tailTrace_17929
  have hstable : (prefixWord ++ tailWord_17929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17929).length < 2 ^ (prefixWord ++ tailWord_17929).sum := by decide
  have hdescent : baseEnd_17929 < baseStart_17929 := by decide
  rcases family_descends (prefixWord ++ tailWord_17929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17932 : List Nat := [2, 2, 1, 2, 5, 1, 3, 5]
def baseStart_17932 : Nat := 118140960795 + 17932 * 2 ^ 59
def prefixEnd_17932 : Nat := 4983230072969 + 3 ^ 40 * 17932 * 2
def baseEnd_17932 : Nat := 1364108903189492543339

theorem tailTrace_17932 : CollatzResearch.WordTrace tailWord_17932 prefixEnd_17932 1364108903189492543339 := by
  unfold tailWord_17932
  simp only [CollatzResearch.WordTrace]
  refine ⟨327016885521450693444025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 436022514028600924592033 327016885521450693444025)
  ·
    refine ⟨245262664141088020083019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 327016885521450693444025 245262664141088020083019)
    ·
      refine ⟨367893996211632030124529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245262664141088020083019 367893996211632030124529)
      ·
        refine ⟨275920497158724022593397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367893996211632030124529 275920497158724022593397)
        ·
          refine ⟨25867546608630377118131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275920497158724022593397 25867546608630377118131)
          ·
            refine ⟨38801319912945565677197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25867546608630377118131 38801319912945565677197)
            ·
              refine ⟨14550494967354587128949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38801319912945565677197 14550494967354587128949)
              ·
                refine ⟨1364108903189492543339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14550494967354587128949 1364108903189492543339)
                ·
                  rfl

theorem cell21_17932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_17932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17932 prefixEnd_17932 := by exact prefixLift 17932
  have htrace : WordTrace (prefixWord ++ tailWord_17932) baseStart_17932 baseEnd_17932 := by
    simpa [prefixWord, tailWord_17932, baseEnd_17932] using wordTrace_append hprefix tailTrace_17932
  have hstable : (prefixWord ++ tailWord_17932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17932).length < 2 ^ (prefixWord ++ tailWord_17932).sum := by decide
  have hdescent : baseEnd_17932 < baseStart_17932 := by decide
  rcases family_descends (prefixWord ++ tailWord_17932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17991 : List Nat := [1, 1, 4, 1, 5, 1, 1, 7]
def baseStart_17991 : Nat := 118140960795 + 17991 * 2 ^ 59
def prefixEnd_17991 : Nat := 4983230072969 + 3 ^ 40 * 17991 * 2
def baseEnd_17991 : Nat := 1368597104465828715521

theorem tailTrace_17991 : CollatzResearch.WordTrace tailWord_17991 prefixEnd_17991 1368597104465828715521 := by
  unfold tailWord_17991
  simp only [CollatzResearch.WordTrace]
  refine ⟨656185677829154463285827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 437457118552769642190551 656185677829154463285827)
  ·
    refine ⟨984278516743731694928741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656185677829154463285827 984278516743731694928741)
    ·
      refine ⟨184552221889449692799139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 984278516743731694928741 184552221889449692799139)
      ·
        refine ⟨276828332834174539198709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184552221889449692799139 276828332834174539198709)
        ·
          refine ⟨25952656203203863049879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 276828332834174539198709 25952656203203863049879)
          ·
            refine ⟨38928984304805794574819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25952656203203863049879 38928984304805794574819)
            ·
              refine ⟨58393476457208691862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38928984304805794574819 58393476457208691862229)
              ·
                refine ⟨1368597104465828715521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58393476457208691862229 1368597104465828715521)
                ·
                  rfl

theorem cell21_17991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_17991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17991 prefixEnd_17991 := by exact prefixLift 17991
  have htrace : WordTrace (prefixWord ++ tailWord_17991) baseStart_17991 baseEnd_17991 := by
    simpa [prefixWord, tailWord_17991, baseEnd_17991] using wordTrace_append hprefix tailTrace_17991
  have hstable : (prefixWord ++ tailWord_17991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17991).length < 2 ^ (prefixWord ++ tailWord_17991).sum := by decide
  have hdescent : baseEnd_17991 < baseStart_17991 := by decide
  rcases family_descends (prefixWord ++ tailWord_17991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17997 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 3]
def baseStart_17997 : Nat := 118140960795 + 17997 * 2 ^ 59
def prefixEnd_17997 : Nat := 4983230072969 + 3 ^ 40 * 17997 * 2
def baseEnd_17997 : Nat := 4107160595142809046551

theorem tailTrace_17997 : CollatzResearch.WordTrace tailWord_17997 prefixEnd_17997 4107160595142809046551 := by
  unfold tailWord_17997
  simp only [CollatzResearch.WordTrace]
  refine ⟨656404515807417488004245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 437603010538278325336163 656404515807417488004245)
  ·
    refine ⟨30768961678472694750199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 656404515807417488004245 30768961678472694750199)
    ·
      refine ⟨46153442517709042125299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30768961678472694750199 46153442517709042125299)
      ·
        refine ⟨69230163776563563187949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46153442517709042125299 69230163776563563187949)
        ·
          refine ⟨25961311416211336195481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69230163776563563187949 25961311416211336195481)
          ·
            refine ⟨19470983562158502146611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25961311416211336195481 19470983562158502146611)
            ·
              refine ⟨29206475343237753219917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19470983562158502146611 29206475343237753219917)
              ·
                refine ⟨10952428253714157457469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29206475343237753219917 10952428253714157457469)
                ·
                  refine ⟨4107160595142809046551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10952428253714157457469 4107160595142809046551)
                  ·
                    rfl

theorem cell21_17997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_17997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_17997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_17997 prefixEnd_17997 := by exact prefixLift 17997
  have htrace : WordTrace (prefixWord ++ tailWord_17997) baseStart_17997 baseEnd_17997 := by
    simpa [prefixWord, tailWord_17997, baseEnd_17997] using wordTrace_append hprefix tailTrace_17997
  have hstable : (prefixWord ++ tailWord_17997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17997).length < 2 ^ (prefixWord ++ tailWord_17997).sum := by decide
  have hdescent : baseEnd_17997 < baseStart_17997 := by decide
  rcases family_descends (prefixWord ++ tailWord_17997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18126 : List Nat := [4, 1, 1, 1, 3, 1, 10]
def baseStart_18126 : Nat := 118140960795 + 18126 * 2 ^ 59
def prefixEnd_18126 : Nat := 4983230072969 + 3 ^ 40 * 18126 * 2
def baseEnd_18126 : Nat := 459622239185250155143

theorem tailTrace_18126 : CollatzResearch.WordTrace tailWord_18126 prefixEnd_18126 459622239185250155143 := by
  unfold tailWord_18126
  simp only [CollatzResearch.WordTrace]
  refine ⟨82638691542509064931279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 440739688226715012966821 82638691542509064931279)
  ·
    refine ⟨123958037313763597396919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82638691542509064931279 123958037313763597396919)
    ·
      refine ⟨185937055970645396095379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123958037313763597396919 185937055970645396095379)
      ·
        refine ⟨278905583955968094143069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185937055970645396095379 278905583955968094143069)
        ·
          refine ⟨104589593983488035303651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278905583955968094143069 104589593983488035303651)
          ·
            refine ⟨156884390975232052955477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104589593983488035303651 156884390975232052955477)
            ·
              refine ⟨459622239185250155143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 156884390975232052955477 459622239185250155143)
              ·
                rfl

theorem cell21_18126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 10].length) (baseStart_18126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18126 prefixEnd_18126 := by exact prefixLift 18126
  have htrace : WordTrace (prefixWord ++ tailWord_18126) baseStart_18126 baseEnd_18126 := by
    simpa [prefixWord, tailWord_18126, baseEnd_18126] using wordTrace_append hprefix tailTrace_18126
  have hstable : (prefixWord ++ tailWord_18126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18126).length < 2 ^ (prefixWord ++ tailWord_18126).sum := by decide
  have hdescent : baseEnd_18126 < baseStart_18126 := by decide
  rcases family_descends (prefixWord ++ tailWord_18126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18129 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_18129 : Nat := 118140960795 + 18129 * 2 ^ 59
def prefixEnd_18129 : Nat := 4983230072969 + 3 ^ 40 * 18129 * 2
def baseEnd_18129 : Nat := 4137284793539912846281

theorem tailTrace_18129 : CollatzResearch.WordTrace tailWord_18129 prefixEnd_18129 4137284793539912846281 := by
  unfold tailWord_18129
  simp only [CollatzResearch.WordTrace]
  refine ⟨661218951329204031809441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 440812634219469354539627 661218951329204031809441)
  ·
    refine ⟨495914213496903023857081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 661218951329204031809441 495914213496903023857081)
    ·
      refine ⟨371935660122677267892811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 495914213496903023857081 371935660122677267892811)
      ·
        refine ⟨557903490184015901839217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371935660122677267892811 557903490184015901839217)
        ·
          refine ⟨418427617638011926379413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557903490184015901839217 418427617638011926379413)
          ·
            refine ⟨19613794576781809049035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 418427617638011926379413 19613794576781809049035)
            ·
              refine ⟨29420691865172713573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19613794576781809049035 29420691865172713573553)
              ·
                refine ⟨22065518898879535180165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29420691865172713573553 22065518898879535180165)
                ·
                  refine ⟨4137284793539912846281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22065518898879535180165 4137284793539912846281)
                  ·
                    rfl

theorem cell21_18129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_18129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18129 prefixEnd_18129 := by exact prefixLift 18129
  have htrace : WordTrace (prefixWord ++ tailWord_18129) baseStart_18129 baseEnd_18129 := by
    simpa [prefixWord, tailWord_18129, baseEnd_18129] using wordTrace_append hprefix tailTrace_18129
  have hstable : (prefixWord ++ tailWord_18129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18129).length < 2 ^ (prefixWord ++ tailWord_18129).sum := by decide
  have hdescent : baseEnd_18129 < baseStart_18129 := by decide
  rcases family_descends (prefixWord ++ tailWord_18129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18202 : List Nat := [3, 1, 1, 3, 2, 2, 1, 8]
def baseStart_18202 : Nat := 118140960795 + 18202 * 2 ^ 59
def prefixEnd_18202 : Nat := 4983230072969 + 3 ^ 40 * 18202 * 2
def baseEnd_18202 : Nat := 1384648129369336043155

theorem tailTrace_18202 : CollatzResearch.WordTrace tailWord_18202 prefixEnd_18202 1384648129369336043155 := by
  unfold tailWord_18202
  simp only [CollatzResearch.WordTrace]
  refine ⟨165970370016184374804215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 442587653376491666144573 165970370016184374804215)
  ·
    refine ⟨248955555024276562206323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165970370016184374804215 248955555024276562206323)
    ·
      refine ⟨373433332536414843309485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248955555024276562206323 373433332536414843309485)
      ·
        refine ⟨140037499701155566241057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373433332536414843309485 140037499701155566241057)
        ·
          refine ⟨105028124775866674680793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140037499701155566241057 105028124775866674680793)
          ·
            refine ⟨78771093581900006010595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105028124775866674680793 78771093581900006010595)
            ·
              refine ⟨118156640372850009015893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78771093581900006010595 118156640372850009015893)
              ·
                refine ⟨1384648129369336043155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 118156640372850009015893 1384648129369336043155)
                ·
                  rfl

theorem cell21_18202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_18202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18202 prefixEnd_18202 := by exact prefixLift 18202
  have htrace : WordTrace (prefixWord ++ tailWord_18202) baseStart_18202 baseEnd_18202 := by
    simpa [prefixWord, tailWord_18202, baseEnd_18202] using wordTrace_append hprefix tailTrace_18202
  have hstable : (prefixWord ++ tailWord_18202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18202).length < 2 ^ (prefixWord ++ tailWord_18202).sum := by decide
  have hdescent : baseEnd_18202 < baseStart_18202 := by decide
  rcases family_descends (prefixWord ++ tailWord_18202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18247 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_18247 : Nat := 118140960795 + 18247 * 2 ^ 59
def prefixEnd_18247 : Nat := 4983230072969 + 3 ^ 40 * 18247 * 2
def baseEnd_18247 : Nat := 4164214001197929879373

theorem tailTrace_18247 : CollatzResearch.WordTrace tailWord_18247 prefixEnd_18247 4164214001197929879373 := by
  unfold tailWord_18247
  simp only [CollatzResearch.WordTrace]
  refine ⟨665522764901710184604995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443681843267806789736663 665522764901710184604995)
  ·
    refine ⟨998284147352565276907493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665522764901710184604995 998284147352565276907493)
    ·
      refine ⟨187178277628605989420155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 998284147352565276907493 187178277628605989420155)
      ·
        refine ⟨280767416442908984130233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187178277628605989420155 280767416442908984130233)
        ·
          refine ⟨210575562332181738097675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280767416442908984130233 210575562332181738097675)
          ·
            refine ⟨315863343498272607146513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210575562332181738097675 315863343498272607146513)
            ·
              refine ⟨236897507623704455359885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315863343498272607146513 236897507623704455359885)
              ·
                refine ⟨88836565358889170759957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236897507623704455359885 88836565358889170759957)
                ·
                  refine ⟨4164214001197929879373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88836565358889170759957 4164214001197929879373)
                  ·
                    rfl

theorem cell21_18247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_18247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18247 prefixEnd_18247 := by exact prefixLift 18247
  have htrace : WordTrace (prefixWord ++ tailWord_18247) baseStart_18247 baseEnd_18247 := by
    simpa [prefixWord, tailWord_18247, baseEnd_18247] using wordTrace_append hprefix tailTrace_18247
  have hstable : (prefixWord ++ tailWord_18247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18247).length < 2 ^ (prefixWord ++ tailWord_18247).sum := by decide
  have hdescent : baseEnd_18247 < baseStart_18247 := by decide
  rcases family_descends (prefixWord ++ tailWord_18247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18250 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_18250 : Nat := 118140960795 + 18250 * 2 ^ 59
def prefixEnd_18250 : Nat := 4983230072969 + 3 ^ 40 * 18250 * 2
def baseEnd_18250 : Nat := 4164898642070591329367

theorem tailTrace_18250 : CollatzResearch.WordTrace tailWord_18250 prefixEnd_18250 4164898642070591329367 := by
  unfold tailWord_18250
  simp only [CollatzResearch.WordTrace]
  refine ⟨166408045972710424241051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 443754789260561131309469 166408045972710424241051)
  ·
    refine ⟨249612068959065636361577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166408045972710424241051 249612068959065636361577)
    ·
      refine ⟨187209051719299227271183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249612068959065636361577 187209051719299227271183)
      ·
        refine ⟨280813577578948840906775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187209051719299227271183 280813577578948840906775)
        ·
          refine ⟨421220366368423261360163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280813577578948840906775 421220366368423261360163)
          ·
            refine ⟨631830549552634892040245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421220366368423261360163 631830549552634892040245)
            ·
              refine ⟨59234114020559521128773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 631830549552634892040245 59234114020559521128773)
              ·
                refine ⟨11106396378854910211645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59234114020559521128773 11106396378854910211645)
                ·
                  refine ⟨4164898642070591329367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11106396378854910211645 4164898642070591329367)
                  ·
                    rfl

theorem cell21_18250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_18250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18250 prefixEnd_18250 := by exact prefixLift 18250
  have htrace : WordTrace (prefixWord ++ tailWord_18250) baseStart_18250 baseEnd_18250 := by
    simpa [prefixWord, tailWord_18250, baseEnd_18250] using wordTrace_append hprefix tailTrace_18250
  have hstable : (prefixWord ++ tailWord_18250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18250).length < 2 ^ (prefixWord ++ tailWord_18250).sum := by decide
  have hdescent : baseEnd_18250 < baseStart_18250 := by decide
  rcases family_descends (prefixWord ++ tailWord_18250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18309 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_18309 : Nat := 118140960795 + 18309 * 2 ^ 59
def prefixEnd_18309 : Nat := 4983230072969 + 3 ^ 40 * 18309 * 2
def baseEnd_18309 : Nat := 4178363245899599845913

theorem tailTrace_18309 : CollatzResearch.WordTrace tailWord_18309 prefixEnd_18309 4178363245899599845913 := by
  unfold tailWord_18309
  simp only [CollatzResearch.WordTrace]
  refine ⟨667784090677094773361981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 445189393784729848907987 667784090677094773361981)
  ·
    refine ⟨250419034003910540010743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 667784090677094773361981 250419034003910540010743)
    ·
      refine ⟨375628551005865810016115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250419034003910540010743 375628551005865810016115)
      ·
        refine ⟨563442826508798715024173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375628551005865810016115 563442826508798715024173)
        ·
          refine ⟨211291059940799518134065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 563442826508798715024173 211291059940799518134065)
          ·
            refine ⟨158468294955599638600549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211291059940799518134065 158468294955599638600549)
            ·
              refine ⟨29712805304174932237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158468294955599638600549 29712805304174932237603)
              ·
                refine ⟨44569207956262398356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29712805304174932237603 44569207956262398356405)
                ·
                  refine ⟨4178363245899599845913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44569207956262398356405 4178363245899599845913)
                  ·
                    rfl

theorem cell21_18309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_18309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18309 prefixEnd_18309 := by exact prefixLift 18309
  have htrace : WordTrace (prefixWord ++ tailWord_18309) baseStart_18309 baseEnd_18309 := by
    simpa [prefixWord, tailWord_18309, baseEnd_18309] using wordTrace_append hprefix tailTrace_18309
  have hstable : (prefixWord ++ tailWord_18309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18309).length < 2 ^ (prefixWord ++ tailWord_18309).sum := by decide
  have hdescent : baseEnd_18309 < baseStart_18309 := by decide
  rcases family_descends (prefixWord ++ tailWord_18309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18343 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 3]
def baseStart_18343 : Nat := 118140960795 + 18343 * 2 ^ 59
def prefixEnd_18343 : Nat := 4983230072969 + 3 ^ 40 * 18343 * 2
def baseEnd_18343 : Nat := 4186122509123096279177

theorem tailTrace_18343 : CollatzResearch.WordTrace tailWord_18343 prefixEnd_18343 4186122509123096279177 := by
  unfold tailWord_18343
  simp only [CollatzResearch.WordTrace]
  refine ⟨669024172553918580099683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 446016115035945720066455 669024172553918580099683)
  ·
    refine ⟨1003536258830877870149525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 669024172553918580099683 1003536258830877870149525)
    ·
      refine ⟨47040762132697400163259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1003536258830877870149525 47040762132697400163259)
      ·
        refine ⟨70561143199046100244889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47040762132697400163259 70561143199046100244889)
        ·
          refine ⟨52920857399284575183667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70561143199046100244889 52920857399284575183667)
          ·
            refine ⟨79381286098926862775501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52920857399284575183667 79381286098926862775501)
            ·
              refine ⟨29767982287097573540813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79381286098926862775501 29767982287097573540813)
              ·
                refine ⟨11162993357661590077805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29767982287097573540813 11162993357661590077805)
                ·
                  refine ⟨4186122509123096279177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11162993357661590077805 4186122509123096279177)
                  ·
                    rfl

theorem cell21_18343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 3].length) (baseStart_18343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18343 prefixEnd_18343 := by exact prefixLift 18343
  have htrace : WordTrace (prefixWord ++ tailWord_18343) baseStart_18343 baseEnd_18343 := by
    simpa [prefixWord, tailWord_18343, baseEnd_18343] using wordTrace_append hprefix tailTrace_18343
  have hstable : (prefixWord ++ tailWord_18343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18343).length < 2 ^ (prefixWord ++ tailWord_18343).sum := by decide
  have hdescent : baseEnd_18343 < baseStart_18343 := by decide
  rcases family_descends (prefixWord ++ tailWord_18343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18475 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_18475 : Nat := 118140960795 + 18475 * 2 ^ 59
def prefixEnd_18475 : Nat := 4983230072969 + 3 ^ 40 * 18475 * 2
def baseEnd_18475 : Nat := 4216246707520200078907

theorem tailTrace_18475 : CollatzResearch.WordTrace tailWord_18475 prefixEnd_18475 4216246707520200078907 := by
  unfold tailWord_18475
  simp only [CollatzResearch.WordTrace]
  refine ⟨673838608075705123904879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 449225738717136749269919 673838608075705123904879)
  ·
    refine ⟨1010757912113557685857319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673838608075705123904879 1010757912113557685857319)
    ·
      refine ⟨1516136868170336528785979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010757912113557685857319 1516136868170336528785979)
      ·
        refine ⟨2274205302255504793178969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516136868170336528785979 2274205302255504793178969)
        ·
          refine ⟨1705653976691628594884227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274205302255504793178969 1705653976691628594884227)
          ·
            refine ⟨2558480965037442892326341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705653976691628594884227 2558480965037442892326341)
            ·
              refine ⟨479715180944520542311189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2558480965037442892326341 479715180944520542311189)
              ·
                refine ⟨22486649106774400420837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 479715180944520542311189 22486649106774400420837)
                ·
                  refine ⟨4216246707520200078907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22486649106774400420837 4216246707520200078907)
                  ·
                    rfl

theorem cell21_18475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_18475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18475 prefixEnd_18475 := by exact prefixLift 18475
  have htrace : WordTrace (prefixWord ++ tailWord_18475) baseStart_18475 baseEnd_18475 := by
    simpa [prefixWord, tailWord_18475, baseEnd_18475] using wordTrace_append hprefix tailTrace_18475
  have hstable : (prefixWord ++ tailWord_18475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18475).length < 2 ^ (prefixWord ++ tailWord_18475).sum := by decide
  have hdescent : baseEnd_18475 < baseStart_18475 := by decide
  rcases family_descends (prefixWord ++ tailWord_18475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18478 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_18478 : Nat := 118140960795 + 18478 * 2 ^ 59
def prefixEnd_18478 : Nat := 4983230072969 + 3 ^ 40 * 18478 * 2
def baseEnd_18478 : Nat := 4216931348392861528901

theorem tailTrace_18478 : CollatzResearch.WordTrace tailWord_18478 prefixEnd_18478 4216931348392861528901 := by
  unfold tailWord_18478
  simp only [CollatzResearch.WordTrace]
  refine ⟨84243503383104579533011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 449298684709891090842725 84243503383104579533011)
  ·
    refine ⟨126365255074656869299517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84243503383104579533011 126365255074656869299517)
    ·
      refine ⟨47386970652996325987319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126365255074656869299517 47386970652996325987319)
      ·
        refine ⟨71080455979494488980979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47386970652996325987319 71080455979494488980979)
        ·
          refine ⟨106620683969241733471469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71080455979494488980979 106620683969241733471469)
          ·
            refine ⟨39982756488465650051801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106620683969241733471469 39982756488465650051801)
            ·
              refine ⟨29987067366349237538851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39982756488465650051801 29987067366349237538851)
              ·
                refine ⟨44980601049523856308277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29987067366349237538851 44980601049523856308277)
                ·
                  refine ⟨4216931348392861528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44980601049523856308277 4216931348392861528901)
                  ·
                    rfl

theorem cell21_18478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_18478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18478 prefixEnd_18478 := by exact prefixLift 18478
  have htrace : WordTrace (prefixWord ++ tailWord_18478) baseStart_18478 baseEnd_18478 := by
    simpa [prefixWord, tailWord_18478, baseEnd_18478] using wordTrace_append hprefix tailTrace_18478
  have hstable : (prefixWord ++ tailWord_18478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18478).length < 2 ^ (prefixWord ++ tailWord_18478).sum := by decide
  have hdescent : baseEnd_18478 < baseStart_18478 := by decide
  rcases family_descends (prefixWord ++ tailWord_18478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18661 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 4]
def baseStart_18661 : Nat := 118140960795 + 18661 * 2 ^ 59
def prefixEnd_18661 : Nat := 4983230072969 + 3 ^ 40 * 18661 * 2
def baseEnd_18661 : Nat := 4258694441625209978527

theorem tailTrace_18661 : CollatzResearch.WordTrace tailWord_18661 prefixEnd_18661 4258694441625209978527 := by
  unfold tailWord_18661
  simp only [CollatzResearch.WordTrace]
  refine ⟨680622585401858890175837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 453748390267905926783891 680622585401858890175837)
  ·
    refine ⟨255233469525697083815939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 680622585401858890175837 255233469525697083815939)
    ·
      refine ⟨382850204288545625723909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255233469525697083815939 382850204288545625723909)
      ·
        refine ⟨71784413304102304823233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382850204288545625723909 71784413304102304823233)
        ·
          refine ⟨53838309978076728617425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71784413304102304823233 53838309978076728617425)
          ·
            refine ⟨40378732483557546463069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53838309978076728617425 40378732483557546463069)
            ·
              refine ⟨15142024681334079923651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40378732483557546463069 15142024681334079923651)
              ·
                refine ⟨22713037022001119885477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142024681334079923651 22713037022001119885477)
                ·
                  refine ⟨4258694441625209978527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22713037022001119885477 4258694441625209978527)
                  ·
                    rfl

theorem cell21_18661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_18661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18661 prefixEnd_18661 := by exact prefixLift 18661
  have htrace : WordTrace (prefixWord ++ tailWord_18661) baseStart_18661 baseEnd_18661 := by
    simpa [prefixWord, tailWord_18661, baseEnd_18661] using wordTrace_append hprefix tailTrace_18661
  have hstable : (prefixWord ++ tailWord_18661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18661).length < 2 ^ (prefixWord ++ tailWord_18661).sum := by decide
  have hdescent : baseEnd_18661 < baseStart_18661 := by decide
  rcases family_descends (prefixWord ++ tailWord_18661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18720 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_18720 : Nat := 118140960795 + 18720 * 2 ^ 59
def prefixEnd_18720 : Nat := 4983230072969 + 3 ^ 40 * 18720 * 2
def baseEnd_18720 : Nat := 4272159045454218495073

theorem tailTrace_18720 : CollatzResearch.WordTrace tailWord_18720 prefixEnd_18720 4272159045454218495073 := by
  unfold tailWord_18720
  simp only [CollatzResearch.WordTrace]
  refine ⟨341387246094055983286807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 455182994792074644382409 341387246094055983286807)
  ·
    refine ⟨512080869141083974930211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 341387246094055983286807 512080869141083974930211)
    ·
      refine ⟨768121303711625962395317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512080869141083974930211 768121303711625962395317)
      ·
        refine ⟨72011372222964933974561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 768121303711625962395317 72011372222964933974561)
        ·
          refine ⟨54008529167223700480921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72011372222964933974561 54008529167223700480921)
          ·
            refine ⟨40506396875417775360691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54008529167223700480921 40506396875417775360691)
            ·
              refine ⟨60759595313126663041037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40506396875417775360691 60759595313126663041037)
              ·
                refine ⟨22784848242422498640389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60759595313126663041037 22784848242422498640389)
                ·
                  refine ⟨4272159045454218495073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22784848242422498640389 4272159045454218495073)
                  ·
                    rfl

theorem cell21_18720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_18720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18720 prefixEnd_18720 := by exact prefixLift 18720
  have htrace : WordTrace (prefixWord ++ tailWord_18720) baseStart_18720 baseEnd_18720 := by
    simpa [prefixWord, tailWord_18720, baseEnd_18720] using wordTrace_append hprefix tailTrace_18720
  have hstable : (prefixWord ++ tailWord_18720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18720).length < 2 ^ (prefixWord ++ tailWord_18720).sum := by decide
  have hdescent : baseEnd_18720 < baseStart_18720 := by decide
  rcases family_descends (prefixWord ++ tailWord_18720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18855 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_18855 : Nat := 118140960795 + 18855 * 2 ^ 59
def prefixEnd_18855 : Nat := 4983230072969 + 3 ^ 40 * 18855 * 2
def baseEnd_18855 : Nat := 4302967884723983744797

theorem tailTrace_18855 : CollatzResearch.WordTrace tailWord_18855 prefixEnd_18855 4302967884723983744797 := by
  unfold tailWord_18855
  simp only [CollatzResearch.WordTrace]
  refine ⟨687698346699030022738019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 458465564466020015158679 687698346699030022738019)
  ·
    refine ⟨1031547520048545034107029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687698346699030022738019 1031547520048545034107029)
    ·
      refine ⟨48353790002275548473767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1031547520048545034107029 48353790002275548473767)
      ·
        refine ⟨72530685003413322710651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48353790002275548473767 72530685003413322710651)
        ·
          refine ⟨108796027505119984065977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72530685003413322710651 108796027505119984065977)
          ·
            refine ⟨81597020628839988049483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108796027505119984065977 81597020628839988049483)
            ·
              refine ⟨122395530943259982074225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81597020628839988049483 122395530943259982074225)
              ·
                refine ⟨91796648207444986555669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122395530943259982074225 91796648207444986555669)
                ·
                  refine ⟨4302967884723983744797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91796648207444986555669 4302967884723983744797)
                  ·
                    rfl

theorem cell21_18855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_18855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18855 prefixEnd_18855 := by exact prefixLift 18855
  have htrace : WordTrace (prefixWord ++ tailWord_18855) baseStart_18855 baseEnd_18855 := by
    simpa [prefixWord, tailWord_18855, baseEnd_18855] using wordTrace_append hprefix tailTrace_18855
  have hstable : (prefixWord ++ tailWord_18855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18855).length < 2 ^ (prefixWord ++ tailWord_18855).sum := by decide
  have hdescent : baseEnd_18855 < baseStart_18855 := by decide
  rcases family_descends (prefixWord ++ tailWord_18855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18931 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_18931 : Nat := 118140960795 + 18931 * 2 ^ 59
def prefixEnd_18931 : Nat := 4983230072969 + 3 ^ 40 * 18931 * 2
def baseEnd_18931 : Nat := 4320312120164740477975

theorem tailTrace_18931 : CollatzResearch.WordTrace tailWord_18931 prefixEnd_18931 4320312120164740477975 := by
  unfold tailWord_18931
  simp only [CollatzResearch.WordTrace]
  refine ⟨690470294423695002504647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460313529615796668336431 690470294423695002504647)
  ·
    refine ⟨1035705441635542503756971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 690470294423695002504647 1035705441635542503756971)
    ·
      refine ⟨1553558162453313755635457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035705441635542503756971 1553558162453313755635457)
      ·
        refine ⟨1165168621839985316726593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1553558162453313755635457 1165168621839985316726593)
        ·
          refine ⟨873876466379988987544945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165168621839985316726593 873876466379988987544945)
          ·
            refine ⟨655407349784991740658709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873876466379988987544945 655407349784991740658709)
            ·
              refine ⟨30722219521171487843377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 655407349784991740658709 30722219521171487843377)
              ·
                refine ⟨23041664640878615882533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30722219521171487843377 23041664640878615882533)
                ·
                  refine ⟨4320312120164740477975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23041664640878615882533 4320312120164740477975)
                  ·
                    rfl

theorem cell21_18931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_18931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18931 prefixEnd_18931 := by exact prefixLift 18931
  have htrace : WordTrace (prefixWord ++ tailWord_18931) baseStart_18931 baseEnd_18931 := by
    simpa [prefixWord, tailWord_18931, baseEnd_18931] using wordTrace_append hprefix tailTrace_18931
  have hstable : (prefixWord ++ tailWord_18931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18931).length < 2 ^ (prefixWord ++ tailWord_18931).sum := by decide
  have hdescent : baseEnd_18931 < baseStart_18931 := by decide
  rcases family_descends (prefixWord ++ tailWord_18931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18934 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_18934 : Nat := 118140960795 + 18934 * 2 ^ 59
def prefixEnd_18934 : Nat := 4983230072969 + 3 ^ 40 * 18934 * 2
def baseEnd_18934 : Nat := 4320996761037401927969

theorem tailTrace_18934 : CollatzResearch.WordTrace tailWord_18934 prefixEnd_18934 4320996761037401927969 := by
  unfold tailWord_18934
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161232088301657178991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 460386475608551009909237 43161232088301657178991)
  ·
    refine ⟨64741848132452485768487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43161232088301657178991 64741848132452485768487)
    ·
      refine ⟨97112772198678728652731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64741848132452485768487 97112772198678728652731)
      ·
        refine ⟨145669158298018092979097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97112772198678728652731 145669158298018092979097)
        ·
          refine ⟨109251868723513569734323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145669158298018092979097 109251868723513569734323)
          ·
            refine ⟨163877803085270354601485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109251868723513569734323 163877803085270354601485)
            ·
              refine ⟨61454176156976382975557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163877803085270354601485 61454176156976382975557)
              ·
                refine ⟨11522658029433071807917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61454176156976382975557 11522658029433071807917)
                ·
                  refine ⟨4320996761037401927969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11522658029433071807917 4320996761037401927969)
                  ·
                    rfl

theorem cell21_18934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_18934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18934 prefixEnd_18934 := by exact prefixLift 18934
  have htrace : WordTrace (prefixWord ++ tailWord_18934) baseStart_18934 baseEnd_18934 := by
    simpa [prefixWord, tailWord_18934, baseEnd_18934] using wordTrace_append hprefix tailTrace_18934
  have hstable : (prefixWord ++ tailWord_18934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18934).length < 2 ^ (prefixWord ++ tailWord_18934).sum := by decide
  have hdescent : baseEnd_18934 < baseStart_18934 := by decide
  rcases family_descends (prefixWord ++ tailWord_18934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18948 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_18948 : Nat := 118140960795 + 18948 * 2 ^ 59
def prefixEnd_18948 : Nat := 4983230072969 + 3 ^ 40 * 18948 * 2
def baseEnd_18948 : Nat := 4324191751776488694607

theorem tailTrace_18948 : CollatzResearch.WordTrace tailWord_18948 prefixEnd_18948 4324191751776488694607 := by
  unfold tailWord_18948
  simp only [CollatzResearch.WordTrace]
  refine ⟨345545167681053452936749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 460726890241404603915665 345545167681053452936749)
  ·
    refine ⟨129579437880395044851281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 345545167681053452936749 129579437880395044851281)
    ·
      refine ⟨97184578410296283638461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129579437880395044851281 97184578410296283638461)
      ·
        refine ⟨36444216903861106364423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97184578410296283638461 36444216903861106364423)
        ·
          refine ⟨54666325355791659546635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36444216903861106364423 54666325355791659546635)
          ·
            refine ⟨81999488033687489319953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54666325355791659546635 81999488033687489319953)
            ·
              refine ⟨61499616025265616989965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81999488033687489319953 61499616025265616989965)
              ·
                refine ⟨23062356009474606371237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61499616025265616989965 23062356009474606371237)
                ·
                  refine ⟨4324191751776488694607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23062356009474606371237 4324191751776488694607)
                  ·
                    rfl

theorem cell21_18948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_18948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18948 prefixEnd_18948 := by exact prefixLift 18948
  have htrace : WordTrace (prefixWord ++ tailWord_18948) baseStart_18948 baseEnd_18948 := by
    simpa [prefixWord, tailWord_18948, baseEnd_18948] using wordTrace_append hprefix tailTrace_18948
  have hstable : (prefixWord ++ tailWord_18948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18948).length < 2 ^ (prefixWord ++ tailWord_18948).sum := by decide
  have hdescent : baseEnd_18948 < baseStart_18948 := by decide
  rcases family_descends (prefixWord ++ tailWord_18948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18959 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_18959 : Nat := 118140960795 + 18959 * 2 ^ 59
def prefixEnd_18959 : Nat := 4983230072969 + 3 ^ 40 * 18959 * 2
def baseEnd_18959 : Nat := 4326702101642914011251

theorem tailTrace_18959 : CollatzResearch.WordTrace tailWord_18959 prefixEnd_18959 4326702101642914011251 := by
  unfold tailWord_18959
  simp only [CollatzResearch.WordTrace]
  refine ⟨691491538322255784523931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460994358881503856349287 691491538322255784523931)
  ·
    refine ⟨1037237307483383676785897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691491538322255784523931 1037237307483383676785897)
    ·
      refine ⟨777927980612537757589423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037237307483383676785897 777927980612537757589423)
      ·
        refine ⟨1166891970918806636384135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777927980612537757589423 1166891970918806636384135)
        ·
          refine ⟨1750337956378209954576203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166891970918806636384135 1750337956378209954576203)
          ·
            refine ⟨2625506934567314931864305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750337956378209954576203 2625506934567314931864305)
            ·
              refine ⟨1969130200925486198898229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625506934567314931864305 1969130200925486198898229)
              ·
                refine ⟨184605956336764331146709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1969130200925486198898229 184605956336764331146709)
                ·
                  refine ⟨4326702101642914011251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184605956336764331146709 4326702101642914011251)
                  ·
                    rfl

theorem cell21_18959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_18959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18959 prefixEnd_18959 := by exact prefixLift 18959
  have htrace : WordTrace (prefixWord ++ tailWord_18959) baseStart_18959 baseEnd_18959 := by
    simpa [prefixWord, tailWord_18959, baseEnd_18959] using wordTrace_append hprefix tailTrace_18959
  have hstable : (prefixWord ++ tailWord_18959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18959).length < 2 ^ (prefixWord ++ tailWord_18959).sum := by decide
  have hdescent : baseEnd_18959 < baseStart_18959 := by decide
  rcases family_descends (prefixWord ++ tailWord_18959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18993 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 3]
def baseStart_18993 : Nat := 118140960795 + 18993 * 2 ^ 59
def prefixEnd_18993 : Nat := 4983230072969 + 3 ^ 40 * 18993 * 2
def baseEnd_18993 : Nat := 4334461364866410444515

theorem tailTrace_18993 : CollatzResearch.WordTrace tailWord_18993 prefixEnd_18993 4334461364866410444515 := by
  unfold tailWord_18993
  simp only [CollatzResearch.WordTrace]
  refine ⟨692731620199079591261633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 461821080132719727507755 692731620199079591261633)
  ·
    refine ⟨519548715149309693446225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 692731620199079591261633 519548715149309693446225)
    ·
      refine ⟨389661536361982270084669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 519548715149309693446225 389661536361982270084669)
      ·
        refine ⟨146123076135743351281751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389661536361982270084669 146123076135743351281751)
        ·
          refine ⟨219184614203615026922627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146123076135743351281751 219184614203615026922627)
          ·
            refine ⟨328776921305422540383941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219184614203615026922627 328776921305422540383941)
            ·
              refine ⟨61645672744766726321989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328776921305422540383941 61645672744766726321989)
              ·
                refine ⟨11558563639643761185373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61645672744766726321989 11558563639643761185373)
                ·
                  refine ⟨4334461364866410444515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11558563639643761185373 4334461364866410444515)
                  ·
                    rfl

theorem cell21_18993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_18993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_18993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_18993 prefixEnd_18993 := by exact prefixLift 18993
  have htrace : WordTrace (prefixWord ++ tailWord_18993) baseStart_18993 baseEnd_18993 := by
    simpa [prefixWord, tailWord_18993, baseEnd_18993] using wordTrace_append hprefix tailTrace_18993
  have hstable : (prefixWord ++ tailWord_18993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18993).length < 2 ^ (prefixWord ++ tailWord_18993).sum := by decide
  have hdescent : baseEnd_18993 < baseStart_18993 := by decide
  rcases family_descends (prefixWord ++ tailWord_18993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19052 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_19052 : Nat := 118140960795 + 19052 * 2 ^ 59
def prefixEnd_19052 : Nat := 4983230072969 + 3 ^ 40 * 19052 * 2
def baseEnd_19052 : Nat := 4347925968695418961061

theorem tailTrace_19052 : CollatzResearch.WordTrace tailWord_19052 prefixEnd_19052 4347925968695418961061 := by
  unfold tailWord_19052
  simp only [CollatzResearch.WordTrace]
  refine ⟨347441763492666333829705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 463255684656888445106273 347441763492666333829705)
  ·
    refine ⟨260581322619499750372279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 347441763492666333829705 260581322619499750372279)
    ·
      refine ⟨390871983929249625558419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260581322619499750372279 390871983929249625558419)
      ·
        refine ⟨586307975893874438337629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390871983929249625558419 586307975893874438337629)
        ·
          refine ⟨219865490960202914376611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 586307975893874438337629 219865490960202914376611)
          ·
            refine ⟨329798236440304371564917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219865490960202914376611 329798236440304371564917)
            ·
              refine ⟨30918584666278534834211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329798236440304371564917 30918584666278534834211)
              ·
                refine ⟨46377876999417802251317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30918584666278534834211 46377876999417802251317)
                ·
                  refine ⟨4347925968695418961061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46377876999417802251317 4347925968695418961061)
                  ·
                    rfl

theorem cell21_19052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_19052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19052 prefixEnd_19052 := by exact prefixLift 19052
  have htrace : WordTrace (prefixWord ++ tailWord_19052) baseStart_19052 baseEnd_19052 := by
    simpa [prefixWord, tailWord_19052, baseEnd_19052] using wordTrace_append hprefix tailTrace_19052
  have hstable : (prefixWord ++ tailWord_19052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19052).length < 2 ^ (prefixWord ++ tailWord_19052).sum := by decide
  have hdescent : baseEnd_19052 < baseStart_19052 := by decide
  rcases family_descends (prefixWord ++ tailWord_19052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19058 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_19058 : Nat := 118140960795 + 19058 * 2 ^ 59
def prefixEnd_19058 : Nat := 4983230072969 + 3 ^ 40 * 19058 * 2
def baseEnd_19058 : Nat := 4349295250440741861049

theorem tailTrace_19058 : CollatzResearch.WordTrace tailWord_19058 prefixEnd_19058 4349295250440741861049 := by
  unfold tailWord_19058
  simp only [CollatzResearch.WordTrace]
  refine ⟨173775591240898923094457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 463401576642397128251885 173775591240898923094457)
  ·
    refine ⟨130331693430674192320843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173775591240898923094457 130331693430674192320843)
    ·
      refine ⟨195497540146011288481265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130331693430674192320843 195497540146011288481265)
      ·
        refine ⟨146623155109508466360949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195497540146011288481265 146623155109508466360949)
        ·
          refine ⟨13745920791516418721339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146623155109508466360949 13745920791516418721339)
          ·
            refine ⟨20618881187274628082009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13745920791516418721339 20618881187274628082009)
            ·
              refine ⟨15464160890455971061507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20618881187274628082009 15464160890455971061507)
              ·
                refine ⟨23196241335683956592261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15464160890455971061507 23196241335683956592261)
                ·
                  refine ⟨4349295250440741861049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23196241335683956592261 4349295250440741861049)
                  ·
                    rfl

theorem cell21_19058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_19058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19058 prefixEnd_19058 := by exact prefixLift 19058
  have htrace : WordTrace (prefixWord ++ tailWord_19058) baseStart_19058 baseEnd_19058 := by
    simpa [prefixWord, tailWord_19058, baseEnd_19058] using wordTrace_append hprefix tailTrace_19058
  have hstable : (prefixWord ++ tailWord_19058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19058).length < 2 ^ (prefixWord ++ tailWord_19058).sum := by decide
  have hdescent : baseEnd_19058 < baseStart_19058 := by decide
  rcases family_descends (prefixWord ++ tailWord_19058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19100 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_19100 : Nat := 118140960795 + 19100 * 2 ^ 59
def prefixEnd_19100 : Nat := 4983230072969 + 3 ^ 40 * 19100 * 2
def baseEnd_19100 : Nat := 4358880222658002160963

theorem tailTrace_19100 : CollatzResearch.WordTrace tailWord_19100 prefixEnd_19100 4358880222658002160963 := by
  unfold tailWord_19100
  simp only [CollatzResearch.WordTrace]
  refine ⟨348317115405718432703377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 464422820540957910271169 348317115405718432703377)
  ·
    refine ⟨261237836554288824527533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 348317115405718432703377 261237836554288824527533)
    ·
      refine ⟨97964188707858309197825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261237836554288824527533 97964188707858309197825)
      ·
        refine ⟨73473141530893731898369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97964188707858309197825 73473141530893731898369)
        ·
          refine ⟨55104856148170298923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73473141530893731898369 55104856148170298923777)
          ·
            refine ⟨41328642111127724192833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55104856148170298923777 41328642111127724192833)
            ·
              refine ⟨30996481583345793144625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41328642111127724192833 30996481583345793144625)
              ·
                refine ⟨23247361187509344858469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30996481583345793144625 23247361187509344858469)
                ·
                  refine ⟨4358880222658002160963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23247361187509344858469 4358880222658002160963)
                  ·
                    rfl

theorem cell21_19100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_19100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19100 prefixEnd_19100 := by exact prefixLift 19100
  have htrace : WordTrace (prefixWord ++ tailWord_19100) baseStart_19100 baseEnd_19100 := by
    simpa [prefixWord, tailWord_19100, baseEnd_19100] using wordTrace_append hprefix tailTrace_19100
  have hstable : (prefixWord ++ tailWord_19100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19100).length < 2 ^ (prefixWord ++ tailWord_19100).sum := by decide
  have hdescent : baseEnd_19100 < baseStart_19100 := by decide
  rcases family_descends (prefixWord ++ tailWord_19100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19159 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_19159 : Nat := 118140960795 + 19159 * 2 ^ 59
def prefixEnd_19159 : Nat := 4983230072969 + 3 ^ 40 * 19159 * 2
def baseEnd_19159 : Nat := 4372344826487010677509

theorem tailTrace_19159 : CollatzResearch.WordTrace tailWord_19159 prefixEnd_19159 4372344826487010677509 := by
  unfold tailWord_19159
  simp only [CollatzResearch.WordTrace]
  refine ⟨698786137597689941804531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 465857425065126627869687 698786137597689941804531)
  ·
    refine ⟨1048179206396534912706797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698786137597689941804531 1048179206396534912706797)
    ·
      refine ⟨393067202398700592265049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1048179206396534912706797 393067202398700592265049)
      ·
        refine ⟨294800401799025444198787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393067202398700592265049 294800401799025444198787)
        ·
          refine ⟨442200602698538166298181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294800401799025444198787 442200602698538166298181)
          ·
            refine ⟨82912613005975906180909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 442200602698538166298181 82912613005975906180909)
            ·
              refine ⟨31092229877240964817841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82912613005975906180909 31092229877240964817841)
              ·
                refine ⟨23319172407930723613381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31092229877240964817841 23319172407930723613381)
                ·
                  refine ⟨4372344826487010677509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23319172407930723613381 4372344826487010677509)
                  ·
                    rfl

theorem cell21_19159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_19159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19159 prefixEnd_19159 := by exact prefixLift 19159
  have htrace : WordTrace (prefixWord ++ tailWord_19159) baseStart_19159 baseEnd_19159 := by
    simpa [prefixWord, tailWord_19159, baseEnd_19159] using wordTrace_append hprefix tailTrace_19159
  have hstable : (prefixWord ++ tailWord_19159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19159).length < 2 ^ (prefixWord ++ tailWord_19159).sum := by decide
  have hdescent : baseEnd_19159 < baseStart_19159 := by decide
  rcases family_descends (prefixWord ++ tailWord_19159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19339 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_19339 : Nat := 118140960795 + 19339 * 2 ^ 59
def prefixEnd_19339 : Nat := 4983230072969 + 3 ^ 40 * 19339 * 2
def baseEnd_19339 : Nat := 4413423278846697677141

theorem tailTrace_19339 : CollatzResearch.WordTrace tailWord_19339 prefixEnd_19339 4413423278846697677141 := by
  unfold tailWord_19339
  simp only [CollatzResearch.WordTrace]
  refine ⟨705351276945580683357071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 470234184630387122238047 705351276945580683357071)
  ·
    refine ⟨1058026915418371025035607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705351276945580683357071 1058026915418371025035607)
    ·
      refine ⟨1587040373127556537553411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058026915418371025035607 1587040373127556537553411)
      ·
        refine ⟨2380560559691334806330117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587040373127556537553411 2380560559691334806330117)
        ·
          refine ⟨446355104942125276186897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2380560559691334806330117 446355104942125276186897)
          ·
            refine ⟨334766328706593957140173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446355104942125276186897 334766328706593957140173)
            ·
              refine ⟨125537373264972733927565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334766328706593957140173 125537373264972733927565)
              ·
                refine ⟨47076514974364775222837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125537373264972733927565 47076514974364775222837)
                ·
                  refine ⟨4413423278846697677141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47076514974364775222837 4413423278846697677141)
                  ·
                    rfl

theorem cell21_19339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_19339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19339 prefixEnd_19339 := by exact prefixLift 19339
  have htrace : WordTrace (prefixWord ++ tailWord_19339) baseStart_19339 baseEnd_19339 := by
    simpa [prefixWord, tailWord_19339, baseEnd_19339] using wordTrace_append hprefix tailTrace_19339
  have hstable : (prefixWord ++ tailWord_19339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19339).length < 2 ^ (prefixWord ++ tailWord_19339).sum := by decide
  have hdescent : baseEnd_19339 < baseStart_19339 := by decide
  rcases family_descends (prefixWord ++ tailWord_19339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19384 : List Nat := [2, 1, 2, 1, 2, 4, 9]
def baseStart_19384 : Nat := 118140960795 + 19384 * 2 ^ 59
def prefixEnd_19384 : Nat := 4983230072969 + 3 ^ 40 * 19384 * 2
def baseEnd_19384 : Nat := 491521432437402158561

theorem tailTrace_19384 : CollatzResearch.WordTrace tailWord_19384 prefixEnd_19384 491521432437402158561 := by
  unfold tailWord_19384
  simp only [CollatzResearch.WordTrace]
  refine ⟨353496280891276684372603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 471328374521702245830137 353496280891276684372603)
  ·
    refine ⟨530244421336915026558905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353496280891276684372603 530244421336915026558905)
    ·
      refine ⟨397683316002686269919179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530244421336915026558905 397683316002686269919179)
      ·
        refine ⟨596524974004029404878769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397683316002686269919179 596524974004029404878769)
        ·
          refine ⟨447393730503022053659077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596524974004029404878769 447393730503022053659077)
          ·
            refine ⟨83886324469316635061077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 447393730503022053659077 83886324469316635061077)
            ·
              refine ⟨491521432437402158561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 83886324469316635061077 491521432437402158561)
              ·
                rfl

theorem cell21_19384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 9].length) (baseStart_19384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19384 prefixEnd_19384 := by exact prefixLift 19384
  have htrace : WordTrace (prefixWord ++ tailWord_19384) baseStart_19384 baseEnd_19384 := by
    simpa [prefixWord, tailWord_19384, baseEnd_19384] using wordTrace_append hprefix tailTrace_19384
  have hstable : (prefixWord ++ tailWord_19384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19384).length < 2 ^ (prefixWord ++ tailWord_19384).sum := by decide
  have hdescent : baseEnd_19384 < baseStart_19384 := by decide
  rcases family_descends (prefixWord ++ tailWord_19384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19390 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_19390 : Nat := 118140960795 + 19390 * 2 ^ 59
def prefixEnd_19390 : Nat := 4983230072969 + 3 ^ 40 * 19390 * 2
def baseEnd_19390 : Nat := 4425062173681942327037

theorem tailTrace_19390 : CollatzResearch.WordTrace tailWord_19390 prefixEnd_19390 4425062173681942327037 := by
  unfold tailWord_19390
  simp only [CollatzResearch.WordTrace]
  refine ⟨88401424970102049182953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 471474266507210928975749 88401424970102049182953)
  ·
    refine ⟨66301068727576536887215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88401424970102049182953 66301068727576536887215)
    ·
      refine ⟨99451603091364805330823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66301068727576536887215 99451603091364805330823)
      ·
        refine ⟨149177404637047207996235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99451603091364805330823 149177404637047207996235)
        ·
          refine ⟨223766106955570811994353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149177404637047207996235 223766106955570811994353)
          ·
            refine ⟨167824580216678108995765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223766106955570811994353 167824580216678108995765)
            ·
              refine ⟨15733554395313572718353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167824580216678108995765 15733554395313572718353)
              ·
                refine ⟨11800165796485179538765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15733554395313572718353 11800165796485179538765)
                ·
                  refine ⟨4425062173681942327037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11800165796485179538765 4425062173681942327037)
                  ·
                    rfl

theorem cell21_19390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_19390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19390 prefixEnd_19390 := by exact prefixLift 19390
  have htrace : WordTrace (prefixWord ++ tailWord_19390) baseStart_19390 baseEnd_19390 := by
    simpa [prefixWord, tailWord_19390, baseEnd_19390] using wordTrace_append hprefix tailTrace_19390
  have hstable : (prefixWord ++ tailWord_19390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19390).length < 2 ^ (prefixWord ++ tailWord_19390).sum := by decide
  have hdescent : baseEnd_19390 < baseStart_19390 := by decide
  rcases family_descends (prefixWord ++ tailWord_19390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19612 : List Nat := [2, 2, 3, 2, 1, 11]
def baseStart_19612 : Nat := 118140960795 + 19612 * 2 ^ 59
def prefixEnd_19612 : Nat := 4983230072969 + 3 ^ 40 * 19612 * 2
def baseEnd_19612 : Nat := 165767614750329245429

theorem tailTrace_19612 : CollatzResearch.WordTrace tailWord_19612 prefixEnd_19612 165767614750329245429 := by
  unfold tailWord_19612
  simp only [CollatzResearch.WordTrace]
  refine ⟨357654202478274154022545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 476872269971032205363393 357654202478274154022545)
  ·
    refine ⟨268240651858705615516909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 357654202478274154022545 268240651858705615516909)
    ·
      refine ⟨100590244447014605818841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268240651858705615516909 100590244447014605818841)
      ·
        refine ⟨75442683335260954364131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100590244447014605818841 75442683335260954364131)
        ·
          refine ⟨113164025002891431546197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75442683335260954364131 113164025002891431546197)
          ·
            refine ⟨165767614750329245429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 113164025002891431546197 165767614750329245429)
            ·
              rfl

theorem cell21_19612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 11].length) (baseStart_19612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19612 prefixEnd_19612 := by exact prefixLift 19612
  have htrace : WordTrace (prefixWord ++ tailWord_19612) baseStart_19612 baseEnd_19612 := by
    simpa [prefixWord, tailWord_19612, baseEnd_19612] using wordTrace_append hprefix tailTrace_19612
  have hstable : (prefixWord ++ tailWord_19612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19612).length < 2 ^ (prefixWord ++ tailWord_19612).sum := by decide
  have hdescent : baseEnd_19612 < baseStart_19612 := by decide
  rcases family_descends (prefixWord ++ tailWord_19612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19618 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_19618 : Nat := 118140960795 + 19618 * 2 ^ 59
def prefixEnd_19618 : Nat := 4983230072969 + 3 ^ 40 * 19618 * 2
def baseEnd_19618 : Nat := 4477094880004212526571

theorem tailTrace_19618 : CollatzResearch.WordTrace tailWord_19618 prefixEnd_19618 4477094880004212526571 := by
  unfold tailWord_19618
  simp only [CollatzResearch.WordTrace]
  refine ⟨178881810733702833190877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 477018161956540888509005 178881810733702833190877)
  ·
    refine ⟨67080679025138562446579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178881810733702833190877 67080679025138562446579)
    ·
      refine ⟨100621018537707843669869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67080679025138562446579 100621018537707843669869)
      ·
        refine ⟨37732881951640441376201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100621018537707843669869 37732881951640441376201)
        ·
          refine ⟨28299661463730331032151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37732881951640441376201 28299661463730331032151)
          ·
            refine ⟨42449492195595496548227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28299661463730331032151 42449492195595496548227)
            ·
              refine ⟨63674238293393244822341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42449492195595496548227 63674238293393244822341)
              ·
                refine ⟨11938919680011233404189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63674238293393244822341 11938919680011233404189)
                ·
                  refine ⟨4477094880004212526571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11938919680011233404189 4477094880004212526571)
                  ·
                    rfl

theorem cell21_19618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_19618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19618 prefixEnd_19618 := by exact prefixLift 19618
  have htrace : WordTrace (prefixWord ++ tailWord_19618) baseStart_19618 baseEnd_19618 := by
    simpa [prefixWord, tailWord_19618, baseEnd_19618] using wordTrace_append hprefix tailTrace_19618
  have hstable : (prefixWord ++ tailWord_19618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19618).length < 2 ^ (prefixWord ++ tailWord_19618).sum := by decide
  have hdescent : baseEnd_19618 < baseStart_19618 := by decide
  rcases family_descends (prefixWord ++ tailWord_19618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19646 : List Nat := [4, 2, 1, 1, 3, 2, 3, 5]
def baseStart_19646 : Nat := 118140960795 + 19646 * 2 ^ 59
def prefixEnd_19646 : Nat := 4983230072969 + 3 ^ 40 * 19646 * 2
def baseEnd_19646 : Nat := 1494494953827462019949

theorem tailTrace_19646 : CollatzResearch.WordTrace tailWord_19646 prefixEnd_19646 1494494953827462019949 := by
  unfold tailWord_19646
  simp only [CollatzResearch.WordTrace]
  refine ⟨89568560854171514347849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 477698991222248076521861 89568560854171514347849)
  ·
    refine ⟨67176420640628635760887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89568560854171514347849 67176420640628635760887)
    ·
      refine ⟨100764630960942953641331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67176420640628635760887 100764630960942953641331)
      ·
        refine ⟨151146946441414430461997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100764630960942953641331 151146946441414430461997)
        ·
          refine ⟨56680104915530411423249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151146946441414430461997 56680104915530411423249)
          ·
            refine ⟨42510078686647808567437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56680104915530411423249 42510078686647808567437)
            ·
              refine ⟨15941279507492928212789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42510078686647808567437 15941279507492928212789)
              ·
                refine ⟨1494494953827462019949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15941279507492928212789 1494494953827462019949)
                ·
                  rfl

theorem cell21_19646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_19646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19646 prefixEnd_19646 := by exact prefixLift 19646
  have htrace : WordTrace (prefixWord ++ tailWord_19646) baseStart_19646 baseEnd_19646 := by
    simpa [prefixWord, tailWord_19646, baseEnd_19646] using wordTrace_append hprefix tailTrace_19646
  have hstable : (prefixWord ++ tailWord_19646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19646).length < 2 ^ (prefixWord ++ tailWord_19646).sum := by decide
  have hdescent : baseEnd_19646 < baseStart_19646 := by decide
  rcases family_descends (prefixWord ++ tailWord_19646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19677 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_19677 : Nat := 118140960795 + 19677 * 2 ^ 59
def prefixEnd_19677 : Nat := 4983230072969 + 3 ^ 40 * 19677 * 2
def baseEnd_19677 : Nat := 4490559483833221043117

theorem tailTrace_19677 : CollatzResearch.WordTrace tailWord_19677 prefixEnd_19677 4490559483833221043117 := by
  unfold tailWord_19677
  simp only [CollatzResearch.WordTrace]
  refine ⟨717679149721064409161285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 478452766480709606107523 717679149721064409161285)
  ·
    refine ⟨134564840572699576717741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 717679149721064409161285 134564840572699576717741)
    ·
      refine ⟨50461815214762341269153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134564840572699576717741 50461815214762341269153)
      ·
        refine ⟨37846361411071755951865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50461815214762341269153 37846361411071755951865)
        ·
          refine ⟨28384771058303816963899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37846361411071755951865 28384771058303816963899)
          ·
            refine ⟨42577156587455725445849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28384771058303816963899 42577156587455725445849)
            ·
              refine ⟨31932867440591794084387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42577156587455725445849 31932867440591794084387)
              ·
                refine ⟨47899301160887691126581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31932867440591794084387 47899301160887691126581)
                ·
                  refine ⟨4490559483833221043117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47899301160887691126581 4490559483833221043117)
                  ·
                    rfl

theorem cell21_19677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_19677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19677 prefixEnd_19677 := by exact prefixLift 19677
  have htrace : WordTrace (prefixWord ++ tailWord_19677) baseStart_19677 baseEnd_19677 := by
    simpa [prefixWord, tailWord_19677, baseEnd_19677] using wordTrace_append hprefix tailTrace_19677
  have hstable : (prefixWord ++ tailWord_19677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19677).length < 2 ^ (prefixWord ++ tailWord_19677).sum := by decide
  have hdescent : baseEnd_19677 < baseStart_19677 := by decide
  rcases family_descends (prefixWord ++ tailWord_19677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19688 : List Nat := [2, 1, 4, 1, 2, 1, 2, 8]
def baseStart_19688 : Nat := 118140960795 + 19688 * 2 ^ 59
def prefixEnd_19688 : Nat := 4983230072969 + 3 ^ 40 * 19688 * 2
def baseEnd_19688 : Nat := 1497689944566548786587

theorem tailTrace_19688 : CollatzResearch.WordTrace tailWord_19688 prefixEnd_19688 1497689944566548786587 := by
  unfold tailWord_19688
  simp only [CollatzResearch.WordTrace]
  refine ⟨359040176340606643905859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 478720235120808858541145 359040176340606643905859)
  ·
    refine ⟨538560264510909965858789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359040176340606643905859 538560264510909965858789)
    ·
      refine ⟨100980049595795618598523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 538560264510909965858789 100980049595795618598523)
      ·
        refine ⟨151470074393693427897785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100980049595795618598523 151470074393693427897785)
        ·
          refine ⟨113602555795270070923339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151470074393693427897785 113602555795270070923339)
          ·
            refine ⟨170403833692905106385009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113602555795270070923339 170403833692905106385009)
            ·
              refine ⟨127802875269678829788757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170403833692905106385009 127802875269678829788757)
              ·
                refine ⟨1497689944566548786587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 127802875269678829788757 1497689944566548786587)
                ·
                  rfl

theorem cell21_19688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_19688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19688 prefixEnd_19688 := by exact prefixLift 19688
  have htrace : WordTrace (prefixWord ++ tailWord_19688) baseStart_19688 baseEnd_19688 := by
    simpa [prefixWord, tailWord_19688, baseEnd_19688] using wordTrace_append hprefix tailTrace_19688
  have hstable : (prefixWord ++ tailWord_19688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19688).length < 2 ^ (prefixWord ++ tailWord_19688).sum := by decide
  have hdescent : baseEnd_19688 < baseStart_19688 := by decide
  rcases family_descends (prefixWord ++ tailWord_19688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19691 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 4]
def baseStart_19691 : Nat := 118140960795 + 19691 * 2 ^ 59
def prefixEnd_19691 : Nat := 4983230072969 + 3 ^ 40 * 19691 * 2
def baseEnd_19691 : Nat := 4493754474572307809755

theorem tailTrace_19691 : CollatzResearch.WordTrace tailWord_19691 prefixEnd_19691 4493754474572307809755 := by
  unfold tailWord_19691
  simp only [CollatzResearch.WordTrace]
  refine ⟨718189771670344800170927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 478793181113563200113951 718189771670344800170927)
  ·
    refine ⟨1077284657505517200256391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 718189771670344800170927 1077284657505517200256391)
    ·
      refine ⟨1615926986258275800384587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077284657505517200256391 1615926986258275800384587)
      ·
        refine ⟨2423890479387413700576881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615926986258275800384587 2423890479387413700576881)
        ·
          refine ⟨1817917859540560275432661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423890479387413700576881 1817917859540560275432661)
          ·
            refine ⟨42607449832981881455453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1817917859540560275432661 42607449832981881455453)
            ·
              refine ⟨15977793687368205545795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42607449832981881455453 15977793687368205545795)
              ·
                refine ⟨23966690531052308318693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15977793687368205545795 23966690531052308318693)
                ·
                  refine ⟨4493754474572307809755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23966690531052308318693 4493754474572307809755)
                  ·
                    rfl

theorem cell21_19691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_19691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19691 prefixEnd_19691 := by exact prefixLift 19691
  have htrace : WordTrace (prefixWord ++ tailWord_19691) baseStart_19691 baseEnd_19691 := by
    simpa [prefixWord, tailWord_19691, baseEnd_19691] using wordTrace_append hprefix tailTrace_19691
  have hstable : (prefixWord ++ tailWord_19691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19691).length < 2 ^ (prefixWord ++ tailWord_19691).sum := by decide
  have hdescent : baseEnd_19691 < baseStart_19691 := by decide
  rcases family_descends (prefixWord ++ tailWord_19691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19736 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_19736 : Nat := 118140960795 + 19736 * 2 ^ 59
def prefixEnd_19736 : Nat := 4983230072969 + 3 ^ 40 * 19736 * 2
def baseEnd_19736 : Nat := 4504024087662229559663

theorem tailTrace_19736 : CollatzResearch.WordTrace tailWord_19736 prefixEnd_19736 4504024087662229559663 := by
  unfold tailWord_19736
  simp only [CollatzResearch.WordTrace]
  refine ⟨359915528253658742779531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 479887371004878323706041 359915528253658742779531)
  ·
    refine ⟨539873292380488114169297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359915528253658742779531 539873292380488114169297)
    ·
      refine ⟨404904969285366085626973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 539873292380488114169297 404904969285366085626973)
      ·
        refine ⟨151839363482012282110115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404904969285366085626973 151839363482012282110115)
        ·
          refine ⟨227759045223018423165173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151839363482012282110115 227759045223018423165173)
          ·
            refine ⟨21352410489657977171735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227759045223018423165173 21352410489657977171735)
            ·
              refine ⟨32028615734486965757603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21352410489657977171735 32028615734486965757603)
              ·
                refine ⟨48042923601730448636405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32028615734486965757603 48042923601730448636405)
                ·
                  refine ⟨4504024087662229559663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48042923601730448636405 4504024087662229559663)
                  ·
                    rfl

theorem cell21_19736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_19736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19736 prefixEnd_19736 := by exact prefixLift 19736
  have htrace : WordTrace (prefixWord ++ tailWord_19736) baseStart_19736 baseEnd_19736 := by
    simpa [prefixWord, tailWord_19736, baseEnd_19736] using wordTrace_append hprefix tailTrace_19736
  have hstable : (prefixWord ++ tailWord_19736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19736).length < 2 ^ (prefixWord ++ tailWord_19736).sum := by decide
  have hdescent : baseEnd_19736 < baseStart_19736 := by decide
  rcases family_descends (prefixWord ++ tailWord_19736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19742 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_19742 : Nat := 118140960795 + 19742 * 2 ^ 59
def prefixEnd_19742 : Nat := 4983230072969 + 3 ^ 40 * 19742 * 2
def baseEnd_19742 : Nat := 4505393369407552459651

theorem tailTrace_19742 : CollatzResearch.WordTrace tailWord_19742 prefixEnd_19742 4505393369407552459651 := by
  unfold tailWord_19742
  simp only [CollatzResearch.WordTrace]
  refine ⟨90006236810697563784685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 480033262990387006851653 90006236810697563784685)
  ·
    refine ⟨33752338804011586419257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90006236810697563784685 33752338804011586419257)
    ·
      refine ⟨25314254103008689814443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33752338804011586419257 25314254103008689814443)
      ·
        refine ⟨37971381154513034721665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25314254103008689814443 37971381154513034721665)
        ·
          refine ⟨28478535865884776041249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37971381154513034721665 28478535865884776041249)
          ·
            refine ⟨21358901899413582030937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28478535865884776041249 21358901899413582030937)
            ·
              refine ⟨16019176424560186523203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21358901899413582030937 16019176424560186523203)
              ·
                refine ⟨24028764636840279784805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16019176424560186523203 24028764636840279784805)
                ·
                  refine ⟨4505393369407552459651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24028764636840279784805 4505393369407552459651)
                  ·
                    rfl

theorem cell21_19742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_19742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19742 prefixEnd_19742 := by exact prefixLift 19742
  have htrace : WordTrace (prefixWord ++ tailWord_19742) baseStart_19742 baseEnd_19742 := by
    simpa [prefixWord, tailWord_19742, baseEnd_19742] using wordTrace_append hprefix tailTrace_19742
  have hstable : (prefixWord ++ tailWord_19742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19742).length < 2 ^ (prefixWord ++ tailWord_19742).sum := by decide
  have hdescent : baseEnd_19742 < baseStart_19742 := by decide
  rcases family_descends (prefixWord ++ tailWord_19742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19843 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_19843 : Nat := 118140960795 + 19843 * 2 ^ 59
def prefixEnd_19843 : Nat := 4983230072969 + 3 ^ 40 * 19843 * 2
def baseEnd_19843 : Nat := 4528442945453821276111

theorem tailTrace_19843 : CollatzResearch.WordTrace tailWord_19843 prefixEnd_19843 4528442945453821276111 := by
  unfold tailWord_19843
  simp only [CollatzResearch.WordTrace]
  refine ⟨723733667119674759704183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 482489111413116506469455 723733667119674759704183)
  ·
    refine ⟨1085600500679512139556275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723733667119674759704183 1085600500679512139556275)
    ·
      refine ⟨1628400751019268209334413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085600500679512139556275 1628400751019268209334413)
      ·
        refine ⟨610650281632225578500405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1628400751019268209334413 610650281632225578500405)
        ·
          refine ⟨57248463903021147984413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 610650281632225578500405 57248463903021147984413)
          ·
            refine ⟨21468173963632930494155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57248463903021147984413 21468173963632930494155)
            ·
              refine ⟨32202260945449395741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21468173963632930494155 32202260945449395741233)
              ·
                refine ⟨24151695709087046805925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32202260945449395741233 24151695709087046805925)
                ·
                  refine ⟨4528442945453821276111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24151695709087046805925 4528442945453821276111)
                  ·
                    rfl

theorem cell21_19843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_19843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19843 prefixEnd_19843 := by exact prefixLift 19843
  have htrace : WordTrace (prefixWord ++ tailWord_19843) baseStart_19843 baseEnd_19843 := by
    simpa [prefixWord, tailWord_19843, baseEnd_19843] using wordTrace_append hprefix tailTrace_19843
  have hstable : (prefixWord ++ tailWord_19843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19843).length < 2 ^ (prefixWord ++ tailWord_19843).sum := by decide
  have hdescent : baseEnd_19843 < baseStart_19843 := by decide
  rcases family_descends (prefixWord ++ tailWord_19843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19860 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_19860 : Nat := 118140960795 + 19860 * 2 ^ 59
def prefixEnd_19860 : Nat := 4983230072969 + 3 ^ 40 * 19860 * 2
def baseEnd_19860 : Nat := 4532322577065569492743

theorem tailTrace_19860 : CollatzResearch.WordTrace tailWord_19860 prefixEnd_19860 4532322577065569492743 := by
  unfold tailWord_19860
  simp only [CollatzResearch.WordTrace]
  refine ⟨362176854029043331536517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 482902472038724442048689 362176854029043331536517)
  ·
    refine ⟨67908160130445624663097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 362176854029043331536517 67908160130445624663097)
    ·
      refine ⟨50931120097834218497323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67908160130445624663097 50931120097834218497323)
      ·
        refine ⟨76396680146751327745985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50931120097834218497323 76396680146751327745985)
        ·
          refine ⟨57297510110063495809489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76396680146751327745985 57297510110063495809489)
          ·
            refine ⟨42973132582547621857117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57297510110063495809489 42973132582547621857117)
            ·
              refine ⟨16114924718455358196419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42973132582547621857117 16114924718455358196419)
              ·
                refine ⟨24172387077683037294629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16114924718455358196419 24172387077683037294629)
                ·
                  refine ⟨4532322577065569492743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24172387077683037294629 4532322577065569492743)
                  ·
                    rfl

theorem cell21_19860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_19860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19860 prefixEnd_19860 := by exact prefixLift 19860
  have htrace : WordTrace (prefixWord ++ tailWord_19860) baseStart_19860 baseEnd_19860 := by
    simpa [prefixWord, tailWord_19860, baseEnd_19860] using wordTrace_append hprefix tailTrace_19860
  have hstable : (prefixWord ++ tailWord_19860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19860).length < 2 ^ (prefixWord ++ tailWord_19860).sum := by decide
  have hdescent : baseEnd_19860 < baseStart_19860 := by decide
  rcases family_descends (prefixWord ++ tailWord_19860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19871 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_19871 : Nat := 118140960795 + 19871 * 2 ^ 59
def prefixEnd_19871 : Nat := 4983230072969 + 3 ^ 40 * 19871 * 2
def baseEnd_19871 : Nat := 4534832926931994809387

theorem tailTrace_19871 : CollatzResearch.WordTrace tailWord_19871 prefixEnd_19871 4534832926931994809387 := by
  unfold tailWord_19871
  simp only [CollatzResearch.WordTrace]
  refine ⟨724754911018235541723467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 483169940678823694482311 724754911018235541723467)
  ·
    refine ⟨1087132366527353312585201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724754911018235541723467 1087132366527353312585201)
    ·
      refine ⟨815349274895514984438901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087132366527353312585201 815349274895514984438901)
      ·
        refine ⟨76438994521454529791147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 815349274895514984438901 76438994521454529791147)
        ·
          refine ⟨114658491782181794686721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76438994521454529791147 114658491782181794686721)
          ·
            refine ⟨85993868836636346015041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114658491782181794686721 85993868836636346015041)
            ·
              refine ⟨64495401627477259511281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85993868836636346015041 64495401627477259511281)
              ·
                refine ⟨48371551220607944633461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64495401627477259511281 48371551220607944633461)
                ·
                  refine ⟨4534832926931994809387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48371551220607944633461 4534832926931994809387)
                  ·
                    rfl

theorem cell21_19871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_19871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19871 prefixEnd_19871 := by exact prefixLift 19871
  have htrace : WordTrace (prefixWord ++ tailWord_19871) baseStart_19871 baseEnd_19871 := by
    simpa [prefixWord, tailWord_19871, baseEnd_19871] using wordTrace_append hprefix tailTrace_19871
  have hstable : (prefixWord ++ tailWord_19871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19871).length < 2 ^ (prefixWord ++ tailWord_19871).sum := by decide
  have hdescent : baseEnd_19871 < baseStart_19871 := by decide
  rcases family_descends (prefixWord ++ tailWord_19871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19874 : List Nat := [3, 3, 1, 2, 1, 4, 2, 5]
def baseStart_19874 : Nat := 118140960795 + 19874 * 2 ^ 59
def prefixEnd_19874 : Nat := 4983230072969 + 3 ^ 40 * 19874 * 2
def baseEnd_19874 : Nat := 1511839189268218753127

theorem tailTrace_19874 : CollatzResearch.WordTrace tailWord_19874 prefixEnd_19874 1511839189268218753127 := by
  unfold tailWord_19874
  simp only [CollatzResearch.WordTrace]
  refine ⟨181216082501841763520669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 483242886671578036055117 181216082501841763520669)
  ·
    refine ⟨67956030938190661320251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181216082501841763520669 67956030938190661320251)
    ·
      refine ⟨101934046407285991980377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67956030938190661320251 101934046407285991980377)
      ·
        refine ⟨76450534805464493985283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101934046407285991980377 76450534805464493985283)
        ·
          refine ⟨114675802208196740977925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76450534805464493985283 114675802208196740977925)
          ·
            refine ⟨21501712914036888933361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114675802208196740977925 21501712914036888933361)
            ·
              refine ⟨16126284685527666700021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21501712914036888933361 16126284685527666700021)
              ·
                refine ⟨1511839189268218753127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16126284685527666700021 1511839189268218753127)
                ·
                  rfl

theorem cell21_19874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_19874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19874 prefixEnd_19874 := by exact prefixLift 19874
  have htrace : WordTrace (prefixWord ++ tailWord_19874) baseStart_19874 baseEnd_19874 := by
    simpa [prefixWord, tailWord_19874, baseEnd_19874] using wordTrace_append hprefix tailTrace_19874
  have hstable : (prefixWord ++ tailWord_19874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19874).length < 2 ^ (prefixWord ++ tailWord_19874).sum := by decide
  have hdescent : baseEnd_19874 < baseStart_19874 := by decide
  rcases family_descends (prefixWord ++ tailWord_19874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19902 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_19902 : Nat := 118140960795 + 19902 * 2 ^ 59
def prefixEnd_19902 : Nat := 4983230072969 + 3 ^ 40 * 19902 * 2
def baseEnd_19902 : Nat := 4541907549282829792657

theorem tailTrace_19902 : CollatzResearch.WordTrace tailWord_19902 prefixEnd_19902 4541907549282829792657 := by
  unfold tailWord_19902
  simp only [CollatzResearch.WordTrace]
  refine ⟨90735696738240979512745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 483923715937285224067973 90735696738240979512745)
  ·
    refine ⟨68051772553680734634559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90735696738240979512745 68051772553680734634559)
    ·
      refine ⟨102077658830521101951839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68051772553680734634559 102077658830521101951839)
      ·
        refine ⟨153116488245781652927759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102077658830521101951839 153116488245781652927759)
        ·
          refine ⟨229674732368672479391639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153116488245781652927759 229674732368672479391639)
          ·
            refine ⟨344512098553008719087459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229674732368672479391639 344512098553008719087459)
            ·
              refine ⟨516768147829513078631189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344512098553008719087459 516768147829513078631189)
              ·
                refine ⟨24223506929508425560837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516768147829513078631189 24223506929508425560837)
                ·
                  refine ⟨4541907549282829792657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24223506929508425560837 4541907549282829792657)
                  ·
                    rfl

theorem cell21_19902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_19902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19902 prefixEnd_19902 := by exact prefixLift 19902
  have htrace : WordTrace (prefixWord ++ tailWord_19902) baseStart_19902 baseEnd_19902 := by
    simpa [prefixWord, tailWord_19902, baseEnd_19902] using wordTrace_append hprefix tailTrace_19902
  have hstable : (prefixWord ++ tailWord_19902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19902).length < 2 ^ (prefixWord ++ tailWord_19902).sum := by decide
  have hdescent : baseEnd_19902 < baseStart_19902 := by decide
  rcases family_descends (prefixWord ++ tailWord_19902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19916 : List Nat := [2, 2, 1, 4, 2, 1, 1, 8]
def baseStart_19916 : Nat := 118140960795 + 19916 * 2 ^ 59
def prefixEnd_19916 : Nat := 4983230072969 + 3 ^ 40 * 19916 * 2
def baseEnd_19916 : Nat := 1515034180007305519765

theorem tailTrace_19916 : CollatzResearch.WordTrace tailWord_19916 prefixEnd_19916 1515034180007305519765 := by
  unfold tailWord_19916
  simp only [CollatzResearch.WordTrace]
  refine ⟨363198097927604113555801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 484264130570138818074401 363198097927604113555801)
  ·
    refine ⟨272398573445703085166851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 363198097927604113555801 272398573445703085166851)
    ·
      refine ⟨408597860168554627750277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272398573445703085166851 408597860168554627750277)
      ·
        refine ⟨76612098781603992703177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 408597860168554627750277 76612098781603992703177)
        ·
          refine ⟨57459074086202994527383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76612098781603992703177 57459074086202994527383)
          ·
            refine ⟨86188611129304491791075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57459074086202994527383 86188611129304491791075)
            ·
              refine ⟨129282916693956737686613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86188611129304491791075 129282916693956737686613)
              ·
                refine ⟨1515034180007305519765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 129282916693956737686613 1515034180007305519765)
                ·
                  rfl

theorem cell21_19916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_19916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19916 prefixEnd_19916 := by exact prefixLift 19916
  have htrace : WordTrace (prefixWord ++ tailWord_19916) baseStart_19916 baseEnd_19916 := by
    simpa [prefixWord, tailWord_19916, baseEnd_19916] using wordTrace_append hprefix tailTrace_19916
  have hstable : (prefixWord ++ tailWord_19916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19916).length < 2 ^ (prefixWord ++ tailWord_19916).sum := by decide
  have hdescent : baseEnd_19916 < baseStart_19916 := by decide
  rcases family_descends (prefixWord ++ tailWord_19916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19978 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_19978 : Nat := 118140960795 + 19978 * 2 ^ 59
def prefixEnd_19978 : Nat := 4983230072969 + 3 ^ 40 * 19978 * 2
def baseEnd_19978 : Nat := 4559251784723586525835

theorem tailTrace_19978 : CollatzResearch.WordTrace tailWord_19978 prefixEnd_19978 4559251784723586525835 := by
  unfold tailWord_19978
  simp only [CollatzResearch.WordTrace]
  refine ⟨182164380407648203967147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 485771681087061877245725 182164380407648203967147)
  ·
    refine ⟨273246570611472305950721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182164380407648203967147 273246570611472305950721)
    ·
      refine ⟨204934927958604229463041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273246570611472305950721 204934927958604229463041)
      ·
        refine ⟨153701195968953172097281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204934927958604229463041 153701195968953172097281)
        ·
          refine ⟨115275896976714879072961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153701195968953172097281 115275896976714879072961)
          ·
            refine ⟨86456922732536159304721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115275896976714879072961 86456922732536159304721)
            ·
              refine ⟨64842692049402119478541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86456922732536159304721 64842692049402119478541)
              ·
                refine ⟨24316009518525794804453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64842692049402119478541 24316009518525794804453)
                ·
                  refine ⟨4559251784723586525835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24316009518525794804453 4559251784723586525835)
                  ·
                    rfl

theorem cell21_19978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_19978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_19978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_19978 prefixEnd_19978 := by exact prefixLift 19978
  have htrace : WordTrace (prefixWord ++ tailWord_19978) baseStart_19978 baseEnd_19978 := by
    simpa [prefixWord, tailWord_19978, baseEnd_19978] using wordTrace_append hprefix tailTrace_19978
  have hstable : (prefixWord ++ tailWord_19978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19978).length < 2 ^ (prefixWord ++ tailWord_19978).sum := by decide
  have hdescent : baseEnd_19978 < baseStart_19978 := by decide
  rcases family_descends (prefixWord ++ tailWord_19978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20023 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_20023 : Nat := 118140960795 + 20023 * 2 ^ 59
def prefixEnd_20023 : Nat := 4983230072969 + 3 ^ 40 * 20023 * 2
def baseEnd_20023 : Nat := 4569521397813508275743

theorem tailTrace_20023 : CollatzResearch.WordTrace tailWord_20023 prefixEnd_20023 4569521397813508275743 := by
  unfold tailWord_20023
  simp only [CollatzResearch.WordTrace]
  refine ⟨730298806467565501256723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 486865870978377000837815 730298806467565501256723)
  ·
    refine ⟨1095448209701348251885085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730298806467565501256723 1095448209701348251885085)
    ·
      refine ⟨410793078638005594456907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1095448209701348251885085 410793078638005594456907)
      ·
        refine ⟨616189617957008391685361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410793078638005594456907 616189617957008391685361)
        ·
          refine ⟨462142213467756293764021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616189617957008391685361 462142213467756293764021)
          ·
            refine ⟨43325832512602152540377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462142213467756293764021 43325832512602152540377)
            ·
              refine ⟨32494374384451614405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43325832512602152540377 32494374384451614405283)
              ·
                refine ⟨48741561576677421607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32494374384451614405283 48741561576677421607925)
                ·
                  refine ⟨4569521397813508275743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48741561576677421607925 4569521397813508275743)
                  ·
                    rfl

theorem cell21_20023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_20023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20023 prefixEnd_20023 := by exact prefixLift 20023
  have htrace : WordTrace (prefixWord ++ tailWord_20023) baseStart_20023 baseEnd_20023 := by
    simpa [prefixWord, tailWord_20023, baseEnd_20023] using wordTrace_append hprefix tailTrace_20023
  have hstable : (prefixWord ++ tailWord_20023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20023).length < 2 ^ (prefixWord ++ tailWord_20023).sum := by decide
  have hdescent : baseEnd_20023 < baseStart_20023 := by decide
  rcases family_descends (prefixWord ++ tailWord_20023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20068 : List Nat := [2, 3, 1, 1, 2, 5, 7]
def baseStart_20068 : Nat := 118140960795 + 20068 * 2 ^ 59
def prefixEnd_20068 : Nat := 4983230072969 + 3 ^ 40 * 20068 * 2
def baseEnd_20068 : Nat := 508865667878158891739

theorem tailTrace_20068 : CollatzResearch.WordTrace tailWord_20068 prefixEnd_20068 508865667878158891739 := by
  unfold tailWord_20068
  simp only [CollatzResearch.WordTrace]
  refine ⟨365970045652269093322429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 487960060869692124429905 365970045652269093322429)
  ·
    refine ⟨137238767119600909995911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 365970045652269093322429 137238767119600909995911)
    ·
      refine ⟨205858150679401364993867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137238767119600909995911 205858150679401364993867)
      ·
        refine ⟨308787226019102047490801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205858150679401364993867 308787226019102047490801)
        ·
          refine ⟨231590419514326535618101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308787226019102047490801 231590419514326535618101)
          ·
            refine ⟨21711601829468112714197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231590419514326535618101 21711601829468112714197)
            ·
              refine ⟨508865667878158891739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21711601829468112714197 508865667878158891739)
              ·
                rfl

theorem cell21_20068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 7].length) (baseStart_20068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20068 prefixEnd_20068 := by exact prefixLift 20068
  have htrace : WordTrace (prefixWord ++ tailWord_20068) baseStart_20068 baseEnd_20068 := by
    simpa [prefixWord, tailWord_20068, baseEnd_20068] using wordTrace_append hprefix tailTrace_20068
  have hstable : (prefixWord ++ tailWord_20068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20068).length < 2 ^ (prefixWord ++ tailWord_20068).sum := by decide
  have hdescent : baseEnd_20068 < baseStart_20068 := by decide
  rcases family_descends (prefixWord ++ tailWord_20068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20085 : List Nat := [1, 3, 4, 2, 1, 2, 2, 6]
def baseStart_20085 : Nat := 118140960795 + 20085 * 2 ^ 59
def prefixEnd_20085 : Nat := 4983230072969 + 3 ^ 40 * 20085 * 2
def baseEnd_20085 : Nat := 1527890214171726080761

theorem tailTrace_20085 : CollatzResearch.WordTrace tailWord_20085 prefixEnd_20085 1527890214171726080761 := by
  unfold tailWord_20085
  simp only [CollatzResearch.WordTrace]
  refine ⟨732560132242950090013709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 488373421495300060009139 732560132242950090013709)
  ·
    refine ⟨274710049591106283755141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 732560132242950090013709 274710049591106283755141)
    ·
      refine ⟨51508134298332428204089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274710049591106283755141 51508134298332428204089)
      ·
        refine ⟨38631100723749321153067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51508134298332428204089 38631100723749321153067)
        ·
          refine ⟨57946651085623981729601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38631100723749321153067 57946651085623981729601)
          ·
            refine ⟨43459988314217986297201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57946651085623981729601 43459988314217986297201)
            ·
              refine ⟨32594991235663489722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43459988314217986297201 32594991235663489722901)
              ·
                refine ⟨1527890214171726080761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32594991235663489722901 1527890214171726080761)
                ·
                  rfl

theorem cell21_20085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_20085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20085 prefixEnd_20085 := by exact prefixLift 20085
  have htrace : WordTrace (prefixWord ++ tailWord_20085) baseStart_20085 baseEnd_20085 := by
    simpa [prefixWord, tailWord_20085, baseEnd_20085] using wordTrace_append hprefix tailTrace_20085
  have hstable : (prefixWord ++ tailWord_20085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20085).length < 2 ^ (prefixWord ++ tailWord_20085).sum := by decide
  have hdescent : baseEnd_20085 < baseStart_20085 := by decide
  rcases family_descends (prefixWord ++ tailWord_20085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20136 : List Nat := [2, 1, 7, 1, 2, 1, 1, 6]
def baseStart_20136 : Nat := 118140960795 + 20136 * 2 ^ 59
def prefixEnd_20136 : Nat := 4983230072969 + 3 ^ 40 * 20136 * 2
def baseEnd_20136 : Nat := 1531769845783474297393

theorem tailTrace_20136 : CollatzResearch.WordTrace tailWord_20136 prefixEnd_20136 1531769845783474297393 := by
  unfold tailWord_20136
  simp only [CollatzResearch.WordTrace]
  refine ⟨367210127529092900060131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 489613503372123866746841 367210127529092900060131)
  ·
    refine ⟨550815191293639350090197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367210127529092900060131 550815191293639350090197)
    ·
      refine ⟨12909731045944672267739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 550815191293639350090197 12909731045944672267739)
      ·
        refine ⟨19364596568917008401609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12909731045944672267739 19364596568917008401609)
        ·
          refine ⟨14523447426687756301207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19364596568917008401609 14523447426687756301207)
          ·
            refine ⟨21785171140031634451811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14523447426687756301207 21785171140031634451811)
            ·
              refine ⟨32677756710047451677717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21785171140031634451811 32677756710047451677717)
              ·
                refine ⟨1531769845783474297393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32677756710047451677717 1531769845783474297393)
                ·
                  rfl

theorem cell21_20136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_20136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20136 prefixEnd_20136 := by exact prefixLift 20136
  have htrace : WordTrace (prefixWord ++ tailWord_20136) baseStart_20136 baseEnd_20136 := by
    simpa [prefixWord, tailWord_20136, baseEnd_20136] using wordTrace_append hprefix tailTrace_20136
  have hstable : (prefixWord ++ tailWord_20136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20136).length < 2 ^ (prefixWord ++ tailWord_20136).sum := by decide
  have hdescent : baseEnd_20136 < baseStart_20136 := by decide
  rcases family_descends (prefixWord ++ tailWord_20136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20330 : List Nat := [3, 1, 3, 4, 1, 1, 3, 5]
def baseStart_20330 : Nat := 118140960795 + 20330 * 2 ^ 59
def prefixEnd_20330 : Nat := 4983230072969 + 3 ^ 40 * 20330 * 2
def baseEnd_20330 : Nat := 1546527660149732219483

theorem tailTrace_20330 : CollatzResearch.WordTrace tailWord_20330 prefixEnd_20330 1546527660149732219483 := by
  unfold tailWord_20330
  simp only [CollatzResearch.WordTrace]
  refine ⟨185374004088839233170611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 494330677570237955121629 185374004088839233170611)
  ·
    refine ⟨278061006133258849755917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185374004088839233170611 278061006133258849755917)
    ·
      refine ⟨104272877299972068658469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278061006133258849755917 104272877299972068658469)
      ·
        refine ⟨19551164493744762873463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104272877299972068658469 19551164493744762873463)
        ·
          refine ⟨29326746740617144310195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19551164493744762873463 29326746740617144310195)
          ·
            refine ⟨43990120110925716465293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29326746740617144310195 43990120110925716465293)
            ·
              refine ⟨16496295041597143674485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43990120110925716465293 16496295041597143674485)
              ·
                refine ⟨1546527660149732219483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16496295041597143674485 1546527660149732219483)
                ·
                  rfl

theorem cell21_20330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_20330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20330 prefixEnd_20330 := by exact prefixLift 20330
  have htrace : WordTrace (prefixWord ++ tailWord_20330) baseStart_20330 baseEnd_20330 := by
    simpa [prefixWord, tailWord_20330, baseEnd_20330] using wordTrace_append hprefix tailTrace_20330
  have hstable : (prefixWord ++ tailWord_20330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20330).length < 2 ^ (prefixWord ++ tailWord_20330).sum := by decide
  have hdescent : baseEnd_20330 < baseStart_20330 := by decide
  rcases family_descends (prefixWord ++ tailWord_20330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20341 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_20341 : Nat := 118140960795 + 20341 * 2 ^ 59
def prefixEnd_20341 : Nat := 4983230072969 + 3 ^ 40 * 20341 * 2
def baseEnd_20341 : Nat := 4642093330315621975093

theorem tailTrace_20341 : CollatzResearch.WordTrace tailWord_20341 prefixEnd_20341 4642093330315621975093 := by
  unfold tailWord_20341
  simp only [CollatzResearch.WordTrace]
  refine ⟨741897219315505811332877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 494598146210337207555251 741897219315505811332877)
  ·
    refine ⟨278211457243314679249829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 741897219315505811332877 278211457243314679249829)
    ·
      refine ⟨52164648233121502359343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278211457243314679249829 52164648233121502359343)
      ·
        refine ⟨78246972349682253539015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52164648233121502359343 78246972349682253539015)
        ·
          refine ⟨117370458524523380308523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78246972349682253539015 117370458524523380308523)
          ·
            refine ⟨176055687786785070462785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117370458524523380308523 176055687786785070462785)
            ·
              refine ⟨132041765840088802847089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176055687786785070462785 132041765840088802847089)
              ·
                refine ⟨99031324380066602135317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132041765840088802847089 99031324380066602135317)
                ·
                  refine ⟨4642093330315621975093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99031324380066602135317 4642093330315621975093)
                  ·
                    rfl

theorem cell21_20341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_20341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20341 prefixEnd_20341 := by exact prefixLift 20341
  have htrace : WordTrace (prefixWord ++ tailWord_20341) baseStart_20341 baseEnd_20341 := by
    simpa [prefixWord, tailWord_20341, baseEnd_20341] using wordTrace_append hprefix tailTrace_20341
  have hstable : (prefixWord ++ tailWord_20341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20341).length < 2 ^ (prefixWord ++ tailWord_20341).sum := by decide
  have hdescent : baseEnd_20341 < baseStart_20341 := by decide
  rcases family_descends (prefixWord ++ tailWord_20341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20355 : List Nat := [1, 1, 1, 3, 4, 3, 8]
def baseStart_20355 : Nat := 118140960795 + 20355 * 2 ^ 59
def prefixEnd_20355 : Nat := 4983230072969 + 3 ^ 40 * 20355 * 2
def baseEnd_20355 : Nat := 516143146783856526859

theorem tailTrace_20355 : CollatzResearch.WordTrace tailWord_20355 prefixEnd_20355 516143146783856526859 := by
  unfold tailWord_20355
  simp only [CollatzResearch.WordTrace]
  refine ⟨742407841264786202342519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 494938560843190801561679 742407841264786202342519)
  ·
    refine ⟨1113611761897179303513779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742407841264786202342519 1113611761897179303513779)
    ·
      refine ⟨1670417642845768955270669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113611761897179303513779 1670417642845768955270669)
      ·
        refine ⟨626406616067163358226501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1670417642845768955270669 626406616067163358226501)
        ·
          refine ⟨117451240512593129667469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 626406616067163358226501 117451240512593129667469)
          ·
            refine ⟨44044215192222423625301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117451240512593129667469 44044215192222423625301)
            ·
              refine ⟨516143146783856526859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 44044215192222423625301 516143146783856526859)
              ·
                rfl

theorem cell21_20355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_20355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20355 prefixEnd_20355 := by exact prefixLift 20355
  have htrace : WordTrace (prefixWord ++ tailWord_20355) baseStart_20355 baseEnd_20355 := by
    simpa [prefixWord, tailWord_20355, baseEnd_20355] using wordTrace_append hprefix tailTrace_20355
  have hstable : (prefixWord ++ tailWord_20355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20355).length < 2 ^ (prefixWord ++ tailWord_20355).sum := by decide
  have hdescent : baseEnd_20355 < baseStart_20355 := by decide
  rcases family_descends (prefixWord ++ tailWord_20355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20431 : List Nat := [1, 1, 2, 1, 1, 5, 4, 6]
def baseStart_20431 : Nat := 118140960795 + 20431 * 2 ^ 59
def prefixEnd_20431 : Nat := 4983230072969 + 3 ^ 40 * 20431 * 2
def baseEnd_20431 : Nat := 1554210852165155158303

theorem tailTrace_20431 : CollatzResearch.WordTrace tailWord_20431 prefixEnd_20431 1554210852165155158303 := by
  unfold tailWord_20431
  simp only [CollatzResearch.WordTrace]
  refine ⟨745179788989451182109147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 496786525992967454739431 745179788989451182109147)
  ·
    refine ⟨1117769683484176773163721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745179788989451182109147 1117769683484176773163721)
    ·
      refine ⟨838327262613132579872791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1117769683484176773163721 838327262613132579872791)
      ·
        refine ⟨1257490893919698869809187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838327262613132579872791 1257490893919698869809187)
        ·
          refine ⟨1886236340879548304713781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257490893919698869809187 1886236340879548304713781)
          ·
            refine ⟨176834656957457653566917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1886236340879548304713781 176834656957457653566917)
            ·
              refine ⟨33156498179523310043797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176834656957457653566917 33156498179523310043797)
              ·
                refine ⟨1554210852165155158303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33156498179523310043797 1554210852165155158303)
                ·
                  rfl

theorem cell21_20431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_20431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20431 prefixEnd_20431 := by exact prefixLift 20431
  have htrace : WordTrace (prefixWord ++ tailWord_20431) baseStart_20431 baseEnd_20431 := by
    simpa [prefixWord, tailWord_20431, baseEnd_20431] using wordTrace_append hprefix tailTrace_20431
  have hstable : (prefixWord ++ tailWord_20431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20431).length < 2 ^ (prefixWord ++ tailWord_20431).sum := by decide
  have hdescent : baseEnd_20431 < baseStart_20431 := by decide
  rcases family_descends (prefixWord ++ tailWord_20431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20572 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_20572 : Nat := 118140960795 + 20572 * 2 ^ 59
def prefixEnd_20572 : Nat := 4983230072969 + 3 ^ 40 * 20572 * 2
def baseEnd_20572 : Nat := 4694810677510553624621

theorem tailTrace_20572 : CollatzResearch.WordTrace tailWord_20572 prefixEnd_20572 4694810677510553624621 := by
  unfold tailWord_20572
  simp only [CollatzResearch.WordTrace]
  refine ⟨375161240739316131495985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 500214987652421508661313 375161240739316131495985)
  ·
    refine ⟨281370930554487098621989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 375161240739316131495985 281370930554487098621989)
    ·
      refine ⟨52757049478966330991623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281370930554487098621989 52757049478966330991623)
      ·
        refine ⟨79135574218449496487435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52757049478966330991623 79135574218449496487435)
        ·
          refine ⟨118703361327674244731153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79135574218449496487435 118703361327674244731153)
          ·
            refine ⟨89027520995755683548365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118703361327674244731153 89027520995755683548365)
            ·
              refine ⟨33385320373408381330637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89027520995755683548365 33385320373408381330637)
              ·
                refine ⟨12519495140028142998989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33385320373408381330637 12519495140028142998989)
                ·
                  refine ⟨4694810677510553624621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519495140028142998989 4694810677510553624621)
                  ·
                    rfl

theorem cell21_20572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_20572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20572 prefixEnd_20572 := by exact prefixLift 20572
  have htrace : WordTrace (prefixWord ++ tailWord_20572) baseStart_20572 baseEnd_20572 := by
    simpa [prefixWord, tailWord_20572, baseEnd_20572] using wordTrace_append hprefix tailTrace_20572
  have hstable : (prefixWord ++ tailWord_20572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20572).length < 2 ^ (prefixWord ++ tailWord_20572).sum := by decide
  have hdescent : baseEnd_20572 < baseStart_20572 := by decide
  rcases family_descends (prefixWord ++ tailWord_20572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20645 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_20645 : Nat := 118140960795 + 20645 * 2 ^ 59
def prefixEnd_20645 : Nat := 4983230072969 + 3 ^ 40 * 20645 * 2
def baseEnd_20645 : Nat := 4711470272078648907805

theorem tailTrace_20645 : CollatzResearch.WordTrace tailWord_20645 prefixEnd_20645 4711470272078648907805 := by
  unfold tailWord_20645
  simp only [CollatzResearch.WordTrace]
  refine ⟨752985010214165730399389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 501990006809443820266259 752985010214165730399389)
  ·
    refine ⟨282369378830312148899771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 752985010214165730399389 282369378830312148899771)
    ·
      refine ⟨423554068245468223349657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282369378830312148899771 423554068245468223349657)
      ·
        refine ⟨317665551184101167512243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423554068245468223349657 317665551184101167512243)
        ·
          refine ⟨476498326776151751268365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317665551184101167512243 476498326776151751268365)
          ·
            refine ⟨178686872541056906725637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476498326776151751268365 178686872541056906725637)
            ·
              refine ⟨33503788601448170011057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178686872541056906725637 33503788601448170011057)
              ·
                refine ⟨25127841451086127508293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33503788601448170011057 25127841451086127508293)
                ·
                  refine ⟨4711470272078648907805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25127841451086127508293 4711470272078648907805)
                  ·
                    rfl

theorem cell21_20645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_20645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20645 prefixEnd_20645 := by exact prefixLift 20645
  have htrace : WordTrace (prefixWord ++ tailWord_20645) baseStart_20645 baseEnd_20645 := by
    simpa [prefixWord, tailWord_20645, baseEnd_20645] using wordTrace_append hprefix tailTrace_20645
  have hstable : (prefixWord ++ tailWord_20645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20645).length < 2 ^ (prefixWord ++ tailWord_20645).sum := by decide
  have hdescent : baseEnd_20645 < baseStart_20645 := by decide
  rcases family_descends (prefixWord ++ tailWord_20645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20704 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_20704 : Nat := 118140960795 + 20704 * 2 ^ 59
def prefixEnd_20704 : Nat := 4983230072969 + 3 ^ 40 * 20704 * 2
def baseEnd_20704 : Nat := 4724934875907657424351

theorem tailTrace_20704 : CollatzResearch.WordTrace tailWord_20704 prefixEnd_20704 4724934875907657424351 := by
  unfold tailWord_20704
  simp only [CollatzResearch.WordTrace]
  refine ⟨377568458500209403398583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 503424611333612537864777 377568458500209403398583)
  ·
    refine ⟨566352687750314105097875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377568458500209403398583 566352687750314105097875)
    ·
      refine ⟨849529031625471157646813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566352687750314105097875 849529031625471157646813)
      ·
        refine ⟨318573386859551684117555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 849529031625471157646813 318573386859551684117555)
        ·
          refine ⟨477860080289327526176333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318573386859551684117555 477860080289327526176333)
          ·
            refine ⟨179197530108497822316125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477860080289327526176333 179197530108497822316125)
            ·
              refine ⟨67199073790686683368547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179197530108497822316125 67199073790686683368547)
              ·
                refine ⟨100798610686030025052821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67199073790686683368547 100798610686030025052821)
                ·
                  refine ⟨4724934875907657424351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100798610686030025052821 4724934875907657424351)
                  ·
                    rfl

theorem cell21_20704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_20704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20704 prefixEnd_20704 := by exact prefixLift 20704
  have htrace : WordTrace (prefixWord ++ tailWord_20704) baseStart_20704 baseEnd_20704 := by
    simpa [prefixWord, tailWord_20704, baseEnd_20704] using wordTrace_append hprefix tailTrace_20704
  have hstable : (prefixWord ++ tailWord_20704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20704).length < 2 ^ (prefixWord ++ tailWord_20704).sum := by decide
  have hdescent : baseEnd_20704 < baseStart_20704 := by decide
  rcases family_descends (prefixWord ++ tailWord_20704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20825 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_20825 : Nat := 118140960795 + 20825 * 2 ^ 59
def prefixEnd_20825 : Nat := 4983230072969 + 3 ^ 40 * 20825 * 2
def baseEnd_20825 : Nat := 4752548724438335907437

theorem tailTrace_20825 : CollatzResearch.WordTrace tailWord_20825 prefixEnd_20825 4752548724438335907437 := by
  unfold tailWord_20825
  simp only [CollatzResearch.WordTrace]
  refine ⟨759550149562056471951929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 506366766374704314634619 759550149562056471951929)
  ·
    refine ⟨569662612171542353963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 759550149562056471951929 569662612171542353963947)
    ·
      refine ⟨854493918257313530945921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569662612171542353963947 854493918257313530945921)
      ·
        refine ⟨640870438692985148209441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854493918257313530945921 640870438692985148209441)
        ·
          refine ⟨480652829019738861157081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640870438692985148209441 480652829019738861157081)
          ·
            refine ⟨360489621764804145867811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480652829019738861157081 360489621764804145867811)
            ·
              refine ⟨540734432647206218801717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360489621764804145867811 540734432647206218801717)
              ·
                refine ⟨50693853060675583012661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540734432647206218801717 50693853060675583012661)
                ·
                  refine ⟨4752548724438335907437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50693853060675583012661 4752548724438335907437)
                  ·
                    rfl

theorem cell21_20825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_20825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20825 prefixEnd_20825 := by exact prefixLift 20825
  have htrace : WordTrace (prefixWord ++ tailWord_20825) baseStart_20825 baseEnd_20825 := by
    simpa [prefixWord, tailWord_20825, baseEnd_20825] using wordTrace_append hprefix tailTrace_20825
  have hstable : (prefixWord ++ tailWord_20825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20825).length < 2 ^ (prefixWord ++ tailWord_20825).sum := by decide
  have hdescent : baseEnd_20825 < baseStart_20825 := by decide
  rcases family_descends (prefixWord ++ tailWord_20825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20842 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_20842 : Nat := 118140960795 + 20842 * 2 ^ 59
def prefixEnd_20842 : Nat := 4983230072969 + 3 ^ 40 * 20842 * 2
def baseEnd_20842 : Nat := 4756428356050084124069

theorem tailTrace_20842 : CollatzResearch.WordTrace tailWord_20842 prefixEnd_20842 4756428356050084124069 := by
  unfold tailWord_20842
  simp only [CollatzResearch.WordTrace]
  refine ⟨190042547625117093830195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 506780127000312250213853 190042547625117093830195)
  ·
    refine ⟨285063821437675640745293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190042547625117093830195 285063821437675640745293)
    ·
      refine ⟨106898933039128365279485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285063821437675640745293 106898933039128365279485)
      ·
        refine ⟨40087099889673136979807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106898933039128365279485 40087099889673136979807)
        ·
          refine ⟨60130649834509705469711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40087099889673136979807 60130649834509705469711)
          ·
            refine ⟨90195974751764558204567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60130649834509705469711 90195974751764558204567)
            ·
              refine ⟨135293962127646837306851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90195974751764558204567 135293962127646837306851)
              ·
                refine ⟨202940943191470255960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135293962127646837306851 202940943191470255960277)
                ·
                  refine ⟨4756428356050084124069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 202940943191470255960277 4756428356050084124069)
                  ·
                    rfl

theorem cell21_20842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_20842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20842 prefixEnd_20842 := by exact prefixLift 20842
  have htrace : WordTrace (prefixWord ++ tailWord_20842) baseStart_20842 baseEnd_20842 := by
    simpa [prefixWord, tailWord_20842, baseEnd_20842] using wordTrace_append hprefix tailTrace_20842
  have hstable : (prefixWord ++ tailWord_20842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20842).length < 2 ^ (prefixWord ++ tailWord_20842).sum := by decide
  have hdescent : baseEnd_20842 < baseStart_20842 := by decide
  rcases family_descends (prefixWord ++ tailWord_20842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20859 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 3]
def baseStart_20859 : Nat := 118140960795 + 20859 * 2 ^ 59
def prefixEnd_20859 : Nat := 4983230072969 + 3 ^ 40 * 20859 * 2
def baseEnd_20859 : Nat := 4760307987661832340701

theorem tailTrace_20859 : CollatzResearch.WordTrace tailWord_20859 prefixEnd_20859 4760307987661832340701 := by
  unfold tailWord_20859
  simp only [CollatzResearch.WordTrace]
  refine ⟨760790231438880278689631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 507193487625920185793087 760790231438880278689631)
  ·
    refine ⟨1141185347158320418034447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760790231438880278689631 1141185347158320418034447)
    ·
      refine ⟨1711778020737480627051671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141185347158320418034447 1711778020737480627051671)
      ·
        refine ⟨2567667031106220940577507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711778020737480627051671 2567667031106220940577507)
        ·
          refine ⟨3851500546659331410866261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567667031106220940577507 3851500546659331410866261)
          ·
            refine ⟨45134772031164039971089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 3851500546659331410866261 45134772031164039971089)
            ·
              refine ⟨33851079023373029978317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45134772031164039971089 33851079023373029978317)
              ·
                refine ⟨12694154633764886241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33851079023373029978317 12694154633764886241869)
                ·
                  refine ⟨4760307987661832340701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12694154633764886241869 4760307987661832340701)
                  ·
                    rfl

theorem cell21_20859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 3].length) (baseStart_20859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20859 prefixEnd_20859 := by exact prefixLift 20859
  have htrace : WordTrace (prefixWord ++ tailWord_20859) baseStart_20859 baseEnd_20859 := by
    simpa [prefixWord, tailWord_20859, baseEnd_20859] using wordTrace_append hprefix tailTrace_20859
  have hstable : (prefixWord ++ tailWord_20859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20859).length < 2 ^ (prefixWord ++ tailWord_20859).sum := by decide
  have hdescent : baseEnd_20859 < baseStart_20859 := by decide
  rcases family_descends (prefixWord ++ tailWord_20859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20873 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_20873 : Nat := 118140960795 + 20873 * 2 ^ 59
def prefixEnd_20873 : Nat := 4983230072969 + 3 ^ 40 * 20873 * 2
def baseEnd_20873 : Nat := 4763502978400919107339

theorem tailTrace_20873 : CollatzResearch.WordTrace tailWord_20873 prefixEnd_20873 4763502978400919107339 := by
  unfold tailWord_20873
  simp only [CollatzResearch.WordTrace]
  refine ⟨761300853388160669699273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 507533902258773779799515 761300853388160669699273)
  ·
    refine ⟨570975640041120502274455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 761300853388160669699273 570975640041120502274455)
    ·
      refine ⟨856463460061680753411683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570975640041120502274455 856463460061680753411683)
      ·
        refine ⟨1284695190092521130117525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856463460061680753411683 1284695190092521130117525)
        ·
          refine ⟨60220087035586927974259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1284695190092521130117525 60220087035586927974259)
          ·
            refine ⟨90330130553380391961389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60220087035586927974259 90330130553380391961389)
            ·
              refine ⟨33873798957517646985521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90330130553380391961389 33873798957517646985521)
              ·
                refine ⟨25405349218138235239141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33873798957517646985521 25405349218138235239141)
                ·
                  refine ⟨4763502978400919107339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25405349218138235239141 4763502978400919107339)
                  ·
                    rfl

theorem cell21_20873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_20873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20873 prefixEnd_20873 := by exact prefixLift 20873
  have htrace : WordTrace (prefixWord ++ tailWord_20873) baseStart_20873 baseEnd_20873 := by
    simpa [prefixWord, tailWord_20873, baseEnd_20873] using wordTrace_append hprefix tailTrace_20873
  have hstable : (prefixWord ++ tailWord_20873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20873).length < 2 ^ (prefixWord ++ tailWord_20873).sum := by decide
  have hdescent : baseEnd_20873 < baseStart_20873 := by decide
  rcases family_descends (prefixWord ++ tailWord_20873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20890 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_20890 : Nat := 118140960795 + 20890 * 2 ^ 59
def prefixEnd_20890 : Nat := 4983230072969 + 3 ^ 40 * 20890 * 2
def baseEnd_20890 : Nat := 4767382610012667323971

theorem tailTrace_20890 : CollatzResearch.WordTrace tailWord_20890 prefixEnd_20890 4767382610012667323971 := by
  unfold tailWord_20890
  simp only [CollatzResearch.WordTrace]
  refine ⟨190480223581643143267031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 507947262884381715378749 190480223581643143267031)
  ·
    refine ⟨285720335372464714900547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190480223581643143267031 285720335372464714900547)
    ·
      refine ⟨428580503058697072350821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285720335372464714900547 428580503058697072350821)
      ·
        refine ⟨80358844323505701065779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428580503058697072350821 80358844323505701065779)
        ·
          refine ⟨120538266485258551598669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80358844323505701065779 120538266485258551598669)
          ·
            refine ⟨45201849931971956849501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120538266485258551598669 45201849931971956849501)
            ·
              refine ⟨16950693724489483818563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45201849931971956849501 16950693724489483818563)
              ·
                refine ⟨25426040586734225727845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16950693724489483818563 25426040586734225727845)
                ·
                  refine ⟨4767382610012667323971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25426040586734225727845 4767382610012667323971)
                  ·
                    rfl

theorem cell21_20890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_20890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20890 prefixEnd_20890 := by exact prefixLift 20890
  have htrace : WordTrace (prefixWord ++ tailWord_20890) baseStart_20890 baseEnd_20890 := by
    simpa [prefixWord, tailWord_20890, baseEnd_20890] using wordTrace_append hprefix tailTrace_20890
  have hstable : (prefixWord ++ tailWord_20890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20890).length < 2 ^ (prefixWord ++ tailWord_20890).sum := by decide
  have hdescent : baseEnd_20890 < baseStart_20890 := by decide
  rcases family_descends (prefixWord ++ tailWord_20890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20901 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_20901 : Nat := 118140960795 + 20901 * 2 ^ 59
def prefixEnd_20901 : Nat := 4983230072969 + 3 ^ 40 * 20901 * 2
def baseEnd_20901 : Nat := 4769892959879092640615

theorem tailTrace_20901 : CollatzResearch.WordTrace tailWord_20901 prefixEnd_20901 4769892959879092640615 := by
  unfold tailWord_20901
  simp only [CollatzResearch.WordTrace]
  refine ⟨762322097286721451718557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508214731524480967812371 762322097286721451718557)
  ·
    refine ⟨285870786482520544394459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 762322097286721451718557 285870786482520544394459)
    ·
      refine ⟨428806179723780816591689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285870786482520544394459 428806179723780816591689)
      ·
        refine ⟨321604634792835612443767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428806179723780816591689 321604634792835612443767)
        ·
          refine ⟨482406952189253418665651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321604634792835612443767 482406952189253418665651)
          ·
            refine ⟨723610428283880127998477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482406952189253418665651 723610428283880127998477)
            ·
              refine ⟨271353910606455047999429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 723610428283880127998477 271353910606455047999429)
              ·
                refine ⟨50878858238710321499893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271353910606455047999429 50878858238710321499893)
                ·
                  refine ⟨4769892959879092640615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50878858238710321499893 4769892959879092640615)
                  ·
                    rfl

theorem cell21_20901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_20901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20901 prefixEnd_20901 := by exact prefixLift 20901
  have htrace : WordTrace (prefixWord ++ tailWord_20901) baseStart_20901 baseEnd_20901 := by
    simpa [prefixWord, tailWord_20901, baseEnd_20901] using wordTrace_append hprefix tailTrace_20901
  have hstable : (prefixWord ++ tailWord_20901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20901).length < 2 ^ (prefixWord ++ tailWord_20901).sum := by decide
  have hdescent : baseEnd_20901 < baseStart_20901 := by decide
  rcases family_descends (prefixWord ++ tailWord_20901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20904 : List Nat := [2, 1, 6, 1, 1, 2, 1, 7]
def baseStart_20904 : Nat := 118140960795 + 20904 * 2 ^ 59
def prefixEnd_20904 : Nat := 4983230072969 + 3 ^ 40 * 20904 * 2
def baseEnd_20904 : Nat := 1590192533583918030203

theorem tailTrace_20904 : CollatzResearch.WordTrace tailWord_20904 prefixEnd_20904 1590192533583918030203 := by
  unfold tailWord_20904
  simp only [CollatzResearch.WordTrace]
  refine ⟨381215758137926482038883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 508287677517235309385177 381215758137926482038883)
  ·
    refine ⟨571823637206889723058325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381215758137926482038883 571823637206889723058325)
    ·
      refine ⟨26804232994072955768359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 571823637206889723058325 26804232994072955768359)
      ·
        refine ⟨40206349491109433652539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26804232994072955768359 40206349491109433652539)
        ·
          refine ⟨60309524236664150478809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40206349491109433652539 60309524236664150478809)
          ·
            refine ⟨45232143177498112859107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60309524236664150478809 45232143177498112859107)
            ·
              refine ⟨67848214766247169288661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45232143177498112859107 67848214766247169288661)
              ·
                refine ⟨1590192533583918030203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67848214766247169288661 1590192533583918030203)
                ·
                  rfl

theorem cell21_20904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_20904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20904 prefixEnd_20904 := by exact prefixLift 20904
  have htrace : WordTrace (prefixWord ++ tailWord_20904) baseStart_20904 baseEnd_20904 := by
    simpa [prefixWord, tailWord_20904, baseEnd_20904] using wordTrace_append hprefix tailTrace_20904
  have hstable : (prefixWord ++ tailWord_20904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20904).length < 2 ^ (prefixWord ++ tailWord_20904).sum := by decide
  have hdescent : baseEnd_20904 < baseStart_20904 := by decide
  rcases family_descends (prefixWord ++ tailWord_20904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20949 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_20949 : Nat := 118140960795 + 20949 * 2 ^ 59
def prefixEnd_20949 : Nat := 4983230072969 + 3 ^ 40 * 20949 * 2
def baseEnd_20949 : Nat := 4780847213841675840517

theorem tailTrace_20949 : CollatzResearch.WordTrace tailWord_20949 prefixEnd_20949 4780847213841675840517 := by
  unfold tailWord_20949
  simp only [CollatzResearch.WordTrace]
  refine ⟨764072801112825649465901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 509381867408550432977267 764072801112825649465901)
  ·
    refine ⟨286527300417309618549713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 764072801112825649465901 286527300417309618549713)
    ·
      refine ⟨214895475312982213912285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286527300417309618549713 214895475312982213912285)
      ·
        refine ⟨80585803242368330217107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214895475312982213912285 80585803242368330217107)
        ·
          refine ⟨120878704863552495325661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80585803242368330217107 120878704863552495325661)
          ·
            refine ⟨45329514323832185747123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120878704863552495325661 45329514323832185747123)
            ·
              refine ⟨67994271485748278620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45329514323832185747123 67994271485748278620685)
              ·
                refine ⟨25497851807155604482757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67994271485748278620685 25497851807155604482757)
                ·
                  refine ⟨4780847213841675840517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25497851807155604482757 4780847213841675840517)
                  ·
                    rfl

theorem cell21_20949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_20949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_20949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_20949 prefixEnd_20949 := by exact prefixLift 20949
  have htrace : WordTrace (prefixWord ++ tailWord_20949) baseStart_20949 baseEnd_20949 := by
    simpa [prefixWord, tailWord_20949, baseEnd_20949] using wordTrace_append hprefix tailTrace_20949
  have hstable : (prefixWord ++ tailWord_20949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20949).length < 2 ^ (prefixWord ++ tailWord_20949).sum := by decide
  have hdescent : baseEnd_20949 < baseStart_20949 := by decide
  rcases family_descends (prefixWord ++ tailWord_20949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21104 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_21104 : Nat := 118140960795 + 21104 * 2 ^ 59
def prefixEnd_21104 : Nat := 4983230072969 + 3 ^ 40 * 21104 * 2
def baseEnd_21104 : Nat := 4816220325595850756867

theorem tailTrace_21104 : CollatzResearch.WordTrace tailWord_21104 prefixEnd_21104 4816220325595850756867 := by
  unfold tailWord_21104
  simp only [CollatzResearch.WordTrace]
  refine ⟨384863057775643560679183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 513150743700858080905577 384863057775643560679183)
  ·
    refine ⟨577294586663465341018775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384863057775643560679183 577294586663465341018775)
    ·
      refine ⟨865941879995198011528163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577294586663465341018775 865941879995198011528163)
      ·
        refine ⟨1298912819992797017292245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865941879995198011528163 1298912819992797017292245)
        ·
          refine ⟨30443269218581180092787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1298912819992797017292245 30443269218581180092787)
          ·
            refine ⟨45664903827871770139181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30443269218581180092787 45664903827871770139181)
            ·
              refine ⟨17124338935451913802193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45664903827871770139181 17124338935451913802193)
              ·
                refine ⟨12843254201588935351645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17124338935451913802193 12843254201588935351645)
                ·
                  refine ⟨4816220325595850756867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12843254201588935351645 4816220325595850756867)
                  ·
                    rfl

theorem cell21_21104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_21104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21104 prefixEnd_21104 := by exact prefixLift 21104
  have htrace : WordTrace (prefixWord ++ tailWord_21104) baseStart_21104 baseEnd_21104 := by
    simpa [prefixWord, tailWord_21104, baseEnd_21104] using wordTrace_append hprefix tailTrace_21104
  have hstable : (prefixWord ++ tailWord_21104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21104).length < 2 ^ (prefixWord ++ tailWord_21104).sum := by decide
  have hdescent : baseEnd_21104 < baseStart_21104 := by decide
  rcases family_descends (prefixWord ++ tailWord_21104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21197 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 3]
def baseStart_21197 : Nat := 118140960795 + 21197 * 2 ^ 59
def prefixEnd_21197 : Nat := 4983230072969 + 3 ^ 40 * 21197 * 2
def baseEnd_21197 : Nat := 4837444192648355706677

theorem tailTrace_21197 : CollatzResearch.WordTrace tailWord_21197 prefixEnd_21197 4837444192648355706677 := by
  unfold tailWord_21197
  simp only [CollatzResearch.WordTrace]
  refine ⟨773118104214364004493845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 515412069476242669662563 773118104214364004493845)
  ·
    refine ⟨36239911135048312710649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 773118104214364004493845 36239911135048312710649)
    ·
      refine ⟨27179933351286234532987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36239911135048312710649 27179933351286234532987)
      ·
        refine ⟨40769900026929351799481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27179933351286234532987 40769900026929351799481)
        ·
          refine ⟨30577425020197013849611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40769900026929351799481 30577425020197013849611)
          ·
            refine ⟨45866137530295520774417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30577425020197013849611 45866137530295520774417)
            ·
              refine ⟨34399603147721640580813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45866137530295520774417 34399603147721640580813)
              ·
                refine ⟨12899851180395615217805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34399603147721640580813 12899851180395615217805)
                ·
                  refine ⟨4837444192648355706677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12899851180395615217805 4837444192648355706677)
                  ·
                    rfl

theorem cell21_21197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_21197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21197 prefixEnd_21197 := by exact prefixLift 21197
  have htrace : WordTrace (prefixWord ++ tailWord_21197) baseStart_21197 baseEnd_21197 := by
    simpa [prefixWord, tailWord_21197, baseEnd_21197] using wordTrace_append hprefix tailTrace_21197
  have hstable : (prefixWord ++ tailWord_21197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21197).length < 2 ^ (prefixWord ++ tailWord_21197).sum := by decide
  have hdescent : baseEnd_21197 < baseStart_21197 := by decide
  rcases family_descends (prefixWord ++ tailWord_21197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21329 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_21329 : Nat := 118140960795 + 21329 * 2 ^ 59
def prefixEnd_21329 : Nat := 4983230072969 + 3 ^ 40 * 21329 * 2
def baseEnd_21329 : Nat := 4867568391045459506407

theorem tailTrace_21329 : CollatzResearch.WordTrace tailWord_21329 prefixEnd_21329 4867568391045459506407 := by
  unfold tailWord_21329
  simp only [CollatzResearch.WordTrace]
  refine ⟨777932539736150548299041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 518621693157433698866027 777932539736150548299041)
  ·
    refine ⟨583449404802112911224281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 777932539736150548299041 583449404802112911224281)
    ·
      refine ⟨437587053601584683418211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583449404802112911224281 437587053601584683418211)
      ·
        refine ⟨656380580402377025127317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437587053601584683418211 656380580402377025127317)
        ·
          refine ⟨30767839706361423052843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 656380580402377025127317 30767839706361423052843)
          ·
            refine ⟨46151759559542134579265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30767839706361423052843 46151759559542134579265)
            ·
              refine ⟨34613819669656600934449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46151759559542134579265 34613819669656600934449)
              ·
                refine ⟨25960364752242450700837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34613819669656600934449 25960364752242450700837)
                ·
                  refine ⟨4867568391045459506407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25960364752242450700837 4867568391045459506407)
                  ·
                    rfl

theorem cell21_21329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_21329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21329 prefixEnd_21329 := by exact prefixLift 21329
  have htrace : WordTrace (prefixWord ++ tailWord_21329) baseStart_21329 baseEnd_21329 := by
    simpa [prefixWord, tailWord_21329, baseEnd_21329] using wordTrace_append hprefix tailTrace_21329
  have hstable : (prefixWord ++ tailWord_21329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21329).length < 2 ^ (prefixWord ++ tailWord_21329).sum := by decide
  have hdescent : baseEnd_21329 < baseStart_21329 := by decide
  rcases family_descends (prefixWord ++ tailWord_21329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21388 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_21388 : Nat := 118140960795 + 21388 * 2 ^ 59
def prefixEnd_21388 : Nat := 4983230072969 + 3 ^ 40 * 21388 * 2
def baseEnd_21388 : Nat := 4881032994874468022953

theorem tailTrace_21388 : CollatzResearch.WordTrace tailWord_21388 prefixEnd_21388 4881032994874468022953 := by
  unfold tailWord_21388
  simp only [CollatzResearch.WordTrace]
  refine ⟨390042223261201812348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 520056297681602416464545 390042223261201812348409)
  ·
    refine ⟨292531667445901359261307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 390042223261201812348409 292531667445901359261307)
    ·
      refine ⟨438797501168852038891961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292531667445901359261307 438797501168852038891961)
      ·
        refine ⟨329098125876639029168971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438797501168852038891961 329098125876639029168971)
        ·
          refine ⟨493647188814958543753457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329098125876639029168971 493647188814958543753457)
          ·
            refine ⟨370235391611218907815093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493647188814958543753457 370235391611218907815093)
            ·
              refine ⟨34709567963551772607665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370235391611218907815093 34709567963551772607665)
              ·
                refine ⟨26032175972663829455749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34709567963551772607665 26032175972663829455749)
                ·
                  refine ⟨4881032994874468022953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26032175972663829455749 4881032994874468022953)
                  ·
                    rfl

theorem cell21_21388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_21388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21388 prefixEnd_21388 := by exact prefixLift 21388
  have htrace : WordTrace (prefixWord ++ tailWord_21388) baseStart_21388 baseEnd_21388 := by
    simpa [prefixWord, tailWord_21388, baseEnd_21388] using wordTrace_append hprefix tailTrace_21388
  have hstable : (prefixWord ++ tailWord_21388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21388).length < 2 ^ (prefixWord ++ tailWord_21388).sum := by decide
  have hdescent : baseEnd_21388 < baseStart_21388 := by decide
  rcases family_descends (prefixWord ++ tailWord_21388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21405 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 4]
def baseStart_21405 : Nat := 118140960795 + 21405 * 2 ^ 59
def prefixEnd_21405 : Nat := 4983230072969 + 3 ^ 40 * 21405 * 2
def baseEnd_21405 : Nat := 4884912626486216239585

theorem tailTrace_21405 : CollatzResearch.WordTrace tailWord_21405 prefixEnd_21405 4884912626486216239585 := by
  unfold tailWord_21405
  simp only [CollatzResearch.WordTrace]
  refine ⟨780704487460815528065669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 520469658307210352043779 780704487460815528065669)
  ·
    refine ⟨146382091398902911512313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 780704487460815528065669 146382091398902911512313)
    ·
      refine ⟨109786568549177183634235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146382091398902911512313 109786568549177183634235)
      ·
        refine ⟨164679852823765775451353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109786568549177183634235 164679852823765775451353)
        ·
          refine ⟨123509889617824331588515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164679852823765775451353 123509889617824331588515)
          ·
            refine ⟨185264834426736497382773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123509889617824331588515 185264834426736497382773)
            ·
              refine ⟨17368578227506546629635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185264834426736497382773 17368578227506546629635)
              ·
                refine ⟨26052867341259819944453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17368578227506546629635 26052867341259819944453)
                ·
                  refine ⟨4884912626486216239585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26052867341259819944453 4884912626486216239585)
                  ·
                    rfl

theorem cell21_21405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_21405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21405 prefixEnd_21405 := by exact prefixLift 21405
  have htrace : WordTrace (prefixWord ++ tailWord_21405) baseStart_21405 baseEnd_21405 := by
    simpa [prefixWord, tailWord_21405, baseEnd_21405] using wordTrace_append hprefix tailTrace_21405
  have hstable : (prefixWord ++ tailWord_21405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21405).length < 2 ^ (prefixWord ++ tailWord_21405).sum := by decide
  have hdescent : baseEnd_21405 < baseStart_21405 := by decide
  rcases family_descends (prefixWord ++ tailWord_21405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21447 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_21447 : Nat := 118140960795 + 21447 * 2 ^ 59
def prefixEnd_21447 : Nat := 4983230072969 + 3 ^ 40 * 21447 * 2
def baseEnd_21447 : Nat := 4894497598703476539499

theorem tailTrace_21447 : CollatzResearch.WordTrace tailWord_21447 prefixEnd_21447 4894497598703476539499 := by
  unfold tailWord_21447
  simp only [CollatzResearch.WordTrace]
  refine ⟨782236353308656701094595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 521490902205771134063063 782236353308656701094595)
  ·
    refine ⟨1173354529962985051641893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782236353308656701094595 1173354529962985051641893)
    ·
      refine ⟨220003974368059697182855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1173354529962985051641893 220003974368059697182855)
      ·
        refine ⟨330005961552089545774283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220003974368059697182855 330005961552089545774283)
        ·
          refine ⟨495008942328134318661425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330005961552089545774283 495008942328134318661425)
          ·
            refine ⟨371256706746100738996069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495008942328134318661425 371256706746100738996069)
            ·
              refine ⟨69610632514893888561763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 371256706746100738996069 69610632514893888561763)
              ·
                refine ⟨104415948772340832842645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69610632514893888561763 104415948772340832842645)
                ·
                  refine ⟨4894497598703476539499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104415948772340832842645 4894497598703476539499)
                  ·
                    rfl

theorem cell21_21447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_21447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21447 prefixEnd_21447 := by exact prefixLift 21447
  have htrace : WordTrace (prefixWord ++ tailWord_21447) baseStart_21447 baseEnd_21447 := by
    simpa [prefixWord, tailWord_21447, baseEnd_21447] using wordTrace_append hprefix tailTrace_21447
  have hstable : (prefixWord ++ tailWord_21447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21447).length < 2 ^ (prefixWord ++ tailWord_21447).sum := by decide
  have hdescent : baseEnd_21447 < baseStart_21447 := by decide
  rcases family_descends (prefixWord ++ tailWord_21447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21464 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_21464 : Nat := 118140960795 + 21464 * 2 ^ 59
def prefixEnd_21464 : Nat := 4983230072969 + 3 ^ 40 * 21464 * 2
def baseEnd_21464 : Nat := 4898377230315224756131

theorem tailTrace_21464 : CollatzResearch.WordTrace tailWord_21464 prefixEnd_21464 4898377230315224756131 := by
  unfold tailWord_21464
  simp only [CollatzResearch.WordTrace]
  refine ⟨391428197123534302231723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 521904262831379069642297 391428197123534302231723)
  ·
    refine ⟨587142295685301453347585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391428197123534302231723 587142295685301453347585)
    ·
      refine ⟨440356721763976090010689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587142295685301453347585 440356721763976090010689)
      ·
        refine ⟨330267541322982067508017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440356721763976090010689 330267541322982067508017)
        ·
          refine ⟨247700655992236550631013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330267541322982067508017 247700655992236550631013)
          ·
            refine ⟨46443872998544353243315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247700655992236550631013 46443872998544353243315)
            ·
              refine ⟨69665809497816529864973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46443872998544353243315 69665809497816529864973)
              ·
                refine ⟨26124678561681198699365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69665809497816529864973 26124678561681198699365)
                ·
                  refine ⟨4898377230315224756131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26124678561681198699365 4898377230315224756131)
                  ·
                    rfl

theorem cell21_21464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_21464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21464 prefixEnd_21464 := by exact prefixLift 21464
  have htrace : WordTrace (prefixWord ++ tailWord_21464) baseStart_21464 baseEnd_21464 := by
    simpa [prefixWord, tailWord_21464, baseEnd_21464] using wordTrace_append hprefix tailTrace_21464
  have hstable : (prefixWord ++ tailWord_21464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21464).length < 2 ^ (prefixWord ++ tailWord_21464).sum := by decide
  have hdescent : baseEnd_21464 < baseStart_21464 := by decide
  rcases family_descends (prefixWord ++ tailWord_21464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21543 : List Nat := [1, 1, 7, 1, 1, 1, 1, 5, 3]
def baseStart_21543 : Nat := 118140960795 + 21543 * 2 ^ 59
def prefixEnd_21543 : Nat := 4983230072969 + 3 ^ 40 * 21543 * 2
def baseEnd_21543 : Nat := 4916406106628642939303

theorem tailTrace_21543 : CollatzResearch.WordTrace tailWord_21543 prefixEnd_21543 4916406106628642939303 := by
  unfold tailWord_21543
  simp only [CollatzResearch.WordTrace]
  refine ⟨785737760960865096589283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 523825173973910064392855 785737760960865096589283)
  ·
    refine ⟨1178606641441297644883925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785737760960865096589283 1178606641441297644883925)
    ·
      refine ⟨27623593158780413551967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1178606641441297644883925 27623593158780413551967)
      ·
        refine ⟨41435389738170620327951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27623593158780413551967 41435389738170620327951)
        ·
          refine ⟨62153084607255930491927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41435389738170620327951 62153084607255930491927)
          ·
            refine ⟨93229626910883895737891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62153084607255930491927 93229626910883895737891)
            ·
              refine ⟨139844440366325843606837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93229626910883895737891 139844440366325843606837)
              ·
                refine ⟨13110416284343047838141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139844440366325843606837 13110416284343047838141)
                ·
                  refine ⟨4916406106628642939303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110416284343047838141 4916406106628642939303)
                  ·
                    rfl

theorem cell21_21543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5, 3].length) (baseStart_21543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21543 prefixEnd_21543 := by exact prefixLift 21543
  have htrace : WordTrace (prefixWord ++ tailWord_21543) baseStart_21543 baseEnd_21543 := by
    simpa [prefixWord, tailWord_21543, baseEnd_21543] using wordTrace_append hprefix tailTrace_21543
  have hstable : (prefixWord ++ tailWord_21543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21543).length < 2 ^ (prefixWord ++ tailWord_21543).sum := by decide
  have hdescent : baseEnd_21543 < baseStart_21543 := by decide
  rcases family_descends (prefixWord ++ tailWord_21543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21633 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 4]
def baseStart_21633 : Nat := 118140960795 + 21633 * 2 ^ 59
def prefixEnd_21633 : Nat := 4983230072969 + 3 ^ 40 * 21633 * 2
def baseEnd_21633 : Nat := 4936945332808486439119

theorem tailTrace_21633 : CollatzResearch.WordTrace tailWord_21633 prefixEnd_21633 4936945332808486439119 := by
  unfold tailWord_21633
  simp only [CollatzResearch.WordTrace]
  refine ⟨789020330634810467365553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 526013553756540311577035 789020330634810467365553)
  ·
    refine ⟨591765247976107850524165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 789020330634810467365553 591765247976107850524165)
    ·
      refine ⟨110955983995520221973281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 591765247976107850524165 110955983995520221973281)
      ·
        refine ⟨83216987996640166479961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110955983995520221973281 83216987996640166479961)
        ·
          refine ⟨62412740997480124859971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83216987996640166479961 62412740997480124859971)
          ·
            refine ⟨93619111496220187289957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62412740997480124859971 93619111496220187289957)
            ·
              refine ⟨17553583405541285116867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93619111496220187289957 17553583405541285116867)
              ·
                refine ⟨26330375108311927675301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17553583405541285116867 26330375108311927675301)
                ·
                  refine ⟨4936945332808486439119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26330375108311927675301 4936945332808486439119)
                  ·
                    rfl

theorem cell21_21633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_21633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21633 prefixEnd_21633 := by exact prefixLift 21633
  have htrace : WordTrace (prefixWord ++ tailWord_21633) baseStart_21633 baseEnd_21633 := by
    simpa [prefixWord, tailWord_21633, baseEnd_21633] using wordTrace_append hprefix tailTrace_21633
  have hstable : (prefixWord ++ tailWord_21633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21633).length < 2 ^ (prefixWord ++ tailWord_21633).sum := by decide
  have hdescent : baseEnd_21633 < baseStart_21633 := by decide
  rcases family_descends (prefixWord ++ tailWord_21633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21644 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_21644 : Nat := 118140960795 + 21644 * 2 ^ 59
def prefixEnd_21644 : Nat := 4983230072969 + 3 ^ 40 * 21644 * 2
def baseEnd_21644 : Nat := 4939455682674911755763

theorem tailTrace_21644 : CollatzResearch.WordTrace tailWord_21644 prefixEnd_21644 4939455682674911755763 := by
  unfold tailWord_21644
  simp only [CollatzResearch.WordTrace]
  refine ⟨394710766797479673007993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 526281022396639564010657 394710766797479673007993)
  ·
    refine ⟨296033075098109754755995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 394710766797479673007993 296033075098109754755995)
    ·
      refine ⟨444049612647164632133993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296033075098109754755995 444049612647164632133993)
      ·
        refine ⟨333037209485373474100495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444049612647164632133993 333037209485373474100495)
        ·
          refine ⟨499555814228060211150743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333037209485373474100495 499555814228060211150743)
          ·
            refine ⟨749333721342090316726115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499555814228060211150743 749333721342090316726115)
            ·
              refine ⟨1124000582013135475089173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749333721342090316726115 1124000582013135475089173)
              ·
                refine ⟨52687527281865725394805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1124000582013135475089173 52687527281865725394805)
                ·
                  refine ⟨4939455682674911755763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52687527281865725394805 4939455682674911755763)
                  ·
                    rfl

theorem cell21_21644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_21644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21644 prefixEnd_21644 := by exact prefixLift 21644
  have htrace : WordTrace (prefixWord ++ tailWord_21644) baseStart_21644 baseEnd_21644 := by
    simpa [prefixWord, tailWord_21644, baseEnd_21644] using wordTrace_append hprefix tailTrace_21644
  have hstable : (prefixWord ++ tailWord_21644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21644).length < 2 ^ (prefixWord ++ tailWord_21644).sum := by decide
  have hdescent : baseEnd_21644 < baseStart_21644 := by decide
  rcases family_descends (prefixWord ++ tailWord_21644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21692 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_21692 : Nat := 118140960795 + 21692 * 2 ^ 59
def prefixEnd_21692 : Nat := 4983230072969 + 3 ^ 40 * 21692 * 2
def baseEnd_21692 : Nat := 4950409936637494955665

theorem tailTrace_21692 : CollatzResearch.WordTrace tailWord_21692 prefixEnd_21692 4950409936637494955665 := by
  unfold tailWord_21692
  simp only [CollatzResearch.WordTrace]
  refine ⟨395586118710531771881665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 527448158280709029175553 395586118710531771881665)
  ·
    refine ⟨296689589032898828911249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 395586118710531771881665 296689589032898828911249)
    ·
      refine ⟨222517191774674121683437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296689589032898828911249 222517191774674121683437)
      ·
        refine ⟨83443946915502795631289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222517191774674121683437 83443946915502795631289)
        ·
          refine ⟨62582960186627096723467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83443946915502795631289 62582960186627096723467)
          ·
            refine ⟨93874440279940645085201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62582960186627096723467 93874440279940645085201)
            ·
              refine ⟨70405830209955483813901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93874440279940645085201 70405830209955483813901)
              ·
                refine ⟨26402186328733306430213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70405830209955483813901 26402186328733306430213)
                ·
                  refine ⟨4950409936637494955665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26402186328733306430213 4950409936637494955665)
                  ·
                    rfl

theorem cell21_21692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_21692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21692 prefixEnd_21692 := by exact prefixLift 21692
  have htrace : WordTrace (prefixWord ++ tailWord_21692) baseStart_21692 baseEnd_21692 := by
    simpa [prefixWord, tailWord_21692, baseEnd_21692] using wordTrace_append hprefix tailTrace_21692
  have hstable : (prefixWord ++ tailWord_21692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21692).length < 2 ^ (prefixWord ++ tailWord_21692).sum := by decide
  have hdescent : baseEnd_21692 < baseStart_21692 := by decide
  rcases family_descends (prefixWord ++ tailWord_21692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21765 : List Nat := [1, 3, 1, 1, 2, 1, 5, 7]
def baseStart_21765 : Nat := 118140960795 + 21765 * 2 ^ 59
def prefixEnd_21765 : Nat := 4983230072969 + 3 ^ 40 * 21765 * 2
def baseEnd_21765 : Nat := 1655689843735196746283

theorem tailTrace_21765 : CollatzResearch.WordTrace tailWord_21765 prefixEnd_21765 1655689843735196746283 := by
  unfold tailWord_21765
  simp only [CollatzResearch.WordTrace]
  refine ⟨793834766156597011170749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 529223177437731340780499 793834766156597011170749)
  ·
    refine ⟨297688037308723879189031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 793834766156597011170749 297688037308723879189031)
    ·
      refine ⟨446532055963085818783547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297688037308723879189031 446532055963085818783547)
      ·
        refine ⟨669798083944628728175321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446532055963085818783547 669798083944628728175321)
        ·
          refine ⟨502348562958471546131491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669798083944628728175321 502348562958471546131491)
          ·
            refine ⟨753522844437707319197237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502348562958471546131491 753522844437707319197237)
            ·
              refine ⟨70642766666035061174741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 753522844437707319197237 70642766666035061174741)
              ·
                refine ⟨1655689843735196746283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70642766666035061174741 1655689843735196746283)
                ·
                  rfl

theorem cell21_21765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_21765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21765 prefixEnd_21765 := by exact prefixLift 21765
  have htrace : WordTrace (prefixWord ++ tailWord_21765) baseStart_21765 baseEnd_21765 := by
    simpa [prefixWord, tailWord_21765, baseEnd_21765] using wordTrace_append hprefix tailTrace_21765
  have hstable : (prefixWord ++ tailWord_21765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21765).length < 2 ^ (prefixWord ++ tailWord_21765).sum := by decide
  have hdescent : baseEnd_21765 < baseStart_21765 := by decide
  rcases family_descends (prefixWord ++ tailWord_21765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21802 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_21802 : Nat := 118140960795 + 21802 * 2 ^ 59
def prefixEnd_21802 : Nat := 4983230072969 + 3 ^ 40 * 21802 * 2
def baseEnd_21802 : Nat := 4975513435301748122107

theorem tailTrace_21802 : CollatzResearch.WordTrace tailWord_21802 prefixEnd_21802 4975513435301748122107 := by
  unfold tailWord_21802
  simp only [CollatzResearch.WordTrace]
  refine ⟨198796066755638082566915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 530122844681701553511773 198796066755638082566915)
  ·
    refine ⟨298194100133457123850373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198796066755638082566915 298194100133457123850373)
    ·
      refine ⟨55911393775023210721945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298194100133457123850373 55911393775023210721945)
      ·
        refine ⟨41933545331267408041459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55911393775023210721945 41933545331267408041459)
        ·
          refine ⟨62900317996901112062189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41933545331267408041459 62900317996901112062189)
          ·
            refine ⟨23587619248837917023321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62900317996901112062189 23587619248837917023321)
            ·
              refine ⟨17690714436628437767491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23587619248837917023321 17690714436628437767491)
              ·
                refine ⟨26536071654942656651237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17690714436628437767491 26536071654942656651237)
                ·
                  refine ⟨4975513435301748122107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26536071654942656651237 4975513435301748122107)
                  ·
                    rfl

theorem cell21_21802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_21802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21802 prefixEnd_21802 := by exact prefixLift 21802
  have htrace : WordTrace (prefixWord ++ tailWord_21802) baseStart_21802 baseEnd_21802 := by
    simpa [prefixWord, tailWord_21802, baseEnd_21802] using wordTrace_append hprefix tailTrace_21802
  have hstable : (prefixWord ++ tailWord_21802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21802).length < 2 ^ (prefixWord ++ tailWord_21802).sum := by decide
  have hdescent : baseEnd_21802 < baseStart_21802 := by decide
  rcases family_descends (prefixWord ++ tailWord_21802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21844 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_21844 : Nat := 118140960795 + 21844 * 2 ^ 59
def prefixEnd_21844 : Nat := 4983230072969 + 3 ^ 40 * 21844 * 2
def baseEnd_21844 : Nat := 4985098407519008422021

theorem tailTrace_21844 : CollatzResearch.WordTrace tailWord_21844 prefixEnd_21844 4985098407519008422021 := by
  unfold tailWord_21844
  simp only [CollatzResearch.WordTrace]
  refine ⟨398358066435196751648293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 531144088580262335531057 398358066435196751648293)
  ·
    refine ⟨74692137456599390934055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 398358066435196751648293 74692137456599390934055)
    ·
      refine ⟨112038206184899086401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74692137456599390934055 112038206184899086401083)
      ·
        refine ⟨168057309277348629601625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112038206184899086401083 168057309277348629601625)
        ·
          refine ⟨126042981958011472201219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168057309277348629601625 126042981958011472201219)
          ·
            refine ⟨189064472937017208301829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126042981958011472201219 189064472937017208301829)
            ·
              refine ⟨35449588675690726556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189064472937017208301829 35449588675690726556593)
              ·
                refine ⟨26587191506768044917445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35449588675690726556593 26587191506768044917445)
                ·
                  refine ⟨4985098407519008422021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26587191506768044917445 4985098407519008422021)
                  ·
                    rfl

theorem cell21_21844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_21844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21844 prefixEnd_21844 := by exact prefixLift 21844
  have htrace : WordTrace (prefixWord ++ tailWord_21844) baseStart_21844 baseEnd_21844 := by
    simpa [prefixWord, tailWord_21844, baseEnd_21844] using wordTrace_append hprefix tailTrace_21844
  have hstable : (prefixWord ++ tailWord_21844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21844).length < 2 ^ (prefixWord ++ tailWord_21844).sum := by decide
  have hdescent : baseEnd_21844 < baseStart_21844 := by decide
  rcases family_descends (prefixWord ++ tailWord_21844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21847 : List Nat := [1, 1, 3, 2, 3, 4, 2, 2, 3]
def baseStart_21847 : Nat := 118140960795 + 21847 * 2 ^ 59
def prefixEnd_21847 : Nat := 4983230072969 + 3 ^ 40 * 21847 * 2
def baseEnd_21847 : Nat := 4985783048391669872015

theorem tailTrace_21847 : CollatzResearch.WordTrace tailWord_21847 prefixEnd_21847 4985783048391669872015 := by
  unfold tailWord_21847
  simp only [CollatzResearch.WordTrace]
  refine ⟨796825551859525015655795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531217034573016677103863 796825551859525015655795)
  ·
    refine ⟨1195238327789287523483693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796825551859525015655795 1195238327789287523483693)
    ·
      refine ⟨448214372920982821306385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1195238327789287523483693 448214372920982821306385)
      ·
        refine ⟨336160779690737115979789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448214372920982821306385 336160779690737115979789)
        ·
          refine ⟨126060292384026418492421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336160779690737115979789 126060292384026418492421)
          ·
            refine ⟨23636304822004953467329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126060292384026418492421 23636304822004953467329)
            ·
              refine ⟨17727228616503715100497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23636304822004953467329 17727228616503715100497)
              ·
                refine ⟨13295421462377786325373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17727228616503715100497 13295421462377786325373)
                ·
                  refine ⟨4985783048391669872015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13295421462377786325373 4985783048391669872015)
                  ·
                    rfl

theorem cell21_21847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].length) (baseStart_21847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21847 prefixEnd_21847 := by exact prefixLift 21847
  have htrace : WordTrace (prefixWord ++ tailWord_21847) baseStart_21847 baseEnd_21847 := by
    simpa [prefixWord, tailWord_21847, baseEnd_21847] using wordTrace_append hprefix tailTrace_21847
  have hstable : (prefixWord ++ tailWord_21847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21847).length < 2 ^ (prefixWord ++ tailWord_21847).sum := by decide
  have hdescent : baseEnd_21847 < baseStart_21847 := by decide
  rcases family_descends (prefixWord ++ tailWord_21847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21872 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_21872 : Nat := 118140960795 + 21872 * 2 ^ 59
def prefixEnd_21872 : Nat := 4983230072969 + 3 ^ 40 * 21872 * 2
def baseEnd_21872 : Nat := 4991488388997181955297

theorem tailTrace_21872 : CollatzResearch.WordTrace tailWord_21872 prefixEnd_21872 4991488388997181955297 := by
  unfold tailWord_21872
  simp only [CollatzResearch.WordTrace]
  refine ⟨398868688384477142657935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 531824917845969523543913 398868688384477142657935)
  ·
    refine ⟨598303032576715713986903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398868688384477142657935 598303032576715713986903)
    ·
      refine ⟨897454548865073570980355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598303032576715713986903 897454548865073570980355)
      ·
        refine ⟨1346181823297610356470533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897454548865073570980355 1346181823297610356470533)
        ·
          refine ⟨252409091868301941838225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1346181823297610356470533 252409091868301941838225)
          ·
            refine ⟨189306818901226456378669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252409091868301941838225 189306818901226456378669)
            ·
              refine ⟨70990057087959921142001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189306818901226456378669 70990057087959921142001)
              ·
                refine ⟨53242542815969940856501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70990057087959921142001 53242542815969940856501)
                ·
                  refine ⟨4991488388997181955297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53242542815969940856501 4991488388997181955297)
                  ·
                    rfl

theorem cell21_21872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_21872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21872 prefixEnd_21872 := by exact prefixLift 21872
  have htrace : WordTrace (prefixWord ++ tailWord_21872) baseStart_21872 baseEnd_21872 := by
    simpa [prefixWord, tailWord_21872, baseEnd_21872] using wordTrace_append hprefix tailTrace_21872
  have hstable : (prefixWord ++ tailWord_21872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21872).length < 2 ^ (prefixWord ++ tailWord_21872).sum := by decide
  have hdescent : baseEnd_21872 < baseStart_21872 := by decide
  rcases family_descends (prefixWord ++ tailWord_21872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21920 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_21920 : Nat := 118140960795 + 21920 * 2 ^ 59
def prefixEnd_21920 : Nat := 4983230072969 + 3 ^ 40 * 21920 * 2
def baseEnd_21920 : Nat := 5002442642959765155199

theorem tailTrace_21920 : CollatzResearch.WordTrace tailWord_21920 prefixEnd_21920 5002442642959765155199 := by
  unfold tailWord_21920
  simp only [CollatzResearch.WordTrace]
  refine ⟨399744040297529241531607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 532992053730038988708809 399744040297529241531607)
  ·
    refine ⟨599616060446293862297411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399744040297529241531607 599616060446293862297411)
    ·
      refine ⟨899424090669440793446117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599616060446293862297411 899424090669440793446117)
      ·
        refine ⟨168642017000520148771147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 899424090669440793446117 168642017000520148771147)
        ·
          refine ⟨252963025500780223156721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168642017000520148771147 252963025500780223156721)
          ·
            refine ⟨189722269125585167367541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252963025500780223156721 189722269125585167367541)
            ·
              refine ⟨17786462730523609440707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189722269125585167367541 17786462730523609440707)
              ·
                refine ⟨26679694095785414161061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17786462730523609440707 26679694095785414161061)
                ·
                  refine ⟨5002442642959765155199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26679694095785414161061 5002442642959765155199)
                  ·
                    rfl

theorem cell21_21920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_21920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21920 prefixEnd_21920 := by exact prefixLift 21920
  have htrace : WordTrace (prefixWord ++ tailWord_21920) baseStart_21920 baseEnd_21920 := by
    simpa [prefixWord, tailWord_21920, baseEnd_21920] using wordTrace_append hprefix tailTrace_21920
  have hstable : (prefixWord ++ tailWord_21920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21920).length < 2 ^ (prefixWord ++ tailWord_21920).sum := by decide
  have hdescent : baseEnd_21920 < baseStart_21920 := by decide
  rcases family_descends (prefixWord ++ tailWord_21920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21931 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_21931 : Nat := 118140960795 + 21931 * 2 ^ 59
def prefixEnd_21931 : Nat := 4983230072969 + 3 ^ 40 * 21931 * 2
def baseEnd_21931 : Nat := 5004952992826190471843

theorem tailTrace_21931 : CollatzResearch.WordTrace tailWord_21931 prefixEnd_21931 5004952992826190471843 := by
  unfold tailWord_21931
  simp only [CollatzResearch.WordTrace]
  refine ⟨799889283555207361713647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 533259522370138241142431 799889283555207361713647)
  ·
    refine ⟨1199833925332811042570471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799889283555207361713647 1199833925332811042570471)
    ·
      refine ⟨1799750887999216563855707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199833925332811042570471 1799750887999216563855707)
      ·
        refine ⟨2699626331998824845783561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799750887999216563855707 2699626331998824845783561)
        ·
          refine ⟨2024719748999118634337671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2699626331998824845783561 2024719748999118634337671)
          ·
            refine ⟨3037079623498677951506507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024719748999118634337671 3037079623498677951506507)
            ·
              refine ⟨4555619435248016927259761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037079623498677951506507 4555619435248016927259761)
              ·
                refine ⟨3416714576436012695444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555619435248016927259761 3416714576436012695444821)
                ·
                  refine ⟨5004952992826190471843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 3416714576436012695444821 5004952992826190471843)
                  ·
                    rfl

theorem cell21_21931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_21931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_21931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_21931 prefixEnd_21931 := by exact prefixLift 21931
  have htrace : WordTrace (prefixWord ++ tailWord_21931) baseStart_21931 baseEnd_21931 := by
    simpa [prefixWord, tailWord_21931, baseEnd_21931] using wordTrace_append hprefix tailTrace_21931
  have hstable : (prefixWord ++ tailWord_21931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21931).length < 2 ^ (prefixWord ++ tailWord_21931).sum := by decide
  have hdescent : baseEnd_21931 < baseStart_21931 := by decide
  rcases family_descends (prefixWord ++ tailWord_21931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22007 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_22007 : Nat := 118140960795 + 22007 * 2 ^ 59
def prefixEnd_22007 : Nat := 4983230072969 + 3 ^ 40 * 22007 * 2
def baseEnd_22007 : Nat := 5022297228266947205021

theorem tailTrace_22007 : CollatzResearch.WordTrace tailWord_22007 prefixEnd_22007 5022297228266947205021 := by
  unfold tailWord_22007
  simp only [CollatzResearch.WordTrace]
  refine ⟨802661231279872341480275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 535107487519914894320183 802661231279872341480275)
  ·
    refine ⟨1203991846919808512220413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802661231279872341480275 1203991846919808512220413)
    ·
      refine ⟨451496942594928192082655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1203991846919808512220413 451496942594928192082655)
      ·
        refine ⟨677245413892392288123983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451496942594928192082655 677245413892392288123983)
        ·
          refine ⟨1015868120838588432185975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677245413892392288123983 1015868120838588432185975)
          ·
            refine ⟨1523802181257882648278963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015868120838588432185975 1523802181257882648278963)
            ·
              refine ⟨2285703271886823972418445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523802181257882648278963 2285703271886823972418445)
              ·
                refine ⟨857138726957558989656917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285703271886823972418445 857138726957558989656917)
                ·
                  refine ⟨5022297228266947205021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 857138726957558989656917 5022297228266947205021)
                  ·
                    rfl

theorem cell21_22007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_22007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22007 prefixEnd_22007 := by exact prefixLift 22007
  have htrace : WordTrace (prefixWord ++ tailWord_22007) baseStart_22007 baseEnd_22007 := by
    simpa [prefixWord, tailWord_22007, baseEnd_22007] using wordTrace_append hprefix tailTrace_22007
  have hstable : (prefixWord ++ tailWord_22007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22007).length < 2 ^ (prefixWord ++ tailWord_22007).sum := by decide
  have hdescent : baseEnd_22007 < baseStart_22007 := by decide
  rcases family_descends (prefixWord ++ tailWord_22007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22027 : List Nat := [1, 1, 1, 1, 9, 1, 1, 6]
def baseStart_22027 : Nat := 118140960795 + 22027 * 2 ^ 59
def prefixEnd_22027 : Nat := 4983230072969 + 3 ^ 40 * 22027 * 2
def baseEnd_22027 : Nat := 1675620500250452290549

theorem tailTrace_22027 : CollatzResearch.WordTrace tailWord_22027 prefixEnd_22027 1675620500250452290549 := by
  unfold tailWord_22027
  simp only [CollatzResearch.WordTrace]
  refine ⟨803390691207415757208335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 535593794138277171472223 803390691207415757208335)
  ·
    refine ⟨1205086036811123635812503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 803390691207415757208335 1205086036811123635812503)
    ·
      refine ⟨1807629055216685453718755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205086036811123635812503 1807629055216685453718755)
      ·
        refine ⟨2711443582825028180578133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807629055216685453718755 2711443582825028180578133)
        ·
          refine ⟨15887364743115399495575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 2711443582825028180578133 15887364743115399495575)
          ·
            refine ⟨23831047114673099243363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15887364743115399495575 23831047114673099243363)
            ·
              refine ⟨35746570672009648865045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23831047114673099243363 35746570672009648865045)
              ·
                refine ⟨1675620500250452290549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35746570672009648865045 1675620500250452290549)
                ·
                  rfl

theorem cell21_22027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].length) (baseStart_22027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22027 prefixEnd_22027 := by exact prefixLift 22027
  have htrace : WordTrace (prefixWord ++ tailWord_22027) baseStart_22027 baseEnd_22027 := by
    simpa [prefixWord, tailWord_22027, baseEnd_22027] using wordTrace_append hprefix tailTrace_22027
  have hstable : (prefixWord ++ tailWord_22027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22027).length < 2 ^ (prefixWord ++ tailWord_22027).sum := by decide
  have hdescent : baseEnd_22027 < baseStart_22027 := by decide
  rcases family_descends (prefixWord ++ tailWord_22027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22058 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_22058 : Nat := 118140960795 + 22058 * 2 ^ 59
def prefixEnd_22058 : Nat := 4983230072969 + 3 ^ 40 * 22058 * 2
def baseEnd_22058 : Nat := 5033936123102191854917

theorem tailTrace_22058 : CollatzResearch.WordTrace tailWord_22058 prefixEnd_22058 5033936123102191854917 := by
  unfold tailWord_22058
  simp only [CollatzResearch.WordTrace]
  refine ⟨201130338523777012896707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 536347569396738701057885 201130338523777012896707)
  ·
    refine ⟨301695507785665519345061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201130338523777012896707 301695507785665519345061)
    ·
      refine ⟨56567907709812284877199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301695507785665519345061 56567907709812284877199)
      ·
        refine ⟨84851861564718427315799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56567907709812284877199 84851861564718427315799)
        ·
          refine ⟨127277792347077640973699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84851861564718427315799 127277792347077640973699)
          ·
            refine ⟨190916688520616461460549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127277792347077640973699 190916688520616461460549)
            ·
              refine ⟨35796879097615586523853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190916688520616461460549 35796879097615586523853)
              ·
                refine ⟨13423829661605844946445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35796879097615586523853 13423829661605844946445)
                ·
                  refine ⟨5033936123102191854917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13423829661605844946445 5033936123102191854917)
                  ·
                    rfl

theorem cell21_22058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_22058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22058 prefixEnd_22058 := by exact prefixLift 22058
  have htrace : WordTrace (prefixWord ++ tailWord_22058) baseStart_22058 baseEnd_22058 := by
    simpa [prefixWord, tailWord_22058, baseEnd_22058] using wordTrace_append hprefix tailTrace_22058
  have hstable : (prefixWord ++ tailWord_22058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22058).length < 2 ^ (prefixWord ++ tailWord_22058).sum := by decide
  have hdescent : baseEnd_22058 < baseStart_22058 := by decide
  rcases family_descends (prefixWord ++ tailWord_22058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22069 : List Nat := [1, 3, 3, 1, 1, 4, 8]
def baseStart_22069 : Nat := 118140960795 + 22069 * 2 ^ 59
def prefixEnd_22069 : Nat := 4983230072969 + 3 ^ 40 * 22069 * 2
def baseEnd_22069 : Nat := 559605163663179685729

theorem tailTrace_22069 : CollatzResearch.WordTrace tailWord_22069 prefixEnd_22069 559605163663179685729 := by
  unfold tailWord_22069
  simp only [CollatzResearch.WordTrace]
  refine ⟨804922557055256930237261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 536615038036837953491507 804922557055256930237261)
  ·
    refine ⟨301845958895721348838973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 804922557055256930237261 301845958895721348838973)
    ·
      refine ⟨113192234585895505814615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301845958895721348838973 113192234585895505814615)
      ·
        refine ⟨169788351878843258721923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113192234585895505814615 169788351878843258721923)
        ·
          refine ⟨254682527818264888082885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169788351878843258721923 254682527818264888082885)
          ·
            refine ⟨47752973965924666515541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254682527818264888082885 47752973965924666515541)
            ·
              refine ⟨559605163663179685729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 47752973965924666515541 559605163663179685729)
              ·
                rfl

theorem cell21_22069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 8].length) (baseStart_22069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22069 prefixEnd_22069 := by exact prefixLift 22069
  have htrace : WordTrace (prefixWord ++ tailWord_22069) baseStart_22069 baseEnd_22069 := by
    simpa [prefixWord, tailWord_22069, baseEnd_22069] using wordTrace_append hprefix tailTrace_22069
  have hstable : (prefixWord ++ tailWord_22069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22069).length < 2 ^ (prefixWord ++ tailWord_22069).sum := by decide
  have hdescent : baseEnd_22069 < baseStart_22069 := by decide
  rcases family_descends (prefixWord ++ tailWord_22069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22072 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_22072 : Nat := 118140960795 + 22072 * 2 ^ 59
def prefixEnd_22072 : Nat := 4983230072969 + 3 ^ 40 * 22072 * 2
def baseEnd_22072 : Nat := 5037131113841278621555

theorem tailTrace_22072 : CollatzResearch.WordTrace tailWord_22072 prefixEnd_22072 5037131113841278621555 := by
  unfold tailWord_22072
  simp only [CollatzResearch.WordTrace]
  refine ⟨402515988022194221298235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 536687984029592295064313 402515988022194221298235)
  ·
    refine ⟨603773982033291331947353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402515988022194221298235 603773982033291331947353)
    ·
      refine ⟨452830486524968498960515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 603773982033291331947353 452830486524968498960515)
      ·
        refine ⟨679245729787452748440773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452830486524968498960515 679245729787452748440773)
        ·
          refine ⟨127358574335147390332645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 679245729787452748440773 127358574335147390332645)
          ·
            refine ⟨23879732687840135687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127358574335147390332645 23879732687840135687371)
            ·
              refine ⟨35819599031760203531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23879732687840135687371 35819599031760203531057)
              ·
                refine ⟨26864699273820152648293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35819599031760203531057 26864699273820152648293)
                ·
                  refine ⟨5037131113841278621555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26864699273820152648293 5037131113841278621555)
                  ·
                    rfl

theorem cell21_22072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_22072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22072 prefixEnd_22072 := by exact prefixLift 22072
  have htrace : WordTrace (prefixWord ++ tailWord_22072) baseStart_22072 baseEnd_22072 := by
    simpa [prefixWord, tailWord_22072, baseEnd_22072] using wordTrace_append hprefix tailTrace_22072
  have hstable : (prefixWord ++ tailWord_22072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22072).length < 2 ^ (prefixWord ++ tailWord_22072).sum := by decide
  have hdescent : baseEnd_22072 < baseStart_22072 := by decide
  rcases family_descends (prefixWord ++ tailWord_22072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22100 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_22100 : Nat := 118140960795 + 22100 * 2 ^ 59
def prefixEnd_22100 : Nat := 4983230072969 + 3 ^ 40 * 22100 * 2
def baseEnd_22100 : Nat := 5043521095319452154831

theorem tailTrace_22100 : CollatzResearch.WordTrace tailWord_22100 prefixEnd_22100 5043521095319452154831 := by
  unfold tailWord_22100
  simp only [CollatzResearch.WordTrace]
  refine ⟨403026609971474612307877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 537368813295299483077169 403026609971474612307877)
  ·
    refine ⟨75567489369651489807727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 403026609971474612307877 75567489369651489807727)
    ·
      refine ⟨113351234054477234711591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75567489369651489807727 113351234054477234711591)
      ·
        refine ⟨170026851081715852067387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113351234054477234711591 170026851081715852067387)
        ·
          refine ⟨255040276622573778101081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170026851081715852067387 255040276622573778101081)
          ·
            refine ⟨191280207466930333575811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255040276622573778101081 191280207466930333575811)
            ·
              refine ⟨286920311200395500363717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191280207466930333575811 286920311200395500363717)
              ·
                refine ⟨53797558350074156318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286920311200395500363717 53797558350074156318197)
                ·
                  refine ⟨5043521095319452154831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53797558350074156318197 5043521095319452154831)
                  ·
                    rfl

theorem cell21_22100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_22100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22100 prefixEnd_22100 := by exact prefixLift 22100
  have htrace : WordTrace (prefixWord ++ tailWord_22100) baseStart_22100 baseEnd_22100 := by
    simpa [prefixWord, tailWord_22100, baseEnd_22100] using wordTrace_append hprefix tailTrace_22100
  have hstable : (prefixWord ++ tailWord_22100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22100).length < 2 ^ (prefixWord ++ tailWord_22100).sum := by decide
  have hdescent : baseEnd_22100 < baseStart_22100 := by decide
  rcases family_descends (prefixWord ++ tailWord_22100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22109 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 3]
def baseStart_22109 : Nat := 118140960795 + 22109 * 2 ^ 59
def prefixEnd_22109 : Nat := 4983230072969 + 3 ^ 40 * 22109 * 2
def baseEnd_22109 : Nat := 5045575017937436504813

theorem tailTrace_22109 : CollatzResearch.WordTrace tailWord_22109 prefixEnd_22109 5045575017937436504813 := by
  unfold tailWord_22109
  simp only [CollatzResearch.WordTrace]
  refine ⟨806381476910343761693381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 537587651273562507795587 806381476910343761693381)
  ·
    refine ⟨151196526920689455317509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 806381476910343761693381 151196526920689455317509)
    ·
      refine ⟨28349348797629272872033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151196526920689455317509 28349348797629272872033)
      ·
        refine ⟨21262011598221954654025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28349348797629272872033 21262011598221954654025)
        ·
          refine ⟨15946508698666465990519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21262011598221954654025 15946508698666465990519)
          ·
            refine ⟨23919763047999698985779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15946508698666465990519 23919763047999698985779)
            ·
              refine ⟨35879644571999548478669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23919763047999698985779 35879644571999548478669)
              ·
                refine ⟨13454866714499830679501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35879644571999548478669 13454866714499830679501)
                ·
                  refine ⟨5045575017937436504813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13454866714499830679501 5045575017937436504813)
                  ·
                    rfl

theorem cell21_22109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_22109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22109 prefixEnd_22109 := by exact prefixLift 22109
  have htrace : WordTrace (prefixWord ++ tailWord_22109) baseStart_22109 baseEnd_22109 := by
    simpa [prefixWord, tailWord_22109, baseEnd_22109] using wordTrace_append hprefix tailTrace_22109
  have hstable : (prefixWord ++ tailWord_22109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22109).length < 2 ^ (prefixWord ++ tailWord_22109).sum := by decide
  have hdescent : baseEnd_22109 < baseStart_22109 := by decide
  rcases family_descends (prefixWord ++ tailWord_22109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22134 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_22134 : Nat := 118140960795 + 22134 * 2 ^ 59
def prefixEnd_22134 : Nat := 4983230072969 + 3 ^ 40 * 22134 * 2
def baseEnd_22134 : Nat := 5051280358542948588095

theorem tailTrace_22134 : CollatzResearch.WordTrace tailWord_22134 prefixEnd_22134 5051280358542948588095 := by
  unfold tailWord_22134
  simp only [CollatzResearch.WordTrace]
  refine ⟨50455831363735814459591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 538195534546515354235637 50455831363735814459591)
  ·
    refine ⟨75683747045603721689387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50455831363735814459591 75683747045603721689387)
    ·
      refine ⟨113525620568405582534081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75683747045603721689387 113525620568405582534081)
      ·
        refine ⟨85144215426304186900561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113525620568405582534081 85144215426304186900561)
        ·
          refine ⟨63858161569728140175421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85144215426304186900561 63858161569728140175421)
          ·
            refine ⟨23946810588648052565783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63858161569728140175421 23946810588648052565783)
            ·
              refine ⟨35920215882972078848675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23946810588648052565783 35920215882972078848675)
              ·
                refine ⟨53880323824458118273013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35920215882972078848675 53880323824458118273013)
                ·
                  refine ⟨5051280358542948588095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53880323824458118273013 5051280358542948588095)
                  ·
                    rfl

theorem cell21_22134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_22134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22134 prefixEnd_22134 := by exact prefixLift 22134
  have htrace : WordTrace (prefixWord ++ tailWord_22134) baseStart_22134 baseEnd_22134 := by
    simpa [prefixWord, tailWord_22134, baseEnd_22134] using wordTrace_append hprefix tailTrace_22134
  have hstable : (prefixWord ++ tailWord_22134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22134).length < 2 ^ (prefixWord ++ tailWord_22134).sum := by decide
  have hdescent : baseEnd_22134 < baseStart_22134 := by decide
  rcases family_descends (prefixWord ++ tailWord_22134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22145 : List Nat := [1, 2, 4, 2, 1, 2, 1, 8]
def baseStart_22145 : Nat := 118140960795 + 22145 * 2 ^ 59
def prefixEnd_22145 : Nat := 4983230072969 + 3 ^ 40 * 22145 * 2
def baseEnd_22145 : Nat := 1684596902803124634913

theorem tailTrace_22145 : CollatzResearch.WordTrace tailWord_22145 prefixEnd_22145 1684596902803124634913 := by
  unfold tailWord_22145
  simp only [CollatzResearch.WordTrace]
  refine ⟨807694504779921910003889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 538463003186614606669259 807694504779921910003889)
  ·
    refine ⟨605770878584941432502917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 807694504779921910003889 605770878584941432502917)
    ·
      refine ⟨113582039734676518594297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 605770878584941432502917 113582039734676518594297)
      ·
        refine ⟨85186529801007388945723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113582039734676518594297 85186529801007388945723)
        ·
          refine ⟨127779794701511083418585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85186529801007388945723 127779794701511083418585)
          ·
            refine ⟨95834846026133312563939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127779794701511083418585 95834846026133312563939)
            ·
              refine ⟨143752269039199968845909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95834846026133312563939 143752269039199968845909)
              ·
                refine ⟨1684596902803124634913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 143752269039199968845909 1684596902803124634913)
                ·
                  rfl

theorem cell21_22145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_22145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22145 prefixEnd_22145 := by exact prefixLift 22145
  have htrace : WordTrace (prefixWord ++ tailWord_22145) baseStart_22145 baseEnd_22145 := by
    simpa [prefixWord, tailWord_22145, baseEnd_22145] using wordTrace_append hprefix tailTrace_22145
  have hstable : (prefixWord ++ tailWord_22145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22145).length < 2 ^ (prefixWord ++ tailWord_22145).sum := by decide
  have hdescent : baseEnd_22145 < baseStart_22145 := by decide
  rcases family_descends (prefixWord ++ tailWord_22145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22148 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_22148 : Nat := 118140960795 + 22148 * 2 ^ 59
def prefixEnd_22148 : Nat := 4983230072969 + 3 ^ 40 * 22148 * 2
def baseEnd_22148 : Nat := 5054475349282035354733

theorem tailTrace_22148 : CollatzResearch.WordTrace tailWord_22148 prefixEnd_22148 5054475349282035354733 := by
  unfold tailWord_22148
  simp only [CollatzResearch.WordTrace]
  refine ⟨403901961884526711181549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 538535949179368948242065 403901961884526711181549)
  ·
    refine ⟨151463235706697516693081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 403901961884526711181549 151463235706697516693081)
    ·
      refine ⟨113597426780023137519811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151463235706697516693081 113597426780023137519811)
      ·
        refine ⟨170396140170034706279717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113597426780023137519811 170396140170034706279717)
        ·
          refine ⟨31949276281881507427447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170396140170034706279717 31949276281881507427447)
          ·
            refine ⟨47923914422822261141171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31949276281881507427447 47923914422822261141171)
            ·
              refine ⟨71885871634233391711757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47923914422822261141171 71885871634233391711757)
              ·
                refine ⟨26957201862837521891909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71885871634233391711757 26957201862837521891909)
                ·
                  refine ⟨5054475349282035354733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26957201862837521891909 5054475349282035354733)
                  ·
                    rfl

theorem cell21_22148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_22148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22148 prefixEnd_22148 := by exact prefixLift 22148
  have htrace : WordTrace (prefixWord ++ tailWord_22148) baseStart_22148 baseEnd_22148 := by
    simpa [prefixWord, tailWord_22148, baseEnd_22148] using wordTrace_append hprefix tailTrace_22148
  have hstable : (prefixWord ++ tailWord_22148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22148).length < 2 ^ (prefixWord ++ tailWord_22148).sum := by decide
  have hdescent : baseEnd_22148 < baseStart_22148 := by decide
  rcases family_descends (prefixWord ++ tailWord_22148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22241 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 4]
def baseStart_22241 : Nat := 118140960795 + 22241 * 2 ^ 59
def prefixEnd_22241 : Nat := 4983230072969 + 3 ^ 40 * 22241 * 2
def baseEnd_22241 : Nat := 5075699216334540304543

theorem tailTrace_22241 : CollatzResearch.WordTrace tailWord_22241 prefixEnd_22241 5075699216334540304543 := by
  unfold tailWord_22241
  simp only [CollatzResearch.WordTrace]
  refine ⟨811195912432130305498577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540797274954753536999051 811195912432130305498577)
  ·
    refine ⟨608396934324097729123933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 811195912432130305498577 608396934324097729123933)
    ·
      refine ⟨228148850371536648421475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 608396934324097729123933 228148850371536648421475)
      ·
        refine ⟨342223275557304972632213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228148850371536648421475 342223275557304972632213)
        ·
          refine ⟨16041716041748670592135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 342223275557304972632213 16041716041748670592135)
          ·
            refine ⟨24062574062623005888203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16041716041748670592135 24062574062623005888203)
            ·
              refine ⟨36093861093934508832305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24062574062623005888203 36093861093934508832305)
              ·
                refine ⟨27070395820450881624229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36093861093934508832305 27070395820450881624229)
                ·
                  refine ⟨5075699216334540304543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27070395820450881624229 5075699216334540304543)
                  ·
                    rfl

theorem cell21_22241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_22241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22241 prefixEnd_22241 := by exact prefixLift 22241
  have htrace : WordTrace (prefixWord ++ tailWord_22241) baseStart_22241 baseEnd_22241 := by
    simpa [prefixWord, tailWord_22241, baseEnd_22241] using wordTrace_append hprefix tailTrace_22241
  have hstable : (prefixWord ++ tailWord_22241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22241).length < 2 ^ (prefixWord ++ tailWord_22241).sum := by decide
  have hdescent : baseEnd_22241 < baseStart_22241 := by decide
  rcases family_descends (prefixWord ++ tailWord_22241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22432 : List Nat := [2, 1, 1, 4, 1, 1, 1, 10]
def baseStart_22432 : Nat := 118140960795 + 22432 * 2 ^ 59
def prefixEnd_22432 : Nat := 4983230072969 + 3 ^ 40 * 22432 * 2
def baseEnd_22432 : Nat := 1706429339520217540273

theorem tailTrace_22432 : CollatzResearch.WordTrace tailWord_22432 prefixEnd_22432 1706429339520217540273 := by
  unfold tailWord_22432
  simp only [CollatzResearch.WordTrace]
  refine ⟨409081127370084962850775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 545441503160113283801033 409081127370084962850775)
  ·
    refine ⟨613621691055127444276163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409081127370084962850775 613621691055127444276163)
    ·
      refine ⟨920432536582691166414245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613621691055127444276163 920432536582691166414245)
      ·
        refine ⟨172581100609254593702671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 920432536582691166414245 172581100609254593702671)
        ·
          refine ⟨258871650913881890554007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172581100609254593702671 258871650913881890554007)
          ·
            refine ⟨388307476370822835831011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258871650913881890554007 388307476370822835831011)
            ·
              refine ⟨582461214556234253746517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388307476370822835831011 582461214556234253746517)
              ·
                refine ⟨1706429339520217540273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 582461214556234253746517 1706429339520217540273)
                ·
                  rfl

theorem cell21_22432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_22432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22432 prefixEnd_22432 := by exact prefixLift 22432
  have htrace : WordTrace (prefixWord ++ tailWord_22432) baseStart_22432 baseEnd_22432 := by
    simpa [prefixWord, tailWord_22432, baseEnd_22432] using wordTrace_append hprefix tailTrace_22432
  have hstable : (prefixWord ++ tailWord_22432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22432).length < 2 ^ (prefixWord ++ tailWord_22432).sum := by decide
  have hdescent : baseEnd_22432 < baseStart_22432 := by decide
  rcases family_descends (prefixWord ++ tailWord_22432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22449 : List Nat := [1, 2, 2, 4, 2, 2, 1, 7]
def baseStart_22449 : Nat := 118140960795 + 22449 * 2 ^ 59
def prefixEnd_22449 : Nat := 4983230072969 + 3 ^ 40 * 22449 * 2
def baseEnd_22449 : Nat := 1707722550057466945817

theorem tailTrace_22449 : CollatzResearch.WordTrace tailWord_22449 prefixEnd_22449 1707722550057466945817 := by
  unfold tailWord_22449
  simp only [CollatzResearch.WordTrace]
  refine ⟨818782295678581829070401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 545854863785721219380267 818782295678581829070401)
  ·
    refine ⟨614086721758936371802801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 818782295678581829070401 614086721758936371802801)
    ·
      refine ⟨460565041319202278852101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 614086721758936371802801 460565041319202278852101)
      ·
        refine ⟨86355945247350427284769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 460565041319202278852101 86355945247350427284769)
        ·
          refine ⟨64766958935512820463577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86355945247350427284769 64766958935512820463577)
          ·
            refine ⟨48575219201634615347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64766958935512820463577 48575219201634615347683)
            ·
              refine ⟨72862828802451923021525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48575219201634615347683 72862828802451923021525)
              ·
                refine ⟨1707722550057466945817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72862828802451923021525 1707722550057466945817)
                ·
                  rfl

theorem cell21_22449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_22449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22449 prefixEnd_22449 := by exact prefixLift 22449
  have htrace : WordTrace (prefixWord ++ tailWord_22449) baseStart_22449 baseEnd_22449 := by
    simpa [prefixWord, tailWord_22449, baseEnd_22449] using wordTrace_append hprefix tailTrace_22449
  have hstable : (prefixWord ++ tailWord_22449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22449).length < 2 ^ (prefixWord ++ tailWord_22449).sum := by decide
  have hdescent : baseEnd_22449 < baseStart_22449 := by decide
  rcases family_descends (prefixWord ++ tailWord_22449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22480 : List Nat := [2, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_22480 : Nat := 118140960795 + 22480 * 2 ^ 59
def prefixEnd_22480 : Nat := 4983230072969 + 3 ^ 40 * 22480 * 2
def baseEnd_22480 : Nat := 5130242272523235820721

theorem tailTrace_22480 : CollatzResearch.WordTrace tailWord_22480 prefixEnd_22480 5130242272523235820721 := by
  unfold tailWord_22480
  simp only [CollatzResearch.WordTrace]
  refine ⟨409956479283137061724447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 546608639044182748965929 409956479283137061724447)
  ·
    refine ⟨614934718924705592586671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409956479283137061724447 614934718924705592586671)
    ·
      refine ⟨922402078387058388880007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614934718924705592586671 922402078387058388880007)
      ·
        refine ⟨1383603117580587583320011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922402078387058388880007 1383603117580587583320011)
        ·
          refine ⟨2075404676370881374980017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383603117580587583320011 2075404676370881374980017)
          ·
            refine ⟨1556553507278161031235013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075404676370881374980017 1556553507278161031235013)
            ·
              refine ⟨291853782614655193356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1556553507278161031235013 291853782614655193356565)
              ·
                refine ⟨13680646060061962188589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291853782614655193356565 13680646060061962188589)
                ·
                  refine ⟨5130242272523235820721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13680646060061962188589 5130242272523235820721)
                  ·
                    rfl

theorem cell21_22480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_22480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22480 prefixEnd_22480 := by exact prefixLift 22480
  have htrace : WordTrace (prefixWord ++ tailWord_22480) baseStart_22480 baseEnd_22480 := by
    simpa [prefixWord, tailWord_22480, baseEnd_22480] using wordTrace_append hprefix tailTrace_22480
  have hstable : (prefixWord ++ tailWord_22480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22480).length < 2 ^ (prefixWord ++ tailWord_22480).sum := by decide
  have hdescent : baseEnd_22480 < baseStart_22480 := by decide
  rcases family_descends (prefixWord ++ tailWord_22480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22486 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_22486 : Nat := 118140960795 + 22486 * 2 ^ 59
def prefixEnd_22486 : Nat := 4983230072969 + 3 ^ 40 * 22486 * 2
def baseEnd_22486 : Nat := 5131611554268558720709

theorem tailTrace_22486 : CollatzResearch.WordTrace tailWord_22486 prefixEnd_22486 5131611554268558720709 := by
  unfold tailWord_22486
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258237284033571760457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 546754531029691432111541 51258237284033571760457)
  ·
    refine ⟨38443677963025178820343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51258237284033571760457 38443677963025178820343)
    ·
      refine ⟨57665516944537768230515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38443677963025178820343 57665516944537768230515)
      ·
        refine ⟨86498275416806652345773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57665516944537768230515 86498275416806652345773)
        ·
          refine ⟨32436853281302494629665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86498275416806652345773 32436853281302494629665)
          ·
            refine ⟨24327639960976870972249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32436853281302494629665 24327639960976870972249)
            ·
              refine ⟨18245729970732653229187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24327639960976870972249 18245729970732653229187)
              ·
                refine ⟨27368594956098979843781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18245729970732653229187 27368594956098979843781)
                ·
                  refine ⟨5131611554268558720709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27368594956098979843781 5131611554268558720709)
                  ·
                    rfl

theorem cell21_22486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_22486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22486 prefixEnd_22486 := by exact prefixLift 22486
  have htrace : WordTrace (prefixWord ++ tailWord_22486) baseStart_22486 baseEnd_22486 := by
    simpa [prefixWord, tailWord_22486, baseEnd_22486] using wordTrace_append hprefix tailTrace_22486
  have hstable : (prefixWord ++ tailWord_22486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22486).length < 2 ^ (prefixWord ++ tailWord_22486).sum := by decide
  have hdescent : baseEnd_22486 < baseStart_22486 := by decide
  rcases family_descends (prefixWord ++ tailWord_22486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22534 : List Nat := [6, 2, 1, 2, 2, 1, 1, 6]
def baseStart_22534 : Nat := 118140960795 + 22534 * 2 ^ 59
def prefixEnd_22534 : Nat := 4983230072969 + 3 ^ 40 * 22534 * 2
def baseEnd_22534 : Nat := 1714188602743713973537

theorem tailTrace_22534 : CollatzResearch.WordTrace tailWord_22534 prefixEnd_22534 1714188602743713973537 := by
  unfold tailWord_22534
  simp only [CollatzResearch.WordTrace]
  refine ⟨25683828136582542059833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 547921666913760897276437 25683828136582542059833)
  ·
    refine ⟨19262871102436906544875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25683828136582542059833 19262871102436906544875)
    ·
      refine ⟨28894306653655359817313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19262871102436906544875 28894306653655359817313)
      ·
        refine ⟨21670729990241519862985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28894306653655359817313 21670729990241519862985)
        ·
          refine ⟨16253047492681139897239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21670729990241519862985 16253047492681139897239)
          ·
            refine ⟨24379571239021709845859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253047492681139897239 24379571239021709845859)
            ·
              refine ⟨36569356858532564768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24379571239021709845859 36569356858532564768789)
              ·
                refine ⟨1714188602743713973537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36569356858532564768789 1714188602743713973537)
                ·
                  rfl

theorem cell21_22534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_22534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22534 prefixEnd_22534 := by exact prefixLift 22534
  have htrace : WordTrace (prefixWord ++ tailWord_22534) baseStart_22534 baseEnd_22534 := by
    simpa [prefixWord, tailWord_22534, baseEnd_22534] using wordTrace_append hprefix tailTrace_22534
  have hstable : (prefixWord ++ tailWord_22534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22534).length < 2 ^ (prefixWord ++ tailWord_22534).sum := by decide
  have hdescent : baseEnd_22534 < baseStart_22534 := by decide
  rcases family_descends (prefixWord ++ tailWord_22534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22539 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_22539 : Nat := 118140960795 + 22539 * 2 ^ 59
def prefixEnd_22539 : Nat := 4983230072969 + 3 ^ 40 * 22539 * 2
def baseEnd_22539 : Nat := 5143706876352244337267

theorem tailTrace_22539 : CollatzResearch.WordTrace tailWord_22539 prefixEnd_22539 5143706876352244337267 := by
  unfold tailWord_22539
  simp only [CollatzResearch.WordTrace]
  refine ⟨822064865352527199846671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 548043243568351466564447 822064865352527199846671)
  ·
    refine ⟨1233097298028790799770007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822064865352527199846671 1233097298028790799770007)
    ·
      refine ⟨1849645947043186199655011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1233097298028790799770007 1849645947043186199655011)
      ·
        refine ⟨2774468920564779299482517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849645947043186199655011 2774468920564779299482517)
        ·
          refine ⟨130053230651474029663243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2774468920564779299482517 130053230651474029663243)
          ·
            refine ⟨195079845977211044494865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130053230651474029663243 195079845977211044494865)
            ·
              refine ⟨146309884482908283371149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195079845977211044494865 146309884482908283371149)
              ·
                refine ⟨54866206681090606264181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146309884482908283371149 54866206681090606264181)
                ·
                  refine ⟨5143706876352244337267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54866206681090606264181 5143706876352244337267)
                  ·
                    rfl

theorem cell21_22539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_22539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22539 prefixEnd_22539 := by exact prefixLift 22539
  have htrace : WordTrace (prefixWord ++ tailWord_22539) baseStart_22539 baseEnd_22539 := by
    simpa [prefixWord, tailWord_22539, baseEnd_22539] using wordTrace_append hprefix tailTrace_22539
  have hstable : (prefixWord ++ tailWord_22539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22539).length < 2 ^ (prefixWord ++ tailWord_22539).sum := by decide
  have hdescent : baseEnd_22539 < baseStart_22539 := by decide
  rcases family_descends (prefixWord ++ tailWord_22539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22553 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_22553 : Nat := 118140960795 + 22553 * 2 ^ 59
def prefixEnd_22553 : Nat := 4983230072969 + 3 ^ 40 * 22553 * 2
def baseEnd_22553 : Nat := 5146901867091331103905

theorem tailTrace_22553 : CollatzResearch.WordTrace tailWord_22553 prefixEnd_22553 5146901867091331103905 := by
  unfold tailWord_22553
  simp only [CollatzResearch.WordTrace]
  refine ⟨822575487301807590856313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 548383658201205060570875 822575487301807590856313)
  ·
    refine ⟨616931615476355693142235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 822575487301807590856313 616931615476355693142235)
    ·
      refine ⟨925397423214533539713353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616931615476355693142235 925397423214533539713353)
      ·
        refine ⟨694048067410900154785015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 925397423214533539713353 694048067410900154785015)
        ·
          refine ⟨1041072101116350232177523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694048067410900154785015 1041072101116350232177523)
          ·
            refine ⟨1561608151674525348266285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041072101116350232177523 1561608151674525348266285)
            ·
              refine ⟨585603056877947005599857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561608151674525348266285 585603056877947005599857)
              ·
                refine ⟨439202292658460254199893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585603056877947005599857 439202292658460254199893)
                ·
                  refine ⟨5146901867091331103905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 439202292658460254199893 5146901867091331103905)
                  ·
                    rfl

theorem cell21_22553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_22553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22553 prefixEnd_22553 := by exact prefixLift 22553
  have htrace : WordTrace (prefixWord ++ tailWord_22553) baseStart_22553 baseEnd_22553 := by
    simpa [prefixWord, tailWord_22553, baseEnd_22553] using wordTrace_append hprefix tailTrace_22553
  have hstable : (prefixWord ++ tailWord_22553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22553).length < 2 ^ (prefixWord ++ tailWord_22553).sum := by decide
  have hdescent : baseEnd_22553 < baseStart_22553 := by decide
  rcases family_descends (prefixWord ++ tailWord_22553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22556 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_22556 : Nat := 118140960795 + 22556 * 2 ^ 59
def prefixEnd_22556 : Nat := 4983230072969 + 3 ^ 40 * 22556 * 2
def baseEnd_22556 : Nat := 5147586507963992553899

theorem tailTrace_22556 : CollatzResearch.WordTrace tailWord_22556 prefixEnd_22556 5147586507963992553899 := by
  unfold tailWord_22556
  simp only [CollatzResearch.WordTrace]
  refine ⟨411342453145469551607761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 548456604193959402143681 411342453145469551607761)
  ·
    refine ⟨308506839859102163705821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 411342453145469551607761 308506839859102163705821)
    ·
      refine ⟨115690064947163311389683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308506839859102163705821 115690064947163311389683)
      ·
        refine ⟨173535097420744967084525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115690064947163311389683 173535097420744967084525)
        ·
          refine ⟨65075661532779362656697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173535097420744967084525 65075661532779362656697)
          ·
            refine ⟨48806746149584521992523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65075661532779362656697 48806746149584521992523)
            ·
              refine ⟨73210119224376782988785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48806746149584521992523 73210119224376782988785)
              ·
                refine ⟨54907589418282587241589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73210119224376782988785 54907589418282587241589)
                ·
                  refine ⟨5147586507963992553899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54907589418282587241589 5147586507963992553899)
                  ·
                    rfl

theorem cell21_22556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_22556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22556 prefixEnd_22556 := by exact prefixLift 22556
  have htrace : WordTrace (prefixWord ++ tailWord_22556) baseStart_22556 baseEnd_22556 := by
    simpa [prefixWord, tailWord_22556, baseEnd_22556] using wordTrace_append hprefix tailTrace_22556
  have hstable : (prefixWord ++ tailWord_22556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22556).length < 2 ^ (prefixWord ++ tailWord_22556).sum := by decide
  have hdescent : baseEnd_22556 < baseStart_22556 := by decide
  rcases family_descends (prefixWord ++ tailWord_22556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22615 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_22615 : Nat := 118140960795 + 22615 * 2 ^ 59
def prefixEnd_22615 : Nat := 4983230072969 + 3 ^ 40 * 22615 * 2
def baseEnd_22615 : Nat := 5161051111793001070445

theorem tailTrace_22615 : CollatzResearch.WordTrace tailWord_22615 prefixEnd_22615 5161051111793001070445 := by
  unfold tailWord_22615
  simp only [CollatzResearch.WordTrace]
  refine ⟨824836813077192179613299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 549891208718128119742199 824836813077192179613299)
  ·
    refine ⟨1237255219615788269419949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 824836813077192179613299 1237255219615788269419949)
    ·
      refine ⟨463970707355920601032481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1237255219615788269419949 463970707355920601032481)
      ·
        refine ⟨347978030516940450774361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463970707355920601032481 347978030516940450774361)
        ·
          refine ⟨260983522887705338080771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347978030516940450774361 260983522887705338080771)
          ·
            refine ⟨391475284331558007121157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260983522887705338080771 391475284331558007121157)
            ·
              refine ⟨73401615812167126335217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 391475284331558007121157 73401615812167126335217)
              ·
                refine ⟨55051211859125344751413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73401615812167126335217 55051211859125344751413)
                ·
                  refine ⟨5161051111793001070445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55051211859125344751413 5161051111793001070445)
                  ·
                    rfl

theorem cell21_22615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_22615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22615 prefixEnd_22615 := by exact prefixLift 22615
  have htrace : WordTrace (prefixWord ++ tailWord_22615) baseStart_22615 baseEnd_22615 := by
    simpa [prefixWord, tailWord_22615, baseEnd_22615] using wordTrace_append hprefix tailTrace_22615
  have hstable : (prefixWord ++ tailWord_22615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22615).length < 2 ^ (prefixWord ++ tailWord_22615).sum := by decide
  have hdescent : baseEnd_22615 < baseStart_22615 := by decide
  rcases family_descends (prefixWord ++ tailWord_22615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22663 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 4]
def baseStart_22663 : Nat := 118140960795 + 22663 * 2 ^ 59
def prefixEnd_22663 : Nat := 4983230072969 + 3 ^ 40 * 22663 * 2
def baseEnd_22663 : Nat := 5172005365755584270347

theorem tailTrace_22663 : CollatzResearch.WordTrace tailWord_22663 prefixEnd_22663 5172005365755584270347 := by
  unfold tailWord_22663
  simp only [CollatzResearch.WordTrace]
  refine ⟨826587516903296377360643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 551058344602197584907095 826587516903296377360643)
  ·
    refine ⟨1239881275354944566040965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826587516903296377360643 1239881275354944566040965)
    ·
      refine ⟨232477739129052106132681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1239881275354944566040965 232477739129052106132681)
      ·
        refine ⟨174358304346789079599511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232477739129052106132681 174358304346789079599511)
        ·
          refine ⟨261537456520183619399267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174358304346789079599511 261537456520183619399267)
          ·
            refine ⟨392306184780275429098901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261537456520183619399267 392306184780275429098901)
            ·
              refine ⟨18389352411575410739011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392306184780275429098901 18389352411575410739011)
              ·
                refine ⟨27584028617363116108517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18389352411575410739011 27584028617363116108517)
                ·
                  refine ⟨5172005365755584270347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27584028617363116108517 5172005365755584270347)
                  ·
                    rfl

theorem cell21_22663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 4].length) (baseStart_22663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22663 prefixEnd_22663 := by exact prefixLift 22663
  have htrace : WordTrace (prefixWord ++ tailWord_22663) baseStart_22663 baseEnd_22663 := by
    simpa [prefixWord, tailWord_22663, baseEnd_22663] using wordTrace_append hprefix tailTrace_22663
  have hstable : (prefixWord ++ tailWord_22663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22663).length < 2 ^ (prefixWord ++ tailWord_22663).sum := by decide
  have hdescent : baseEnd_22663 < baseStart_22663 := by decide
  rcases family_descends (prefixWord ++ tailWord_22663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22742 : List Nat := [5, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_22742 : Nat := 118140960795 + 22742 * 2 ^ 59
def prefixEnd_22742 : Nat := 4983230072969 + 3 ^ 40 * 22742 * 2
def baseEnd_22742 : Nat := 5190034242069002453519

theorem tailTrace_22742 : CollatzResearch.WordTrace tailWord_22742 prefixEnd_22742 5190034242069002453519 := by
  unfold tailWord_22742
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841805226068304342905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 552979255744728579657653 51841805226068304342905)
  ·
    refine ⟨38881353919551228257179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51841805226068304342905 38881353919551228257179)
    ·
      refine ⟨58322030879326842385769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38881353919551228257179 58322030879326842385769)
      ·
        refine ⟨43741523159495131789327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58322030879326842385769 43741523159495131789327)
        ·
          refine ⟨65612284739242697683991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43741523159495131789327 65612284739242697683991)
          ·
            refine ⟨98418427108864046525987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65612284739242697683991 98418427108864046525987)
            ·
              refine ⟨147627640663296069788981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98418427108864046525987 147627640663296069788981)
              ·
                refine ⟨13840091312184006542717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147627640663296069788981 13840091312184006542717)
                ·
                  refine ⟨5190034242069002453519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13840091312184006542717 5190034242069002453519)
                  ·
                    rfl

theorem cell21_22742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_22742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22742 prefixEnd_22742 := by exact prefixLift 22742
  have htrace : WordTrace (prefixWord ++ tailWord_22742) baseStart_22742 baseEnd_22742 := by
    simpa [prefixWord, tailWord_22742, baseEnd_22742] using wordTrace_append hprefix tailTrace_22742
  have hstable : (prefixWord ++ tailWord_22742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22742).length < 2 ^ (prefixWord ++ tailWord_22742).sum := by decide
  have hdescent : baseEnd_22742 < baseStart_22742 := by decide
  rcases family_descends (prefixWord ++ tailWord_22742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22767 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_22767 : Nat := 118140960795 + 22767 * 2 ^ 59
def prefixEnd_22767 : Nat := 4983230072969 + 3 ^ 40 * 22767 * 2
def baseEnd_22767 : Nat := 5195739582674514536801

theorem tailTrace_22767 : CollatzResearch.WordTrace tailWord_22767 prefixEnd_22767 5195739582674514536801 := by
  unfold tailWord_22767
  simp only [CollatzResearch.WordTrace]
  refine ⟨830380708526522139146555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 553587139017681426097703 830380708526522139146555)
  ·
    refine ⟨1245571062789783208719833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830380708526522139146555 1245571062789783208719833)
    ·
      refine ⟨934178297092337406539875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1245571062789783208719833 934178297092337406539875)
      ·
        refine ⟨1401267445638506109809813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934178297092337406539875 1401267445638506109809813)
        ·
          refine ⟨65684411514304973897335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1401267445638506109809813 65684411514304973897335)
          ·
            refine ⟨98526617271457460846003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65684411514304973897335 98526617271457460846003)
            ·
              refine ⟨147789925907186191269005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98526617271457460846003 147789925907186191269005)
              ·
                refine ⟨55421222215194821725877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147789925907186191269005 55421222215194821725877)
                ·
                  refine ⟨5195739582674514536801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55421222215194821725877 5195739582674514536801)
                  ·
                    rfl

theorem cell21_22767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_22767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22767 prefixEnd_22767 := by exact prefixLift 22767
  have htrace : WordTrace (prefixWord ++ tailWord_22767) baseStart_22767 baseEnd_22767 := by
    simpa [prefixWord, tailWord_22767, baseEnd_22767] using wordTrace_append hprefix tailTrace_22767
  have hstable : (prefixWord ++ tailWord_22767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22767).length < 2 ^ (prefixWord ++ tailWord_22767).sum := by decide
  have hdescent : baseEnd_22767 < baseStart_22767 := by decide
  rcases family_descends (prefixWord ++ tailWord_22767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22801 : List Nat := [1, 2, 2, 1, 1, 7, 1, 3, 3]
def baseStart_22801 : Nat := 118140960795 + 22801 * 2 ^ 59
def prefixEnd_22801 : Nat := 4983230072969 + 3 ^ 40 * 22801 * 2
def baseEnd_22801 : Nat := 5203498845898010970065

theorem tailTrace_22801 : CollatzResearch.WordTrace tailWord_22801 prefixEnd_22801 5203498845898010970065 := by
  unfold tailWord_22801
  simp only [CollatzResearch.WordTrace]
  refine ⟨831620790403345945884257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 554413860268897297256171 831620790403345945884257)
  ·
    refine ⟨623715592802509459413193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831620790403345945884257 623715592802509459413193)
    ·
      refine ⟨467786694601882094559895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623715592802509459413193 467786694601882094559895)
      ·
        refine ⟨701680041902823141839843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467786694601882094559895 701680041902823141839843)
        ·
          refine ⟨1052520062854234712759765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701680041902823141839843 1052520062854234712759765)
          ·
            refine ⟨24668438973146126080307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1052520062854234712759765 24668438973146126080307)
            ·
              refine ⟨37002658459719189120461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24668438973146126080307 37002658459719189120461)
              ·
                refine ⟨13875996922394695920173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37002658459719189120461 13875996922394695920173)
                ·
                  refine ⟨5203498845898010970065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13875996922394695920173 5203498845898010970065)
                  ·
                    rfl

theorem cell21_22801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_22801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22801 prefixEnd_22801 := by exact prefixLift 22801
  have htrace : WordTrace (prefixWord ++ tailWord_22801) baseStart_22801 baseEnd_22801 := by
    simpa [prefixWord, tailWord_22801, baseEnd_22801] using wordTrace_append hprefix tailTrace_22801
  have hstable : (prefixWord ++ tailWord_22801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22801).length < 2 ^ (prefixWord ++ tailWord_22801).sum := by decide
  have hdescent : baseEnd_22801 < baseStart_22801 := by decide
  rcases family_descends (prefixWord ++ tailWord_22801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22818 : List Nat := [3, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_22818 : Nat := 118140960795 + 22818 * 2 ^ 59
def prefixEnd_22818 : Nat := 4983230072969 + 3 ^ 40 * 22818 * 2
def baseEnd_22818 : Nat := 5207378477509759186697

theorem tailTrace_22818 : CollatzResearch.WordTrace tailWord_22818 prefixEnd_22818 5207378477509759186697 := by
  unfold tailWord_22818
  simp only [CollatzResearch.WordTrace]
  refine ⟨208060207835439462313277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 554827220894505232835405 208060207835439462313277)
  ·
    refine ⟨78022577938289798367479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208060207835439462313277 78022577938289798367479)
    ·
      refine ⟨117033866907434697551219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78022577938289798367479 117033866907434697551219)
      ·
        refine ⟨175550800361152046326829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117033866907434697551219 175550800361152046326829)
        ·
          refine ⟨65831550135432017372561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175550800361152046326829 65831550135432017372561)
          ·
            refine ⟨49373662601574013029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65831550135432017372561 49373662601574013029421)
            ·
              refine ⟨18515123475590254886033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49373662601574013029421 18515123475590254886033)
              ·
                refine ⟨13886342606692691164525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18515123475590254886033 13886342606692691164525)
                ·
                  refine ⟨5207378477509759186697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13886342606692691164525 5207378477509759186697)
                  ·
                    rfl

theorem cell21_22818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_22818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22818 prefixEnd_22818 := by exact prefixLift 22818
  have htrace : WordTrace (prefixWord ++ tailWord_22818) baseStart_22818 baseEnd_22818 := by
    simpa [prefixWord, tailWord_22818, baseEnd_22818] using wordTrace_append hprefix tailTrace_22818
  have hstable : (prefixWord ++ tailWord_22818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22818).length < 2 ^ (prefixWord ++ tailWord_22818).sum := by decide
  have hdescent : baseEnd_22818 < baseStart_22818 := by decide
  rcases family_descends (prefixWord ++ tailWord_22818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22860 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_22860 : Nat := 118140960795 + 22860 * 2 ^ 59
def prefixEnd_22860 : Nat := 4983230072969 + 3 ^ 40 * 22860 * 2
def baseEnd_22860 : Nat := 5216963449727019486611

theorem tailTrace_22860 : CollatzResearch.WordTrace tailWord_22860 prefixEnd_22860 5216963449727019486611 := by
  unfold tailWord_22860
  simp only [CollatzResearch.WordTrace]
  refine ⟨416886348594799511141017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 555848464793066014854689 416886348594799511141017)
  ·
    refine ⟨312664761446099633355763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 416886348594799511141017 312664761446099633355763)
    ·
      refine ⟨468997142169149450033645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312664761446099633355763 468997142169149450033645)
      ·
        refine ⟨175873928313431043762617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468997142169149450033645 175873928313431043762617)
        ·
          refine ⟨131905446235073282821963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175873928313431043762617 131905446235073282821963)
          ·
            refine ⟨197858169352609924232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131905446235073282821963 197858169352609924232945)
            ·
              refine ⟨148393627014457443174709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197858169352609924232945 148393627014457443174709)
              ·
                refine ⟨13911902532605385297629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148393627014457443174709 13911902532605385297629)
                ·
                  refine ⟨5216963449727019486611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13911902532605385297629 5216963449727019486611)
                  ·
                    rfl

theorem cell21_22860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_22860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22860 prefixEnd_22860 := by exact prefixLift 22860
  have htrace : WordTrace (prefixWord ++ tailWord_22860) baseStart_22860 baseEnd_22860 := by
    simpa [prefixWord, tailWord_22860, baseEnd_22860] using wordTrace_append hprefix tailTrace_22860
  have hstable : (prefixWord ++ tailWord_22860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22860).length < 2 ^ (prefixWord ++ tailWord_22860).sum := by decide
  have hdescent : baseEnd_22860 < baseStart_22860 := by decide
  rcases family_descends (prefixWord ++ tailWord_22860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22936 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_22936 : Nat := 118140960795 + 22936 * 2 ^ 59
def prefixEnd_22936 : Nat := 4983230072969 + 3 ^ 40 * 22936 * 2
def baseEnd_22936 : Nat := 5234307685167776219789

theorem tailTrace_22936 : CollatzResearch.WordTrace tailWord_22936 prefixEnd_22936 5234307685167776219789 := by
  unfold tailWord_22936
  simp only [CollatzResearch.WordTrace]
  refine ⟨418272322457132001024331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 557696429942842668032441 418272322457132001024331)
  ·
    refine ⟨627408483685698001536497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418272322457132001024331 627408483685698001536497)
    ·
      refine ⟨470556362764273501152373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627408483685698001536497 470556362764273501152373)
      ·
        refine ⟨44114659009150640733035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 470556362764273501152373 44114659009150640733035)
        ·
          refine ⟨66171988513725961099553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44114659009150640733035 66171988513725961099553)
          ·
            refine ⟨49628991385294470824665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66171988513725961099553 49628991385294470824665)
            ·
              refine ⟨37221743538970853118499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49628991385294470824665 37221743538970853118499)
              ·
                refine ⟨55832615308456279677749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37221743538970853118499 55832615308456279677749)
                ·
                  refine ⟨5234307685167776219789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55832615308456279677749 5234307685167776219789)
                  ·
                    rfl

theorem cell21_22936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_22936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_22936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_22936 prefixEnd_22936 := by exact prefixLift 22936
  have htrace : WordTrace (prefixWord ++ tailWord_22936) baseStart_22936 baseEnd_22936 := by
    simpa [prefixWord, tailWord_22936, baseEnd_22936] using wordTrace_append hprefix tailTrace_22936
  have hstable : (prefixWord ++ tailWord_22936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22936).length < 2 ^ (prefixWord ++ tailWord_22936).sum := by decide
  have hdescent : baseEnd_22936 < baseStart_22936 := by decide
  rcases family_descends (prefixWord ++ tailWord_22936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23147 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 3]
def baseStart_23147 : Nat := 118140960795 + 23147 * 2 ^ 59
def prefixEnd_23147 : Nat := 4983230072969 + 3 ^ 40 * 23147 * 2
def baseEnd_23147 : Nat := 5282460759878298202691

theorem tailTrace_23147 : CollatzResearch.WordTrace tailWord_23147 prefixEnd_23147 5282460759878298202691 := by
  unfold tailWord_23147
  simp only [CollatzResearch.WordTrace]
  refine ⟨844240447149847037979695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 562826964766564691986463 844240447149847037979695)
  ·
    refine ⟨1266360670724770556969543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 844240447149847037979695 1266360670724770556969543)
    ·
      refine ⟨1899541006087155835454315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266360670724770556969543 1899541006087155835454315)
      ·
        refine ⟨2849311509130733753181473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899541006087155835454315 2849311509130733753181473)
        ·
          refine ⟨2136983631848050314886105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849311509130733753181473 2136983631848050314886105)
          ·
            refine ⟨1602737723886037736164579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136983631848050314886105 1602737723886037736164579)
            ·
              refine ⟨2404106585829056604246869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602737723886037736164579 2404106585829056604246869)
              ·
                refine ⟨14086562026342128540509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2404106585829056604246869 14086562026342128540509)
                ·
                  refine ⟨5282460759878298202691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14086562026342128540509 5282460759878298202691)
                  ·
                    rfl

theorem cell21_23147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 3].length) (baseStart_23147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23147 prefixEnd_23147 := by exact prefixLift 23147
  have htrace : WordTrace (prefixWord ++ tailWord_23147) baseStart_23147 baseEnd_23147 := by
    simpa [prefixWord, tailWord_23147, baseEnd_23147] using wordTrace_append hprefix tailTrace_23147
  have hstable : (prefixWord ++ tailWord_23147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23147).length < 2 ^ (prefixWord ++ tailWord_23147).sum := by decide
  have hdescent : baseEnd_23147 < baseStart_23147 := by decide
  rcases family_descends (prefixWord ++ tailWord_23147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23161 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_23161 : Nat := 118140960795 + 23161 * 2 ^ 59
def prefixEnd_23161 : Nat := 4983230072969 + 3 ^ 40 * 23161 * 2
def baseEnd_23161 : Nat := 5285655750617384969329

theorem tailTrace_23161 : CollatzResearch.WordTrace tailWord_23161 prefixEnd_23161 5285655750617384969329 := by
  unfold tailWord_23161
  simp only [CollatzResearch.WordTrace]
  refine ⟨844751069099127428989337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 563167379399418285992891 844751069099127428989337)
  ·
    refine ⟨633563301824345571742003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 844751069099127428989337 633563301824345571742003)
    ·
      refine ⟨950344952736518357613005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633563301824345571742003 950344952736518357613005)
      ·
        refine ⟨356379357276194384104877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 950344952736518357613005 356379357276194384104877)
        ·
          refine ⟨133642258978572894039329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356379357276194384104877 133642258978572894039329)
          ·
            refine ⟨100231694233929670529497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133642258978572894039329 100231694233929670529497)
            ·
              refine ⟨75173770675447252897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100231694233929670529497 75173770675447252897123)
              ·
                refine ⟨112760656013170879345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75173770675447252897123 112760656013170879345685)
                ·
                  refine ⟨5285655750617384969329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112760656013170879345685 5285655750617384969329)
                  ·
                    rfl

theorem cell21_23161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_23161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23161 prefixEnd_23161 := by exact prefixLift 23161
  have htrace : WordTrace (prefixWord ++ tailWord_23161) baseStart_23161 baseEnd_23161 := by
    simpa [prefixWord, tailWord_23161, baseEnd_23161] using wordTrace_append hprefix tailTrace_23161
  have hstable : (prefixWord ++ tailWord_23161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23161).length < 2 ^ (prefixWord ++ tailWord_23161).sum := by decide
  have hdescent : baseEnd_23161 < baseStart_23161 := by decide
  rcases family_descends (prefixWord ++ tailWord_23161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23296 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_23296 : Nat := 118140960795 + 23296 * 2 ^ 59
def prefixEnd_23296 : Nat := 4983230072969 + 3 ^ 40 * 23296 * 2
def baseEnd_23296 : Nat := 5316464589887150219053

theorem tailTrace_23296 : CollatzResearch.WordTrace tailWord_23296 prefixEnd_23296 5316464589887150219053 := by
  unfold tailWord_23296
  simp only [CollatzResearch.WordTrace]
  refine ⟨424837461805022742576871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 566449949073363656769161 424837461805022742576871)
  ·
    refine ⟨637256192707534113865307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424837461805022742576871 637256192707534113865307)
    ·
      refine ⟨955884289061301170797961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637256192707534113865307 955884289061301170797961)
      ·
        refine ⟨716913216795975878098471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955884289061301170797961 716913216795975878098471)
        ·
          refine ⟨1075369825193963817147707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716913216795975878098471 1075369825193963817147707)
          ·
            refine ⟨1613054737790945725721561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075369825193963817147707 1613054737790945725721561)
            ·
              refine ⟨1209791053343209294291171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613054737790945725721561 1209791053343209294291171)
              ·
                refine ⟨1814686580014813941436757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209791053343209294291171 1814686580014813941436757)
                ·
                  refine ⟨5316464589887150219053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1814686580014813941436757 5316464589887150219053)
                  ·
                    rfl

theorem cell21_23296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_23296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23296 prefixEnd_23296 := by exact prefixLift 23296
  have htrace : WordTrace (prefixWord ++ tailWord_23296) baseStart_23296 baseEnd_23296 := by
    simpa [prefixWord, tailWord_23296, baseEnd_23296] using wordTrace_append hprefix tailTrace_23296
  have hstable : (prefixWord ++ tailWord_23296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23296).length < 2 ^ (prefixWord ++ tailWord_23296).sum := by decide
  have hdescent : baseEnd_23296 < baseStart_23296 := by decide
  rcases family_descends (prefixWord ++ tailWord_23296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23327 : List Nat := [1, 1, 2, 4, 2, 2, 9]
def baseStart_23327 : Nat := 118140960795 + 23327 * 2 ^ 59
def prefixEnd_23327 : Nat := 4983230072969 + 3 ^ 40 * 23327 * 2
def baseEnd_23327 : Nat := 591504356915331689147

theorem tailTrace_23327 : CollatzResearch.WordTrace tailWord_23327 prefixEnd_23327 591504356915331689147 := by
  unfold tailWord_23327
  simp only [CollatzResearch.WordTrace]
  refine ⟨850805586497737779532235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567203724331825186354823 850805586497737779532235)
  ·
    refine ⟨1276208379746606669298353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 850805586497737779532235 1276208379746606669298353)
    ·
      refine ⟨957156284809955001973765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1276208379746606669298353 957156284809955001973765)
      ·
        refine ⟨179466803401866562870081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 957156284809955001973765 179466803401866562870081)
        ·
          refine ⟨134600102551399922152561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179466803401866562870081 134600102551399922152561)
          ·
            refine ⟨100950076913549941614421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134600102551399922152561 100950076913549941614421)
            ·
              refine ⟨591504356915331689147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 100950076913549941614421 591504356915331689147)
              ·
                rfl

theorem cell21_23327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_23327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23327 prefixEnd_23327 := by exact prefixLift 23327
  have htrace : WordTrace (prefixWord ++ tailWord_23327) baseStart_23327 baseEnd_23327 := by
    simpa [prefixWord, tailWord_23327, baseEnd_23327] using wordTrace_append hprefix tailTrace_23327
  have hstable : (prefixWord ++ tailWord_23327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23327).length < 2 ^ (prefixWord ++ tailWord_23327).sum := by decide
  have hdescent : baseEnd_23327 < baseStart_23327 := by decide
  rcases family_descends (prefixWord ++ tailWord_23327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23347 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 4]
def baseStart_23347 : Nat := 118140960795 + 23347 * 2 ^ 59
def prefixEnd_23347 : Nat := 4983230072969 + 3 ^ 40 * 23347 * 2
def baseEnd_23347 : Nat := 5328103484722394868949

theorem tailTrace_23347 : CollatzResearch.WordTrace tailWord_23347 prefixEnd_23347 5328103484722394868949 := by
  unfold tailWord_23347
  simp only [CollatzResearch.WordTrace]
  refine ⟨851535046425281195260295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567690030950187463506863 851535046425281195260295)
  ·
    refine ⟨1277302569637921792890443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851535046425281195260295 1277302569637921792890443)
    ·
      refine ⟨1915953854456882689335665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277302569637921792890443 1915953854456882689335665)
      ·
        refine ⟨1436965390842662017001749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1915953854456882689335665 1436965390842662017001749)
        ·
          refine ⟨67357752695749782046957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1436965390842662017001749 67357752695749782046957)
          ·
            refine ⟨25259157260906168267609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67357752695749782046957 25259157260906168267609)
            ·
              refine ⟨18944367945679626200707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25259157260906168267609 18944367945679626200707)
              ·
                refine ⟨28416551918519439301061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18944367945679626200707 28416551918519439301061)
                ·
                  refine ⟨5328103484722394868949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28416551918519439301061 5328103484722394868949)
                  ·
                    rfl

theorem cell21_23347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 4].length) (baseStart_23347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23347 prefixEnd_23347 := by exact prefixLift 23347
  have htrace : WordTrace (prefixWord ++ tailWord_23347) baseStart_23347 baseEnd_23347 := by
    simpa [prefixWord, tailWord_23347, baseEnd_23347] using wordTrace_append hprefix tailTrace_23347
  have hstable : (prefixWord ++ tailWord_23347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23347).length < 2 ^ (prefixWord ++ tailWord_23347).sum := by decide
  have hdescent : baseEnd_23347 < baseStart_23347 := by decide
  rcases family_descends (prefixWord ++ tailWord_23347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23403 : List Nat := [1, 1, 1, 1, 2, 2, 7, 6]
def baseStart_23403 : Nat := 118140960795 + 23403 * 2 ^ 59
def prefixEnd_23403 : Nat := 4983230072969 + 3 ^ 40 * 23403 * 2
def baseEnd_23403 : Nat := 1780294482559580645167

theorem tailTrace_23403 : CollatzResearch.WordTrace tailWord_23403 prefixEnd_23403 1780294482559580645167 := by
  unfold tailWord_23403
  simp only [CollatzResearch.WordTrace]
  refine ⟨853577534222402759298863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569051689481601839532575 853577534222402759298863)
  ·
    refine ⟨1280366301333604138948295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853577534222402759298863 1280366301333604138948295)
    ·
      refine ⟨1920549452000406208422443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280366301333604138948295 1920549452000406208422443)
      ·
        refine ⟨2880824178000609312633665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920549452000406208422443 2880824178000609312633665)
        ·
          refine ⟨2160618133500456984475249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880824178000609312633665 2160618133500456984475249)
          ·
            refine ⟨1620463600125342738356437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160618133500456984475249 1620463600125342738356437)
            ·
              refine ⟨37979615627937720430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1620463600125342738356437 37979615627937720430229)
              ·
                refine ⟨1780294482559580645167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37979615627937720430229 1780294482559580645167)
                ·
                  rfl

theorem cell21_23403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_23403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23403 prefixEnd_23403 := by exact prefixLift 23403
  have htrace : WordTrace (prefixWord ++ tailWord_23403) baseStart_23403 baseEnd_23403 := by
    simpa [prefixWord, tailWord_23403, baseEnd_23403] using wordTrace_append hprefix tailTrace_23403
  have hstable : (prefixWord ++ tailWord_23403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23403).length < 2 ^ (prefixWord ++ tailWord_23403).sum := by decide
  have hdescent : baseEnd_23403 < baseStart_23403 := by decide
  rcases family_descends (prefixWord ++ tailWord_23403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23485 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 3]
def baseStart_23485 : Nat := 118140960795 + 23485 * 2 ^ 59
def prefixEnd_23485 : Nat := 4983230072969 + 3 ^ 40 * 23485 * 2
def baseEnd_23485 : Nat := 5359596964864821568667

theorem tailTrace_23485 : CollatzResearch.WordTrace tailWord_23485 prefixEnd_23485 5359596964864821568667 := by
  unfold tailWord_23485
  simp only [CollatzResearch.WordTrace]
  refine ⟨856568319925330763783909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 571045546616887175855939 856568319925330763783909)
  ·
    refine ⟨160606559985999518209483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 856568319925330763783909 160606559985999518209483)
    ·
      refine ⟨240909839978999277314225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160606559985999518209483 240909839978999277314225)
      ·
        refine ⟨180682379984249457985669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240909839978999277314225 180682379984249457985669)
        ·
          refine ⟨33877946247046773372313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180682379984249457985669 33877946247046773372313)
          ·
            refine ⟨25408459685285080029235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33877946247046773372313 25408459685285080029235)
            ·
              refine ⟨38112689527927620043853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25408459685285080029235 38112689527927620043853)
              ·
                refine ⟨14292258572972857516445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38112689527927620043853 14292258572972857516445)
                ·
                  refine ⟨5359596964864821568667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14292258572972857516445 5359596964864821568667)
                  ·
                    rfl

theorem cell21_23485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_23485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23485 prefixEnd_23485 := by exact prefixLift 23485
  have htrace : WordTrace (prefixWord ++ tailWord_23485) baseStart_23485 baseEnd_23485 := by
    simpa [prefixWord, tailWord_23485, baseEnd_23485] using wordTrace_append hprefix tailTrace_23485
  have hstable : (prefixWord ++ tailWord_23485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23485).length < 2 ^ (prefixWord ++ tailWord_23485).sum := by decide
  have hdescent : baseEnd_23485 < baseStart_23485 := by decide
  rcases family_descends (prefixWord ++ tailWord_23485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23496 : List Nat := [2, 1, 3, 1, 5, 2, 7]
def baseStart_23496 : Nat := 118140960795 + 23496 * 2 ^ 59
def prefixEnd_23496 : Nat := 4983230072969 + 3 ^ 40 * 23496 * 2
def baseEnd_23496 : Nat := 595789701636805209479

theorem tailTrace_23496 : CollatzResearch.WordTrace tailWord_23496 prefixEnd_23496 595789701636805209479 := by
  unfold tailWord_23496
  simp only [CollatzResearch.WordTrace]
  refine ⟨428484761442739821217171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571313015256986428289561 428484761442739821217171)
  ·
    refine ⟨642727142164109731825757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428484761442739821217171 642727142164109731825757)
    ·
      refine ⟨241022678311541149434659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 642727142164109731825757 241022678311541149434659)
      ·
        refine ⟨361534017467311724151989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241022678311541149434659 361534017467311724151989)
        ·
          refine ⟨33893814137560474139249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361534017467311724151989 33893814137560474139249)
          ·
            refine ⟨25420360603170355604437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33893814137560474139249 25420360603170355604437)
            ·
              refine ⟨595789701636805209479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25420360603170355604437 595789701636805209479)
              ·
                rfl

theorem cell21_23496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 7].length) (baseStart_23496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23496 prefixEnd_23496 := by exact prefixLift 23496
  have htrace : WordTrace (prefixWord ++ tailWord_23496) baseStart_23496 baseEnd_23496 := by
    simpa [prefixWord, tailWord_23496, baseEnd_23496] using wordTrace_append hprefix tailTrace_23496
  have hstable : (prefixWord ++ tailWord_23496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23496).length < 2 ^ (prefixWord ++ tailWord_23496).sum := by decide
  have hdescent : baseEnd_23496 < baseStart_23496 := by decide
  rcases family_descends (prefixWord ++ tailWord_23496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23524 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_23524 : Nat := 118140960795 + 23524 * 2 ^ 59
def prefixEnd_23524 : Nat := 4983230072969 + 3 ^ 40 * 23524 * 2
def baseEnd_23524 : Nat := 5368497296209420418587

theorem tailTrace_23524 : CollatzResearch.WordTrace tailWord_23524 prefixEnd_23524 5368497296209420418587 := by
  unfold tailWord_23524
  simp only [CollatzResearch.WordTrace]
  refine ⟨428995383392020212226813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571993844522693616302417 428995383392020212226813)
  ·
    refine ⟨160873268772007579585055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 428995383392020212226813 160873268772007579585055)
    ·
      refine ⟨241309903158011369377583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160873268772007579585055 241309903158011369377583)
      ·
        refine ⟨361964854737017054066375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241309903158011369377583 361964854737017054066375)
        ·
          refine ⟨542947282105525581099563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361964854737017054066375 542947282105525581099563)
          ·
            refine ⟨814420923158288371649345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542947282105525581099563 814420923158288371649345)
            ·
              refine ⟨610815692368716278737009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814420923158288371649345 610815692368716278737009)
              ·
                refine ⟨458111769276537209052757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610815692368716278737009 458111769276537209052757)
                ·
                  refine ⟨5368497296209420418587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 458111769276537209052757 5368497296209420418587)
                  ·
                    rfl

theorem cell21_23524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_23524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23524 prefixEnd_23524 := by exact prefixLift 23524
  have htrace : WordTrace (prefixWord ++ tailWord_23524) baseStart_23524 baseEnd_23524 := by
    simpa [prefixWord, tailWord_23524, baseEnd_23524] using wordTrace_append hprefix tailTrace_23524
  have hstable : (prefixWord ++ tailWord_23524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23524).length < 2 ^ (prefixWord ++ tailWord_23524).sum := by decide
  have hdescent : baseEnd_23524 < baseStart_23524 := by decide
  rcases family_descends (prefixWord ++ tailWord_23524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23569 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_23569 : Nat := 118140960795 + 23569 * 2 ^ 59
def prefixEnd_23569 : Nat := 4983230072969 + 3 ^ 40 * 23569 * 2
def baseEnd_23569 : Nat := 5378766909299342168495

theorem tailTrace_23569 : CollatzResearch.WordTrace tailWord_23569 prefixEnd_23569 5378766909299342168495 := by
  unfold tailWord_23569
  simp only [CollatzResearch.WordTrace]
  refine ⟨859632051621013109841761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 573088034414008739894507 859632051621013109841761)
  ·
    refine ⟨644724038715759832381321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 859632051621013109841761 644724038715759832381321)
    ·
      refine ⟨483543029036819874285991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 644724038715759832381321 483543029036819874285991)
      ·
        refine ⟨725314543555229811428987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483543029036819874285991 725314543555229811428987)
        ·
          refine ⟨1087971815332844717143481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725314543555229811428987 1087971815332844717143481)
          ·
            refine ⟨815978861499633537857611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087971815332844717143481 815978861499633537857611)
            ·
              refine ⟨1223968292249450306786417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815978861499633537857611 1223968292249450306786417)
              ·
                refine ⟨917976219187087730089813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223968292249450306786417 917976219187087730089813)
                ·
                  refine ⟨5378766909299342168495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 917976219187087730089813 5378766909299342168495)
                  ·
                    rfl

theorem cell21_23569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_23569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23569 prefixEnd_23569 := by exact prefixLift 23569
  have htrace : WordTrace (prefixWord ++ tailWord_23569) baseStart_23569 baseEnd_23569 := by
    simpa [prefixWord, tailWord_23569, baseEnd_23569] using wordTrace_append hprefix tailTrace_23569
  have hstable : (prefixWord ++ tailWord_23569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23569).length < 2 ^ (prefixWord ++ tailWord_23569).sum := by decide
  have hdescent : baseEnd_23569 < baseStart_23569 := by decide
  rcases family_descends (prefixWord ++ tailWord_23569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23586 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_23586 : Nat := 118140960795 + 23586 * 2 ^ 59
def prefixEnd_23586 : Nat := 4983230072969 + 3 ^ 40 * 23586 * 2
def baseEnd_23586 : Nat := 5382646540911090385127

theorem tailTrace_23586 : CollatzResearch.WordTrace tailWord_23586 prefixEnd_23586 5382646540911090385127 := by
  unfold tailWord_23586
  simp only [CollatzResearch.WordTrace]
  refine ⟨215063023139856253302653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 573501395039616675473741 215063023139856253302653)
  ·
    refine ⟨80648633677446094988495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215063023139856253302653 80648633677446094988495)
    ·
      refine ⟨120972950516169142482743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80648633677446094988495 120972950516169142482743)
      ·
        refine ⟨181459425774253713724115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120972950516169142482743 181459425774253713724115)
        ·
          refine ⟨272189138661380570586173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181459425774253713724115 272189138661380570586173)
          ·
            refine ⟨102070926998017713969815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272189138661380570586173 102070926998017713969815)
            ·
              refine ⟨153106390497026570954723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102070926998017713969815 153106390497026570954723)
              ·
                refine ⟨229659585745539856432085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153106390497026570954723 229659585745539856432085)
                ·
                  refine ⟨5382646540911090385127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 229659585745539856432085 5382646540911090385127)
                  ·
                    rfl

theorem cell21_23586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_23586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23586 prefixEnd_23586 := by exact prefixLift 23586
  have htrace : WordTrace (prefixWord ++ tailWord_23586) baseStart_23586 baseEnd_23586 := by
    simpa [prefixWord, tailWord_23586, baseEnd_23586] using wordTrace_append hprefix tailTrace_23586
  have hstable : (prefixWord ++ tailWord_23586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23586).length < 2 ^ (prefixWord ++ tailWord_23586).sum := by decide
  have hdescent : baseEnd_23586 < baseStart_23586 := by decide
  rcases family_descends (prefixWord ++ tailWord_23586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23600 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_23600 : Nat := 118140960795 + 23600 * 2 ^ 59
def prefixEnd_23600 : Nat := 4983230072969 + 3 ^ 40 * 23600 * 2
def baseEnd_23600 : Nat := 5385841531650177151765

theorem tailTrace_23600 : CollatzResearch.WordTrace tailWord_23600 prefixEnd_23600 5385841531650177151765 := by
  unfold tailWord_23600
  simp only [CollatzResearch.WordTrace]
  refine ⟨430381357254352702110127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 573841809672470269480169 430381357254352702110127)
  ·
    refine ⟨645572035881529053165191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430381357254352702110127 645572035881529053165191)
    ·
      refine ⟨968358053822293579747787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645572035881529053165191 968358053822293579747787)
      ·
        refine ⟨1452537080733440369621681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968358053822293579747787 1452537080733440369621681)
        ·
          refine ⟨1089402810550080277216261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452537080733440369621681 1089402810550080277216261)
          ·
            refine ⟨204263026978140051978049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1089402810550080277216261 204263026978140051978049)
            ·
              refine ⟨153197270233605038983537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204263026978140051978049 153197270233605038983537)
              ·
                refine ⟨114897952675203779237653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153197270233605038983537 114897952675203779237653)
                ·
                  refine ⟨5385841531650177151765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114897952675203779237653 5385841531650177151765)
                  ·
                    rfl

theorem cell21_23600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_23600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23600 prefixEnd_23600 := by exact prefixLift 23600
  have htrace : WordTrace (prefixWord ++ tailWord_23600) baseStart_23600 baseEnd_23600 := by
    simpa [prefixWord, tailWord_23600, baseEnd_23600] using wordTrace_append hprefix tailTrace_23600
  have hstable : (prefixWord ++ tailWord_23600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23600).length < 2 ^ (prefixWord ++ tailWord_23600).sum := by decide
  have hdescent : baseEnd_23600 < baseStart_23600 := by decide
  rcases family_descends (prefixWord ++ tailWord_23600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23676 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_23676 : Nat := 118140960795 + 23676 * 2 ^ 59
def prefixEnd_23676 : Nat := 4983230072969 + 3 ^ 40 * 23676 * 2
def baseEnd_23676 : Nat := 5403185767090933884943

theorem tailTrace_23676 : CollatzResearch.WordTrace tailWord_23676 prefixEnd_23676 5403185767090933884943 := by
  unfold tailWord_23676
  simp only [CollatzResearch.WordTrace]
  refine ⟨431767331116685191993441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 575689774822246922657921 431767331116685191993441)
  ·
    refine ⟨323825498337513893995081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 431767331116685191993441 323825498337513893995081)
    ·
      refine ⟨242869123753135420496311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323825498337513893995081 242869123753135420496311)
      ·
        refine ⟨364303685629703130744467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242869123753135420496311 364303685629703130744467)
        ·
          refine ⟨546455528444554696116701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364303685629703130744467 546455528444554696116701)
          ·
            refine ⟨204920823166708011043763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546455528444554696116701 204920823166708011043763)
            ·
              refine ⟨307381234750062016565645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204920823166708011043763 307381234750062016565645)
              ·
                refine ⟨115267963031273256212117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307381234750062016565645 115267963031273256212117)
                ·
                  refine ⟨5403185767090933884943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115267963031273256212117 5403185767090933884943)
                  ·
                    rfl

theorem cell21_23676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_23676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23676 prefixEnd_23676 := by exact prefixLift 23676
  have htrace : WordTrace (prefixWord ++ tailWord_23676) baseStart_23676 baseEnd_23676 := by
    simpa [prefixWord, tailWord_23676, baseEnd_23676] using wordTrace_append hprefix tailTrace_23676
  have hstable : (prefixWord ++ tailWord_23676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23676).length < 2 ^ (prefixWord ++ tailWord_23676).sum := by decide
  have hdescent : baseEnd_23676 < baseStart_23676 := by decide
  rcases family_descends (prefixWord ++ tailWord_23676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23786 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_23786 : Nat := 118140960795 + 23786 * 2 ^ 59
def prefixEnd_23786 : Nat := 4983230072969 + 3 ^ 40 * 23786 * 2
def baseEnd_23786 : Nat := 5428289265755187051385

theorem tailTrace_23786 : CollatzResearch.WordTrace tailWord_23786 prefixEnd_23786 5428289265755187051385 := by
  unfold tailWord_23786
  simp only [CollatzResearch.WordTrace]
  refine ⟨216886672958714792622803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 578364461223239446994141 216886672958714792622803)
  ·
    refine ⟨325330009438072188934205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216886672958714792622803 325330009438072188934205)
    ·
      refine ⟨121998753539277070850327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325330009438072188934205 121998753539277070850327)
      ·
        refine ⟨182998130308915606275491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121998753539277070850327 182998130308915606275491)
        ·
          refine ⟨274497195463373409413237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182998130308915606275491 274497195463373409413237)
          ·
            refine ⟨25734112074691257132491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 274497195463373409413237 25734112074691257132491)
            ·
              refine ⟨38601168112036885698737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25734112074691257132491 38601168112036885698737)
              ·
                refine ⟨28950876084027664274053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38601168112036885698737 28950876084027664274053)
                ·
                  refine ⟨5428289265755187051385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28950876084027664274053 5428289265755187051385)
                  ·
                    rfl

theorem cell21_23786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_23786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23786 prefixEnd_23786 := by exact prefixLift 23786
  have htrace : WordTrace (prefixWord ++ tailWord_23786) baseStart_23786 baseEnd_23786 := by
    simpa [prefixWord, tailWord_23786, baseEnd_23786] using wordTrace_append hprefix tailTrace_23786
  have hstable : (prefixWord ++ tailWord_23786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23786).length < 2 ^ (prefixWord ++ tailWord_23786).sum := by decide
  have hdescent : baseEnd_23786 < baseStart_23786 := by decide
  rcases family_descends (prefixWord ++ tailWord_23786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23859 : List Nat := [1, 1, 1, 2, 5, 3, 2, 6]
def baseStart_23859 : Nat := 118140960795 + 23859 * 2 ^ 59
def prefixEnd_23859 : Nat := 4983230072969 + 3 ^ 40 * 23859 * 2
def baseEnd_23859 : Nat := 1814982953441094111523

theorem tailTrace_23859 : CollatzResearch.WordTrace tailWord_23859 prefixEnd_23859 1814982953441094111523 := by
  unfold tailWord_23859
  simp only [CollatzResearch.WordTrace]
  refine ⟨870209220570392637898631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 580139480380261758599087 870209220570392637898631)
  ·
    refine ⟨1305313830855588956847947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870209220570392637898631 1305313830855588956847947)
    ·
      refine ⟨1957970746283383435271921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305313830855588956847947 1957970746283383435271921)
      ·
        refine ⟨1468478059712537576453941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957970746283383435271921 1468478059712537576453941)
        ·
          refine ⟨137669818098050397792557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1468478059712537576453941 137669818098050397792557)
          ·
            refine ⟨51626181786768899172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137669818098050397792557 51626181786768899172209)
            ·
              refine ⟨38719636340076674379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51626181786768899172209 38719636340076674379157)
              ·
                refine ⟨1814982953441094111523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38719636340076674379157 1814982953441094111523)
                ·
                  rfl

theorem cell21_23859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_23859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23859 prefixEnd_23859 := by exact prefixLift 23859
  have htrace : WordTrace (prefixWord ++ tailWord_23859) baseStart_23859 baseEnd_23859 := by
    simpa [prefixWord, tailWord_23859, baseEnd_23859] using wordTrace_append hprefix tailTrace_23859
  have hstable : (prefixWord ++ tailWord_23859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23859).length < 2 ^ (prefixWord ++ tailWord_23859).sum := by decide
  have hdescent : baseEnd_23859 < baseStart_23859 := by decide
  rcases family_descends (prefixWord ++ tailWord_23859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23876 : List Nat := [2, 3, 4, 1, 1, 1, 2, 7]
def baseStart_23876 : Nat := 118140960795 + 23876 * 2 ^ 59
def prefixEnd_23876 : Nat := 4983230072969 + 3 ^ 40 * 23876 * 2
def baseEnd_23876 : Nat := 1816276163978343517067

theorem tailTrace_23876 : CollatzResearch.WordTrace tailWord_23876 prefixEnd_23876 1816276163978343517067 := by
  unfold tailWord_23876
  simp only [CollatzResearch.WordTrace]
  refine ⟨435414630754402270633741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 580552841005869694178321 435414630754402270633741)
  ·
    refine ⟨163280486532900851487653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 435414630754402270633741 163280486532900851487653)
    ·
      refine ⟨30615091224918909653935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163280486532900851487653 30615091224918909653935)
      ·
        refine ⟨45922636837378364480903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30615091224918909653935 45922636837378364480903)
        ·
          refine ⟨68883955256067546721355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45922636837378364480903 68883955256067546721355)
          ·
            refine ⟨103325932884101320082033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68883955256067546721355 103325932884101320082033)
            ·
              refine ⟨77494449663075990061525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103325932884101320082033 77494449663075990061525)
              ·
                refine ⟨1816276163978343517067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77494449663075990061525 1816276163978343517067)
                ·
                  rfl

theorem cell21_23876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_23876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23876 prefixEnd_23876 := by exact prefixLift 23876
  have htrace : WordTrace (prefixWord ++ tailWord_23876) baseStart_23876 baseEnd_23876 := by
    simpa [prefixWord, tailWord_23876, baseEnd_23876] using wordTrace_append hprefix tailTrace_23876
  have hstable : (prefixWord ++ tailWord_23876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23876).length < 2 ^ (prefixWord ++ tailWord_23876).sum := by decide
  have hdescent : baseEnd_23876 < baseStart_23876 := by decide
  rcases family_descends (prefixWord ++ tailWord_23876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23907 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 3]
def baseStart_23907 : Nat := 118140960795 + 23907 * 2 ^ 59
def prefixEnd_23907 : Nat := 4983230072969 + 3 ^ 40 * 23907 * 2
def baseEnd_23907 : Nat := 5455903114285865534471

theorem tailTrace_23907 : CollatzResearch.WordTrace tailWord_23907 prefixEnd_23907 5455903114285865534471 := by
  unfold tailWord_23907
  simp only [CollatzResearch.WordTrace]
  refine ⟨871959924396496835645975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 581306616264331223763983 871959924396496835645975)
  ·
    refine ⟨1307939886594745253468963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 871959924396496835645975 1307939886594745253468963)
    ·
      refine ⟨1961909829892117880203445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307939886594745253468963 1961909829892117880203445)
      ·
        refine ⟨183929046552386051269073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1961909829892117880203445 183929046552386051269073)
        ·
          refine ⟨137946784914289538451805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183929046552386051269073 137946784914289538451805)
          ·
            refine ⟨51730044342858576919427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137946784914289538451805 51730044342858576919427)
            ·
              refine ⟨77595066514287865379141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51730044342858576919427 77595066514287865379141)
              ·
                refine ⟨14549074971428974758589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77595066514287865379141 14549074971428974758589)
                ·
                  refine ⟨5455903114285865534471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14549074971428974758589 5455903114285865534471)
                  ·
                    rfl

theorem cell21_23907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 3].length) (baseStart_23907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23907 prefixEnd_23907 := by exact prefixLift 23907
  have htrace : WordTrace (prefixWord ++ tailWord_23907) baseStart_23907 baseEnd_23907 := by
    simpa [prefixWord, tailWord_23907, baseEnd_23907] using wordTrace_append hprefix tailTrace_23907
  have hstable : (prefixWord ++ tailWord_23907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23907).length < 2 ^ (prefixWord ++ tailWord_23907).sum := by decide
  have hdescent : baseEnd_23907 < baseStart_23907 := by decide
  rcases family_descends (prefixWord ++ tailWord_23907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23963 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_23963 : Nat := 118140960795 + 23963 * 2 ^ 59
def prefixEnd_23963 : Nat := 4983230072969 + 3 ^ 40 * 23963 * 2
def baseEnd_23963 : Nat := 5468683077242212601023

theorem tailTrace_23963 : CollatzResearch.WordTrace tailWord_23963 prefixEnd_23963 5468683077242212601023 := by
  unfold tailWord_23963
  simp only [CollatzResearch.WordTrace]
  refine ⟨874002412193618399684543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 582668274795745599789695 874002412193618399684543)
  ·
    refine ⟨1311003618290427599526815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874002412193618399684543 1311003618290427599526815)
    ·
      refine ⟨1966505427435641399290223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311003618290427599526815 1966505427435641399290223)
      ·
        refine ⟨2949758141153462098935335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966505427435641399290223 2949758141153462098935335)
        ·
          refine ⟨4424637211730193148403003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949758141153462098935335 4424637211730193148403003)
          ·
            refine ⟨6636955817595289722604505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424637211730193148403003 6636955817595289722604505)
            ·
              refine ⟨4977716863196467291953379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636955817595289722604505 4977716863196467291953379)
              ·
                refine ⟨7466575294794700937930069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977716863196467291953379 7466575294794700937930069)
                ·
                  refine ⟨5468683077242212601023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 7466575294794700937930069 5468683077242212601023)
                  ·
                    rfl

theorem cell21_23963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_23963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23963 prefixEnd_23963 := by exact prefixLift 23963
  have htrace : WordTrace (prefixWord ++ tailWord_23963) baseStart_23963 baseEnd_23963 := by
    simpa [prefixWord, tailWord_23963, baseEnd_23963] using wordTrace_append hprefix tailTrace_23963
  have hstable : (prefixWord ++ tailWord_23963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23963).length < 2 ^ (prefixWord ++ tailWord_23963).sum := by decide
  have hdescent : baseEnd_23963 < baseStart_23963 := by decide
  rcases family_descends (prefixWord ++ tailWord_23963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23980 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_23980 : Nat := 118140960795 + 23980 * 2 ^ 59
def prefixEnd_23980 : Nat := 4983230072969 + 3 ^ 40 * 23980 * 2
def baseEnd_23980 : Nat := 5472562708853960817655

theorem tailTrace_23980 : CollatzResearch.WordTrace tailWord_23980 prefixEnd_23980 5472562708853960817655 := by
  unfold tailWord_23980
  simp only [CollatzResearch.WordTrace]
  refine ⟨437311226566015151526697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 583081635421353535368929 437311226566015151526697)
  ·
    refine ⟨327983419924511363645023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 437311226566015151526697 327983419924511363645023)
    ·
      refine ⟨491975129886767045467535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327983419924511363645023 491975129886767045467535)
      ·
        refine ⟨737962694830150568201303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491975129886767045467535 737962694830150568201303)
        ·
          refine ⟨1106944042245225852301955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737962694830150568201303 1106944042245225852301955)
          ·
            refine ⟨1660416063367838778452933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106944042245225852301955 1660416063367838778452933)
            ·
              refine ⟨311328011881469770959925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1660416063367838778452933 311328011881469770959925)
              ·
                refine ⟨29187001113887791027493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311328011881469770959925 29187001113887791027493)
                ·
                  refine ⟨5472562708853960817655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29187001113887791027493 5472562708853960817655)
                  ·
                    rfl

theorem cell21_23980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_23980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_23980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_23980 prefixEnd_23980 := by exact prefixLift 23980
  have htrace : WordTrace (prefixWord ++ tailWord_23980) baseStart_23980 baseEnd_23980 := by
    simpa [prefixWord, tailWord_23980, baseEnd_23980] using wordTrace_append hprefix tailTrace_23980
  have hstable : (prefixWord ++ tailWord_23980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23980).length < 2 ^ (prefixWord ++ tailWord_23980).sum := by decide
  have hdescent : baseEnd_23980 < baseStart_23980 := by decide
  rcases family_descends (prefixWord ++ tailWord_23980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24163 : List Nat := [1, 1, 1, 5, 1, 3, 4, 5]
def baseStart_24163 : Nat := 118140960795 + 24163 * 2 ^ 59
def prefixEnd_24163 : Nat := 4983230072969 + 3 ^ 40 * 24163 * 2
def baseEnd_24163 : Nat := 1838108600695436422427

theorem tailTrace_24163 : CollatzResearch.WordTrace tailWord_24163 prefixEnd_24163 1838108600695436422427 := by
  unfold tailWord_24163
  simp only [CollatzResearch.WordTrace]
  refine ⟨881297011469052556965143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 587531340979368371310095 881297011469052556965143)
  ·
    refine ⟨1321945517203578835447715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881297011469052556965143 1321945517203578835447715)
    ·
      refine ⟨1982918275805368253171573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321945517203578835447715 1982918275805368253171573)
      ·
        refine ⟨185898588356753273734835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1982918275805368253171573 185898588356753273734835)
        ·
          refine ⟨278847882535129910602253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185898588356753273734835 278847882535129910602253)
          ·
            refine ⟨104567955950673716475845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278847882535129910602253 104567955950673716475845)
            ·
              refine ⟨19606491740751321839221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104567955950673716475845 19606491740751321839221)
              ·
                refine ⟨1838108600695436422427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19606491740751321839221 1838108600695436422427)
                ·
                  rfl

theorem cell21_24163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].length) (baseStart_24163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24163 prefixEnd_24163 := by exact prefixLift 24163
  have htrace : WordTrace (prefixWord ++ tailWord_24163) baseStart_24163 baseEnd_24163 := by
    simpa [prefixWord, tailWord_24163, baseEnd_24163] using wordTrace_append hprefix tailTrace_24163
  have hstable : (prefixWord ++ tailWord_24163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24163).length < 2 ^ (prefixWord ++ tailWord_24163).sum := by decide
  have hdescent : baseEnd_24163 < baseStart_24163 := by decide
  rcases family_descends (prefixWord ++ tailWord_24163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24200 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 4]
def baseStart_24200 : Nat := 118140960795 + 24200 * 2 ^ 59
def prefixEnd_24200 : Nat := 4983230072969 + 3 ^ 40 * 24200 * 2
def baseEnd_24200 : Nat := 5522769706182467150539

theorem tailTrace_24200 : CollatzResearch.WordTrace tailWord_24200 prefixEnd_24200 5522769706182467150539 := by
  unfold tailWord_24200
  simp only [CollatzResearch.WordTrace]
  refine ⟨441323256167503938031027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 588431008223338584041369 441323256167503938031027)
  ·
    refine ⟨661984884251255907046541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441323256167503938031027 661984884251255907046541)
    ·
      refine ⟨248244331594220965142453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 661984884251255907046541 248244331594220965142453)
      ·
        refine ⟨23272906086958215482105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 248244331594220965142453 23272906086958215482105)
        ·
          refine ⟨17454679565218661611579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23272906086958215482105 17454679565218661611579)
          ·
            refine ⟨26182019347827992417369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17454679565218661611579 26182019347827992417369)
            ·
              refine ⟨19636514510870994313027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26182019347827992417369 19636514510870994313027)
              ·
                refine ⟨29454771766306491469541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19636514510870994313027 29454771766306491469541)
                ·
                  refine ⟨5522769706182467150539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29454771766306491469541 5522769706182467150539)
                  ·
                    rfl

theorem cell21_24200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_24200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24200 prefixEnd_24200 := by exact prefixLift 24200
  have htrace : WordTrace (prefixWord ++ tailWord_24200) baseStart_24200 baseEnd_24200 := by
    simpa [prefixWord, tailWord_24200, baseEnd_24200] using wordTrace_append hprefix tailTrace_24200
  have hstable : (prefixWord ++ tailWord_24200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24200).length < 2 ^ (prefixWord ++ tailWord_24200).sum := by decide
  have hdescent : baseEnd_24200 < baseStart_24200 := by decide
  rcases family_descends (prefixWord ++ tailWord_24200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24245 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 3]
def baseStart_24245 : Nat := 118140960795 + 24245 * 2 ^ 59
def prefixEnd_24245 : Nat := 4983230072969 + 3 ^ 40 * 24245 * 2
def baseEnd_24245 : Nat := 5533039319272388900447

theorem tailTrace_24245 : CollatzResearch.WordTrace tailWord_24245 prefixEnd_24245 5533039319272388900447 := by
  unfold tailWord_24245
  simp only [CollatzResearch.WordTrace]
  refine ⟨884287797171980561450189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589525198114653707633459 884287797171980561450189)
  ·
    refine ⟨331607923939492710543821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 884287797171980561450189 331607923939492710543821)
    ·
      refine ⟨124352971477309766453933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331607923939492710543821 124352971477309766453933)
      ·
        refine ⟨46632364303991162420225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124352971477309766453933 46632364303991162420225)
        ·
          refine ⟨34974273227993371815169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46632364303991162420225 34974273227993371815169)
          ·
            refine ⟨26230704920995028861377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34974273227993371815169 26230704920995028861377)
            ·
              refine ⟨19673028690746271646033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26230704920995028861377 19673028690746271646033)
              ·
                refine ⟨14754771518059703734525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19673028690746271646033 14754771518059703734525)
                ·
                  refine ⟨5533039319272388900447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14754771518059703734525 5533039319272388900447)
                  ·
                    rfl

theorem cell21_24245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_24245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24245 prefixEnd_24245 := by exact prefixLift 24245
  have htrace : WordTrace (prefixWord ++ tailWord_24245) baseStart_24245 baseEnd_24245 := by
    simpa [prefixWord, tailWord_24245, baseEnd_24245] using wordTrace_append hprefix tailTrace_24245
  have hstable : (prefixWord ++ tailWord_24245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24245).length < 2 ^ (prefixWord ++ tailWord_24245).sum := by decide
  have hdescent : baseEnd_24245 < baseStart_24245 := by decide
  rcases family_descends (prefixWord ++ tailWord_24245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24253 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_24253 : Nat := 118140960795 + 24253 * 2 ^ 59
def prefixEnd_24253 : Nat := 4983230072969 + 3 ^ 40 * 24253 * 2
def baseEnd_24253 : Nat := 5534865028266152767097

theorem tailTrace_24253 : CollatzResearch.WordTrace tailWord_24253 prefixEnd_24253 5534865028266152767097 := by
  unfold tailWord_24253
  simp only [CollatzResearch.WordTrace]
  refine ⟨884579581142997927741413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589719720761998618494275 884579581142997927741413)
  ·
    refine ⟨165858671464312111451515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 884579581142997927741413 165858671464312111451515)
    ·
      refine ⟨248788007196468167177273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165858671464312111451515 248788007196468167177273)
      ·
        refine ⟨186591005397351125382955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248788007196468167177273 186591005397351125382955)
        ·
          refine ⟨279886508096026688074433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186591005397351125382955 279886508096026688074433)
          ·
            refine ⟨209914881072020016055825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279886508096026688074433 209914881072020016055825)
            ·
              refine ⟨157436160804015012041869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209914881072020016055825 157436160804015012041869)
              ·
                refine ⟨59038560301505629515701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157436160804015012041869 59038560301505629515701)
                ·
                  refine ⟨5534865028266152767097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59038560301505629515701 5534865028266152767097)
                  ·
                    rfl

theorem cell21_24253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_24253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24253 prefixEnd_24253 := by exact prefixLift 24253
  have htrace : WordTrace (prefixWord ++ tailWord_24253) baseStart_24253 baseEnd_24253 := by
    simpa [prefixWord, tailWord_24253, baseEnd_24253] using wordTrace_append hprefix tailTrace_24253
  have hstable : (prefixWord ++ tailWord_24253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24253).length < 2 ^ (prefixWord ++ tailWord_24253).sum := by decide
  have hdescent : baseEnd_24253 < baseStart_24253 := by decide
  rcases family_descends (prefixWord ++ tailWord_24253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24301 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 4]
def baseStart_24301 : Nat := 118140960795 + 24301 * 2 ^ 59
def prefixEnd_24301 : Nat := 4983230072969 + 3 ^ 40 * 24301 * 2
def baseEnd_24301 : Nat := 5545819282228735966999

theorem tailTrace_24301 : CollatzResearch.WordTrace tailWord_24301 prefixEnd_24301 5545819282228735966999 := by
  unfold tailWord_24301
  simp only [CollatzResearch.WordTrace]
  refine ⟨886330284969102125488757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 590886856646068083659171 886330284969102125488757)
  ·
    refine ⟨83093464215853324264571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 886330284969102125488757 83093464215853324264571)
    ·
      refine ⟨124640196323779986396857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83093464215853324264571 124640196323779986396857)
      ·
        refine ⟨93480147242834989797643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124640196323779986396857 93480147242834989797643)
        ·
          refine ⟨140220220864252484696465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93480147242834989797643 140220220864252484696465)
          ·
            refine ⟨105165165648189363522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140220220864252484696465 105165165648189363522349)
            ·
              refine ⟨39436937118071011320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105165165648189363522349 39436937118071011320881)
              ·
                refine ⟨29577702838553258490661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39436937118071011320881 29577702838553258490661)
                ·
                  refine ⟨5545819282228735966999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29577702838553258490661 5545819282228735966999)
                  ·
                    rfl

theorem cell21_24301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_24301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24301 prefixEnd_24301 := by exact prefixLift 24301
  have htrace : WordTrace (prefixWord ++ tailWord_24301) baseStart_24301 baseEnd_24301 := by
    simpa [prefixWord, tailWord_24301, baseEnd_24301] using wordTrace_append hprefix tailTrace_24301
  have hstable : (prefixWord ++ tailWord_24301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24301).length < 2 ^ (prefixWord ++ tailWord_24301).sum := by decide
  have hdescent : baseEnd_24301 < baseStart_24301 := by decide
  rcases family_descends (prefixWord ++ tailWord_24301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24360 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_24360 : Nat := 118140960795 + 24360 * 2 ^ 59
def prefixEnd_24360 : Nat := 4983230072969 + 3 ^ 40 * 24360 * 2
def baseEnd_24360 : Nat := 5559283886057744483545

theorem tailTrace_24360 : CollatzResearch.WordTrace tailWord_24360 prefixEnd_24360 5559283886057744483545 := by
  unfold tailWord_24360
  simp only [CollatzResearch.WordTrace]
  refine ⟨444241095877677600943267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 592321461170236801257689 444241095877677600943267)
  ·
    refine ⟨666361643816516401414901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444241095877677600943267 666361643816516401414901)
    ·
      refine ⟨62471404107798412632647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 666361643816516401414901 62471404107798412632647)
      ·
        refine ⟨93707106161697618948971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62471404107798412632647 93707106161697618948971)
        ·
          refine ⟨140560659242546428423457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93707106161697618948971 140560659242546428423457)
          ·
            refine ⟨105420494431909821317593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140560659242546428423457 105420494431909821317593)
            ·
              refine ⟨79065370823932365988195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105420494431909821317593 79065370823932365988195)
              ·
                refine ⟨118598056235898548982293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79065370823932365988195 118598056235898548982293)
                ·
                  refine ⟨5559283886057744483545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118598056235898548982293 5559283886057744483545)
                  ·
                    rfl

theorem cell21_24360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_24360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24360 prefixEnd_24360 := by exact prefixLift 24360
  have htrace : WordTrace (prefixWord ++ tailWord_24360) baseStart_24360 baseEnd_24360 := by
    simpa [prefixWord, tailWord_24360, baseEnd_24360] using wordTrace_append hprefix tailTrace_24360
  have hstable : (prefixWord ++ tailWord_24360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24360).length < 2 ^ (prefixWord ++ tailWord_24360).sum := by decide
  have hdescent : baseEnd_24360 < baseStart_24360 := by decide
  rcases family_descends (prefixWord ++ tailWord_24360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24546 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_24546 : Nat := 118140960795 + 24546 * 2 ^ 59
def prefixEnd_24546 : Nat := 4983230072969 + 3 ^ 40 * 24546 * 2
def baseEnd_24546 : Nat := 5601731620162754383165

theorem tailTrace_24546 : CollatzResearch.WordTrace tailWord_24546 prefixEnd_24546 5601731620162754383165 := by
  unfold tailWord_24546
  simp only [CollatzResearch.WordTrace]
  refine ⟨223816542270377242039373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 596844112721005978771661 223816542270377242039373)
  ·
    refine ⟨83931203351391465764765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223816542270377242039373 83931203351391465764765)
    ·
      refine ⟨31474201256771799661787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83931203351391465764765 31474201256771799661787)
      ·
        refine ⟨47211301885157699492681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31474201256771799661787 47211301885157699492681)
        ·
          refine ⟨35408476413868274619511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47211301885157699492681 35408476413868274619511)
          ·
            refine ⟨53112714620802411929267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35408476413868274619511 53112714620802411929267)
            ·
              refine ⟨79669071931203617893901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53112714620802411929267 79669071931203617893901)
              ·
                refine ⟨29875901974201356710213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79669071931203617893901 29875901974201356710213)
                ·
                  refine ⟨5601731620162754383165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29875901974201356710213 5601731620162754383165)
                  ·
                    rfl

theorem cell21_24546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_24546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24546 prefixEnd_24546 := by exact prefixLift 24546
  have htrace : WordTrace (prefixWord ++ tailWord_24546) baseStart_24546 baseEnd_24546 := by
    simpa [prefixWord, tailWord_24546, baseEnd_24546] using wordTrace_append hprefix tailTrace_24546
  have hstable : (prefixWord ++ tailWord_24546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24546).length < 2 ^ (prefixWord ++ tailWord_24546).sum := by decide
  have hdescent : baseEnd_24546 < baseStart_24546 := by decide
  rcases family_descends (prefixWord ++ tailWord_24546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24588 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_24588 : Nat := 118140960795 + 24588 * 2 ^ 59
def prefixEnd_24588 : Nat := 4983230072969 + 3 ^ 40 * 24588 * 2
def baseEnd_24588 : Nat := 5611316592380014683079

theorem tailTrace_24588 : CollatzResearch.WordTrace tailWord_24588 prefixEnd_24588 5611316592380014683079 := by
  unfold tailWord_24588
  simp only [CollatzResearch.WordTrace]
  refine ⟨448399017464675070593209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 597865356619566760790945 448399017464675070593209)
  ·
    refine ⟨336299263098506302944907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 448399017464675070593209 336299263098506302944907)
    ·
      refine ⟨504448894647759454417361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336299263098506302944907 504448894647759454417361)
      ·
        refine ⟨378336670985819590813021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504448894647759454417361 378336670985819590813021)
        ·
          refine ⟨141876251619682346554883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378336670985819590813021 141876251619682346554883)
          ·
            refine ⟨212814377429523519832325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141876251619682346554883 212814377429523519832325)
            ·
              refine ⟨39902695768035659968561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212814377429523519832325 39902695768035659968561)
              ·
                refine ⟨29927021826026744976421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39902695768035659968561 29927021826026744976421)
                ·
                  refine ⟨5611316592380014683079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29927021826026744976421 5611316592380014683079)
                  ·
                    rfl

theorem cell21_24588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_24588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24588 prefixEnd_24588 := by exact prefixLift 24588
  have htrace : WordTrace (prefixWord ++ tailWord_24588) baseStart_24588 baseEnd_24588 := by
    simpa [prefixWord, tailWord_24588, baseEnd_24588] using wordTrace_append hprefix tailTrace_24588
  have hstable : (prefixWord ++ tailWord_24588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24588).length < 2 ^ (prefixWord ++ tailWord_24588).sum := by decide
  have hdescent : baseEnd_24588 < baseStart_24588 := by decide
  rcases family_descends (prefixWord ++ tailWord_24588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24602 : List Nat := [3, 1, 1, 3, 1, 3, 3, 6]
def baseStart_24602 : Nat := 118140960795 + 24602 * 2 ^ 59
def prefixEnd_24602 : Nat := 4983230072969 + 3 ^ 40 * 24602 * 2
def baseEnd_24602 : Nat := 1871503861039700483239

theorem tailTrace_24602 : CollatzResearch.WordTrace tailWord_24602 prefixEnd_24602 1871503861039700483239 := by
  unfold tailWord_24602
  simp only [CollatzResearch.WordTrace]
  refine ⟨224327164219657633049015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 598205771252420354797373 224327164219657633049015)
  ·
    refine ⟨336490746329486449573523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224327164219657633049015 336490746329486449573523)
    ·
      refine ⟨504736119494229674360285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336490746329486449573523 504736119494229674360285)
      ·
        refine ⟨189276044810336127885107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504736119494229674360285 189276044810336127885107)
        ·
          refine ⟨283914067215504191827661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189276044810336127885107 283914067215504191827661)
          ·
            refine ⟨106467775205814071935373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283914067215504191827661 106467775205814071935373)
            ·
              refine ⟨39925415702180276975765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106467775205814071935373 39925415702180276975765)
              ·
                refine ⟨1871503861039700483239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39925415702180276975765 1871503861039700483239)
                ·
                  rfl

theorem cell21_24602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_24602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24602 prefixEnd_24602 := by exact prefixLift 24602
  have htrace : WordTrace (prefixWord ++ tailWord_24602) baseStart_24602 baseEnd_24602 := by
    simpa [prefixWord, tailWord_24602, baseEnd_24602] using wordTrace_append hprefix tailTrace_24602
  have hstable : (prefixWord ++ tailWord_24602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24602).length < 2 ^ (prefixWord ++ tailWord_24602).sum := by decide
  have hdescent : baseEnd_24602 < baseStart_24602 := by decide
  rcases family_descends (prefixWord ++ tailWord_24602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24647 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_24647 : Nat := 118140960795 + 24647 * 2 ^ 59
def prefixEnd_24647 : Nat := 4983230072969 + 3 ^ 40 * 24647 * 2
def baseEnd_24647 : Nat := 5624781196209023199625

theorem tailTrace_24647 : CollatzResearch.WordTrace tailWord_24647 prefixEnd_24647 5624781196209023199625 := by
  unfold tailWord_24647
  simp only [CollatzResearch.WordTrace]
  refine ⟨898949941715603217584195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 599299961143735478389463 898949941715603217584195)
  ·
    refine ⟨1348424912573404826376293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 898949941715603217584195 1348424912573404826376293)
    ·
      refine ⟨252829671107513404945555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1348424912573404826376293 252829671107513404945555)
      ·
        refine ⟨379244506661270107418333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252829671107513404945555 379244506661270107418333)
        ·
          refine ⟨142216689997976290281875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379244506661270107418333 142216689997976290281875)
          ·
            refine ⟨213325034996964435422813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142216689997976290281875 213325034996964435422813)
            ·
              refine ⟨79996888123861663283555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213325034996964435422813 79996888123861663283555)
              ·
                refine ⟨119995332185792494925333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79996888123861663283555 119995332185792494925333)
                ·
                  refine ⟨5624781196209023199625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119995332185792494925333 5624781196209023199625)
                  ·
                    rfl

theorem cell21_24647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_24647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24647 prefixEnd_24647 := by exact prefixLift 24647
  have htrace : WordTrace (prefixWord ++ tailWord_24647) baseStart_24647 baseEnd_24647 := by
    simpa [prefixWord, tailWord_24647, baseEnd_24647] using wordTrace_append hprefix tailTrace_24647
  have hstable : (prefixWord ++ tailWord_24647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24647).length < 2 ^ (prefixWord ++ tailWord_24647).sum := by decide
  have hdescent : baseEnd_24647 < baseStart_24647 := by decide
  rcases family_descends (prefixWord ++ tailWord_24647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24670 : List Nat := [4, 4, 1, 1, 2, 2, 2, 5]
def baseStart_24670 : Nat := 118140960795 + 24670 * 2 ^ 59
def prefixEnd_24670 : Nat := 4983230072969 + 3 ^ 40 * 24670 * 2
def baseEnd_24670 : Nat := 1876676703188698105415

theorem tailTrace_24670 : CollatzResearch.WordTrace tailWord_24670 prefixEnd_24670 1876676703188698105415 := by
  unfold tailWord_24670
  simp only [CollatzResearch.WordTrace]
  refine ⟨112473602579034768208933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 599859213754852097114309 112473602579034768208933)
  ·
    refine ⟨21088800483569019039175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112473602579034768208933 21088800483569019039175)
    ·
      refine ⟨31633200725353528558763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21088800483569019039175 31633200725353528558763)
      ·
        refine ⟨47449801088030292838145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31633200725353528558763 47449801088030292838145)
        ·
          refine ⟨35587350816022719628609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47449801088030292838145 35587350816022719628609)
          ·
            refine ⟨26690513112017039721457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35587350816022719628609 26690513112017039721457)
            ·
              refine ⟨20017884834012779791093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26690513112017039721457 20017884834012779791093)
              ·
                refine ⟨1876676703188698105415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20017884834012779791093 1876676703188698105415)
                ·
                  rfl

theorem cell21_24670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_24670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24670 prefixEnd_24670 := by exact prefixLift 24670
  have htrace : WordTrace (prefixWord ++ tailWord_24670) baseStart_24670 baseEnd_24670 := by
    simpa [prefixWord, tailWord_24670, baseEnd_24670] using wordTrace_append hprefix tailTrace_24670
  have hstable : (prefixWord ++ tailWord_24670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24670).length < 2 ^ (prefixWord ++ tailWord_24670).sum := by decide
  have hdescent : baseEnd_24670 < baseStart_24670 := by decide
  rcases family_descends (prefixWord ++ tailWord_24670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24709 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_24709 : Nat := 118140960795 + 24709 * 2 ^ 59
def prefixEnd_24709 : Nat := 4983230072969 + 3 ^ 40 * 24709 * 2
def baseEnd_24709 : Nat := 5638930440910693166165

theorem tailTrace_24709 : CollatzResearch.WordTrace tailWord_24709 prefixEnd_24709 5638930440910693166165 := by
  unfold tailWord_24709
  simp only [CollatzResearch.WordTrace]
  refine ⟨901211267490987806341181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600807511660658537560787 901211267490987806341181)
  ·
    refine ⟨337954225309120427377943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 901211267490987806341181 337954225309120427377943)
    ·
      refine ⟨506931337963680641066915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337954225309120427377943 506931337963680641066915)
      ·
        refine ⟨760397006945520961600373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506931337963680641066915 760397006945520961600373)
        ·
          refine ⟨71287219401142590150035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 760397006945520961600373 71287219401142590150035)
          ·
            refine ⟨106930829101713885225053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71287219401142590150035 106930829101713885225053)
            ·
              refine ⟨40099060913142706959395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106930829101713885225053 40099060913142706959395)
              ·
                refine ⟨60148591369714060439093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40099060913142706959395 60148591369714060439093)
                ·
                  refine ⟨5638930440910693166165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60148591369714060439093 5638930440910693166165)
                  ·
                    rfl

theorem cell21_24709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_24709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24709 prefixEnd_24709 := by exact prefixLift 24709
  have htrace : WordTrace (prefixWord ++ tailWord_24709) baseStart_24709 baseEnd_24709 := by
    simpa [prefixWord, tailWord_24709, baseEnd_24709] using wordTrace_append hprefix tailTrace_24709
  have hstable : (prefixWord ++ tailWord_24709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24709).length < 2 ^ (prefixWord ++ tailWord_24709).sum := by decide
  have hdescent : baseEnd_24709 < baseStart_24709 := by decide
  rcases family_descends (prefixWord ++ tailWord_24709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24830 : List Nat := [4, 2, 2, 1, 1, 1, 2, 8]
def baseStart_24830 : Nat := 118140960795 + 24830 * 2 ^ 59
def prefixEnd_24830 : Nat := 4983230072969 + 3 ^ 40 * 24830 * 2
def baseEnd_24830 : Nat := 1888848096480457216417

theorem tailTrace_24830 : CollatzResearch.WordTrace tailWord_24830 prefixEnd_24830 1888848096480457216417 := by
  unfold tailWord_24830
  simp only [CollatzResearch.WordTrace]
  refine ⟨113203062506578183936993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 603749666701750314330629 113203062506578183936993)
  ·
    refine ⟨84902296879933637952745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113203062506578183936993 84902296879933637952745)
    ·
      refine ⟨63676722659950228464559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84902296879933637952745 63676722659950228464559)
      ·
        refine ⟨95515083989925342696839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63676722659950228464559 95515083989925342696839)
        ·
          refine ⟨143272625984888014045259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95515083989925342696839 143272625984888014045259)
          ·
            refine ⟨214908938977332021067889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143272625984888014045259 214908938977332021067889)
            ·
              refine ⟨161181704232999015800917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214908938977332021067889 161181704232999015800917)
              ·
                refine ⟨1888848096480457216417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 161181704232999015800917 1888848096480457216417)
                ·
                  rfl

theorem cell21_24830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_24830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24830 prefixEnd_24830 := by exact prefixLift 24830
  have htrace : WordTrace (prefixWord ++ tailWord_24830) baseStart_24830 baseEnd_24830 := by
    simpa [prefixWord, tailWord_24830, baseEnd_24830] using wordTrace_append hprefix tailTrace_24830
  have hstable : (prefixWord ++ tailWord_24830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24830).length < 2 ^ (prefixWord ++ tailWord_24830).sum := by decide
  have hdescent : baseEnd_24830 < baseStart_24830 := by decide
  rcases family_descends (prefixWord ++ tailWord_24830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24844 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_24844 : Nat := 118140960795 + 24844 * 2 ^ 59
def prefixEnd_24844 : Nat := 4983230072969 + 3 ^ 40 * 24844 * 2
def baseEnd_24844 : Nat := 5669739280180458415889

theorem tailTrace_24844 : CollatzResearch.WordTrace tailWord_24844 prefixEnd_24844 5669739280180458415889 := by
  unfold tailWord_24844
  simp only [CollatzResearch.WordTrace]
  refine ⟨453067561000952931252793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 604090081334603908337057 453067561000952931252793)
  ·
    refine ⟨339800670750714698439595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 453067561000952931252793 339800670750714698439595)
    ·
      refine ⟨509701006126072047659393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339800670750714698439595 509701006126072047659393)
      ·
        refine ⟨382275754594554035744545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509701006126072047659393 382275754594554035744545)
        ·
          refine ⟨286706815945915526808409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382275754594554035744545 286706815945915526808409)
          ·
            refine ⟨215030111959436645106307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286706815945915526808409 215030111959436645106307)
            ·
              refine ⟨322545167939154967659461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215030111959436645106307 322545167939154967659461)
              ·
                refine ⟨60477218988591556436149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322545167939154967659461 60477218988591556436149)
                ·
                  refine ⟨5669739280180458415889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60477218988591556436149 5669739280180458415889)
                  ·
                    rfl

theorem cell21_24844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_24844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24844 prefixEnd_24844 := by exact prefixLift 24844
  have htrace : WordTrace (prefixWord ++ tailWord_24844) baseStart_24844 baseEnd_24844 := by
    simpa [prefixWord, tailWord_24844, baseEnd_24844] using wordTrace_append hprefix tailTrace_24844
  have hstable : (prefixWord ++ tailWord_24844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24844).length < 2 ^ (prefixWord ++ tailWord_24844).sum := by decide
  have hdescent : baseEnd_24844 < baseStart_24844 := by decide
  rcases family_descends (prefixWord ++ tailWord_24844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24937 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 3]
def baseStart_24937 : Nat := 118140960795 + 24937 * 2 ^ 59
def prefixEnd_24937 : Nat := 4983230072969 + 3 ^ 40 * 24937 * 2
def baseEnd_24937 : Nat := 5690963147232963365699

theorem tailTrace_24937 : CollatzResearch.WordTrace tailWord_24937 prefixEnd_24937 5690963147232963365699 := by
  unfold tailWord_24937
  simp only [CollatzResearch.WordTrace]
  refine ⟨909527110664982745641065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606351407109988497094043 909527110664982745641065)
  ·
    refine ⟨682145332998737059230799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 909527110664982745641065 682145332998737059230799)
    ·
      refine ⟨1023217999498105588846199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682145332998737059230799 1023217999498105588846199)
      ·
        refine ⟨1534826999247158383269299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023217999498105588846199 1534826999247158383269299)
        ·
          refine ⟨2302240498870737574903949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534826999247158383269299 2302240498870737574903949)
          ·
            refine ⟨863340187076526590588981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2302240498870737574903949 863340187076526590588981)
            ·
              refine ⟨80938142538424367867717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 863340187076526590588981 80938142538424367867717)
              ·
                refine ⟨15175901725954568975197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80938142538424367867717 15175901725954568975197)
                ·
                  refine ⟨5690963147232963365699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15175901725954568975197 5690963147232963365699)
                  ·
                    rfl

theorem cell21_24937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_24937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24937 prefixEnd_24937 := by exact prefixLift 24937
  have htrace : WordTrace (prefixWord ++ tailWord_24937) baseStart_24937 baseEnd_24937 := by
    simpa [prefixWord, tailWord_24937, baseEnd_24937] using wordTrace_append hprefix tailTrace_24937
  have hstable : (prefixWord ++ tailWord_24937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24937).length < 2 ^ (prefixWord ++ tailWord_24937).sum := by decide
  have hdescent : baseEnd_24937 < baseStart_24937 := by decide
  rcases family_descends (prefixWord ++ tailWord_24937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24996 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_24996 : Nat := 118140960795 + 24996 * 2 ^ 59
def prefixEnd_24996 : Nat := 4983230072969 + 3 ^ 40 * 24996 * 2
def baseEnd_24996 : Nat := 5704427751061971882245

theorem tailTrace_24996 : CollatzResearch.WordTrace tailWord_24996 prefixEnd_24996 5704427751061971882245 := by
  unfold tailWord_24996
  simp only [CollatzResearch.WordTrace]
  refine ⟨455839508725617911019421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 607786011634157214692561 455839508725617911019421)
  ·
    refine ⟨170939815772106716632283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 455839508725617911019421 170939815772106716632283)
    ·
      refine ⟨256409723658160074948425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170939815772106716632283 256409723658160074948425)
      ·
        refine ⟨192307292743620056211319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256409723658160074948425 192307292743620056211319)
        ·
          refine ⟨288460939115430084316979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192307292743620056211319 288460939115430084316979)
          ·
            refine ⟨432691408673145126475469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288460939115430084316979 432691408673145126475469)
            ·
              refine ⟨162259278252429422428301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432691408673145126475469 162259278252429422428301)
              ·
                refine ⟨60847229344661033410613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162259278252429422428301 60847229344661033410613)
                ·
                  refine ⟨5704427751061971882245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60847229344661033410613 5704427751061971882245)
                  ·
                    rfl

theorem cell21_24996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_24996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_24996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_24996 prefixEnd_24996 := by exact prefixLift 24996
  have htrace : WordTrace (prefixWord ++ tailWord_24996) baseStart_24996 baseEnd_24996 := by
    simpa [prefixWord, tailWord_24996, baseEnd_24996] using wordTrace_append hprefix tailTrace_24996
  have hstable : (prefixWord ++ tailWord_24996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24996).length < 2 ^ (prefixWord ++ tailWord_24996).sum := by decide
  have hdescent : baseEnd_24996 < baseStart_24996 := by decide
  rcases family_descends (prefixWord ++ tailWord_24996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25140 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_25140 : Nat := 118140960795 + 25140 * 2 ^ 59
def prefixEnd_25140 : Nat := 4983230072969 + 3 ^ 40 * 25140 * 2
def baseEnd_25140 : Nat := 5737290512949721481951

theorem tailTrace_25140 : CollatzResearch.WordTrace tailWord_25140 prefixEnd_25140 5737290512949721481951 := by
  unfold tailWord_25140
  simp only [CollatzResearch.WordTrace]
  refine ⟨458465564464774207640437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 611287419286365610187249 458465564464774207640437)
  ·
    refine ⟨42981146668572581966291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 458465564464774207640437 42981146668572581966291)
    ·
      refine ⟨64471720002858872949437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42981146668572581966291 64471720002858872949437)
      ·
        refine ⟨24176895001072077356039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64471720002858872949437 24176895001072077356039)
        ·
          refine ⟨36265342501608116034059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24176895001072077356039 36265342501608116034059)
          ·
            refine ⟨54398013752412174051089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36265342501608116034059 54398013752412174051089)
            ·
              refine ⟨40798510314309130538317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54398013752412174051089 40798510314309130538317)
              ·
                refine ⟨15299441367865923951869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40798510314309130538317 15299441367865923951869)
                ·
                  refine ⟨5737290512949721481951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15299441367865923951869 5737290512949721481951)
                  ·
                    rfl

theorem cell21_25140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_25140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25140 prefixEnd_25140 := by exact prefixLift 25140
  have htrace : WordTrace (prefixWord ++ tailWord_25140) baseStart_25140 baseEnd_25140 := by
    simpa [prefixWord, tailWord_25140, baseEnd_25140] using wordTrace_append hprefix tailTrace_25140
  have hstable : (prefixWord ++ tailWord_25140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25140).length < 2 ^ (prefixWord ++ tailWord_25140).sum := by decide
  have hdescent : baseEnd_25140 < baseStart_25140 := by decide
  rcases family_descends (prefixWord ++ tailWord_25140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25165 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 5]
def baseStart_25165 : Nat := 118140960795 + 25165 * 2 ^ 59
def prefixEnd_25165 : Nat := 4983230072969 + 3 ^ 40 * 25165 * 2
def baseEnd_25165 : Nat := 5742995853555233565233

theorem tailTrace_25165 : CollatzResearch.WordTrace tailWord_25165 prefixEnd_25165 5742995853555233565233 := by
  unfold tailWord_25165
  simp only [CollatzResearch.WordTrace]
  refine ⟨917842953838977684940949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 611895302559318456627299 917842953838977684940949)
  ·
    refine ⟨43023888461202078981607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 917842953838977684940949 43023888461202078981607)
    ·
      refine ⟨64535832691803118472411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43023888461202078981607 64535832691803118472411)
      ·
        refine ⟨96803749037704677708617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64535832691803118472411 96803749037704677708617)
        ·
          refine ⟨72602811778278508281463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96803749037704677708617 72602811778278508281463)
          ·
            refine ⟨108904217667417762422195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72602811778278508281463 108904217667417762422195)
            ·
              refine ⟨163356326501126643633293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108904217667417762422195 163356326501126643633293)
              ·
                refine ⟨61258622437922491362485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163356326501126643633293 61258622437922491362485)
                ·
                  refine ⟨5742995853555233565233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61258622437922491362485 5742995853555233565233)
                  ·
                    rfl

theorem cell21_25165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_25165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25165 prefixEnd_25165 := by exact prefixLift 25165
  have htrace : WordTrace (prefixWord ++ tailWord_25165) baseStart_25165 baseEnd_25165 := by
    simpa [prefixWord, tailWord_25165, baseEnd_25165] using wordTrace_append hprefix tailTrace_25165
  have hstable : (prefixWord ++ tailWord_25165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25165).length < 2 ^ (prefixWord ++ tailWord_25165).sum := by decide
  have hdescent : baseEnd_25165 < baseStart_25165 := by decide
  rcases family_descends (prefixWord ++ tailWord_25165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25207 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_25207 : Nat := 118140960795 + 25207 * 2 ^ 59
def prefixEnd_25207 : Nat := 4983230072969 + 3 ^ 40 * 25207 * 2
def baseEnd_25207 : Nat := 5752580825772493865147

theorem tailTrace_25207 : CollatzResearch.WordTrace tailWord_25207 prefixEnd_25207 5752580825772493865147 := by
  unfold tailWord_25207
  simp only [CollatzResearch.WordTrace]
  refine ⟨919374819686818857969875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 612916546457879238646583 919374819686818857969875)
  ·
    refine ⟨1379062229530228286954813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919374819686818857969875 1379062229530228286954813)
    ·
      refine ⟨517148336073835607608055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1379062229530228286954813 517148336073835607608055)
      ·
        refine ⟨775722504110753411412083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517148336073835607608055 775722504110753411412083)
        ·
          refine ⟨1163583756166130117118125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775722504110753411412083 1163583756166130117118125)
          ·
            refine ⟨436343908562298793919297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163583756166130117118125 436343908562298793919297)
            ·
              refine ⟨327257931421724095439473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436343908562298793919297 327257931421724095439473)
              ·
                refine ⟨245443448566293071579605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327257931421724095439473 245443448566293071579605)
                ·
                  refine ⟨5752580825772493865147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245443448566293071579605 5752580825772493865147)
                  ·
                    rfl

theorem cell21_25207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_25207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25207 prefixEnd_25207 := by exact prefixLift 25207
  have htrace : WordTrace (prefixWord ++ tailWord_25207) baseStart_25207 baseEnd_25207 := by
    simpa [prefixWord, tailWord_25207, baseEnd_25207] using wordTrace_append hprefix tailTrace_25207
  have hstable : (prefixWord ++ tailWord_25207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25207).length < 2 ^ (prefixWord ++ tailWord_25207).sum := by decide
  have hdescent : baseEnd_25207 < baseStart_25207 := by decide
  rcases family_descends (prefixWord ++ tailWord_25207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25269 : List Nat := [1, 3, 3, 3, 1, 10]
def baseStart_25269 : Nat := 118140960795 + 25269 * 2 ^ 59
def prefixEnd_25269 : Nat := 4983230072969 + 3 ^ 40 * 25269 * 2
def baseEnd_25269 : Nat := 213582595202746808581

theorem tailTrace_25269 : CollatzResearch.WordTrace tailWord_25269 prefixEnd_25269 213582595202746808581 := by
  unfold tailWord_25269
  simp only [CollatzResearch.WordTrace]
  refine ⟨921636145462203446726861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 614424096974802297817907 921636145462203446726861)
  ·
    refine ⟨345613554548326292522573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 921636145462203446726861 345613554548326292522573)
    ·
      refine ⟨129605082955622359695965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345613554548326292522573 129605082955622359695965)
      ·
        refine ⟨48601906108358384885987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129605082955622359695965 48601906108358384885987)
        ·
          refine ⟨72902859162537577328981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48601906108358384885987 72902859162537577328981)
          ·
            refine ⟨213582595202746808581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 72902859162537577328981 213582595202746808581)
            ·
              rfl

theorem cell21_25269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 10].length) (baseStart_25269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25269 prefixEnd_25269 := by exact prefixLift 25269
  have htrace : WordTrace (prefixWord ++ tailWord_25269) baseStart_25269 baseEnd_25269 := by
    simpa [prefixWord, tailWord_25269, baseEnd_25269] using wordTrace_append hprefix tailTrace_25269
  have hstable : (prefixWord ++ tailWord_25269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25269).length < 2 ^ (prefixWord ++ tailWord_25269).sum := by decide
  have hdescent : baseEnd_25269 < baseStart_25269 := by decide
  rcases family_descends (prefixWord ++ tailWord_25269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25317 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 3]
def baseStart_25317 : Nat := 118140960795 + 25317 * 2 ^ 59
def prefixEnd_25317 : Nat := 4983230072969 + 3 ^ 40 * 25317 * 2
def baseEnd_25317 : Nat := 5777684324436747031589

theorem tailTrace_25317 : CollatzResearch.WordTrace tailWord_25317 prefixEnd_25317 5777684324436747031589 := by
  unfold tailWord_25317
  simp only [CollatzResearch.WordTrace]
  refine ⟨923386849288307644474205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 615591232858871762982803 923386849288307644474205)
  ·
    refine ⟨346270068483115366677827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 923386849288307644474205 346270068483115366677827)
    ·
      refine ⟨519405102724673050016741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346270068483115366677827 519405102724673050016741)
      ·
        refine ⟨97388456760876196878139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519405102724673050016741 97388456760876196878139)
        ·
          refine ⟨146082685141314295317209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97388456760876196878139 146082685141314295317209)
          ·
            refine ⟨109562013855985721487907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146082685141314295317209 109562013855985721487907)
            ·
              refine ⟨164343020783978582231861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109562013855985721487907 164343020783978582231861)
              ·
                refine ⟨15407158198497992084237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164343020783978582231861 15407158198497992084237)
                ·
                  refine ⟨5777684324436747031589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15407158198497992084237 5777684324436747031589)
                  ·
                    rfl

theorem cell21_25317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_25317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25317 prefixEnd_25317 := by exact prefixLift 25317
  have htrace : WordTrace (prefixWord ++ tailWord_25317) baseStart_25317 baseEnd_25317 := by
    simpa [prefixWord, tailWord_25317, baseEnd_25317] using wordTrace_append hprefix tailTrace_25317
  have hstable : (prefixWord ++ tailWord_25317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25317).length < 2 ^ (prefixWord ++ tailWord_25317).sum := by decide
  have hdescent : baseEnd_25317 < baseStart_25317 := by decide
  rcases family_descends (prefixWord ++ tailWord_25317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25328 : List Nat := [2, 1, 1, 1, 3, 1, 12]
def baseStart_25328 : Nat := 118140960795 + 25328 * 2 ^ 59
def prefixEnd_25328 : Nat := 4983230072969 + 3 ^ 40 * 25328 * 2
def baseEnd_25328 : Nat := 642243852700352483137

theorem tailTrace_25328 : CollatzResearch.WordTrace tailWord_25328 prefixEnd_25328 642243852700352483137 := by
  unfold tailWord_25328
  simp only [CollatzResearch.WordTrace]
  refine ⟨461894026124228261562319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 615858701498971015416425 461894026124228261562319)
  ·
    refine ⟨692841039186342392343479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 461894026124228261562319 692841039186342392343479)
    ·
      refine ⟨1039261558779513588515219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692841039186342392343479 1039261558779513588515219)
      ·
        refine ⟨1558892338169270382772829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039261558779513588515219 1558892338169270382772829)
        ·
          refine ⟨584584626813476393539811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1558892338169270382772829 584584626813476393539811)
          ·
            refine ⟨876876940220214590309717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584584626813476393539811 876876940220214590309717)
            ·
              refine ⟨642243852700352483137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 876876940220214590309717 642243852700352483137)
              ·
                rfl

theorem cell21_25328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 12].length) (baseStart_25328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25328 prefixEnd_25328 := by exact prefixLift 25328
  have htrace : WordTrace (prefixWord ++ tailWord_25328) baseStart_25328 baseEnd_25328 := by
    simpa [prefixWord, tailWord_25328, baseEnd_25328] using wordTrace_append hprefix tailTrace_25328
  have hstable : (prefixWord ++ tailWord_25328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25328).length < 2 ^ (prefixWord ++ tailWord_25328).sum := by decide
  have hdescent : baseEnd_25328 < baseStart_25328 := by decide
  rcases family_descends (prefixWord ++ tailWord_25328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25348 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_25348 : Nat := 118140960795 + 25348 * 2 ^ 59
def prefixEnd_25348 : Nat := 4983230072969 + 3 ^ 40 * 25348 * 2
def baseEnd_25348 : Nat := 5784758946787582014859

theorem tailTrace_25348 : CollatzResearch.WordTrace tailWord_25348 prefixEnd_25348 5784758946787582014859 := by
  unfold tailWord_25348
  simp only [CollatzResearch.WordTrace]
  refine ⟨462258756087999969426349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 616345008117333292568465 462258756087999969426349)
  ·
    refine ⟨173347033532999988534881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 462258756087999969426349 173347033532999988534881)
    ·
      refine ⟨130010275149749991401161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173347033532999988534881 130010275149749991401161)
      ·
        refine ⟨97507706362312493550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130010275149749991401161 97507706362312493550871)
        ·
          refine ⟨146261559543468740326307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97507706362312493550871 146261559543468740326307)
          ·
            refine ⟨219392339315203110489461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146261559543468740326307 219392339315203110489461)
            ·
              refine ⟨20568031810800291608387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219392339315203110489461 20568031810800291608387)
              ·
                refine ⟨30852047716200437412581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20568031810800291608387 30852047716200437412581)
                ·
                  refine ⟨5784758946787582014859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30852047716200437412581 5784758946787582014859)
                  ·
                    rfl

theorem cell21_25348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_25348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25348 prefixEnd_25348 := by exact prefixLift 25348
  have htrace : WordTrace (prefixWord ++ tailWord_25348) baseStart_25348 baseEnd_25348 := by
    simpa [prefixWord, tailWord_25348, baseEnd_25348] using wordTrace_append hprefix tailTrace_25348
  have hstable : (prefixWord ++ tailWord_25348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25348).length < 2 ^ (prefixWord ++ tailWord_25348).sum := by decide
  have hdescent : baseEnd_25348 < baseStart_25348 := by decide
  rcases family_descends (prefixWord ++ tailWord_25348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25359 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 5]
def baseStart_25359 : Nat := 118140960795 + 25359 * 2 ^ 59
def prefixEnd_25359 : Nat := 4983230072969 + 3 ^ 40 * 25359 * 2
def baseEnd_25359 : Nat := 5787269296654007331503

theorem tailTrace_25359 : CollatzResearch.WordTrace tailWord_25359 prefixEnd_25359 5787269296654007331503 := by
  unfold tailWord_25359
  simp only [CollatzResearch.WordTrace]
  refine ⟨924918715136148817503131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616612476757432545002087 924918715136148817503131)
  ·
    refine ⟨1387378072704223226254697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924918715136148817503131 1387378072704223226254697)
    ·
      refine ⟨1040533554528167419691023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1387378072704223226254697 1040533554528167419691023)
      ·
        refine ⟨1560800331792251129536535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040533554528167419691023 1560800331792251129536535)
        ·
          refine ⟨2341200497688376694304803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560800331792251129536535 2341200497688376694304803)
          ·
            refine ⟨3511800746532565041457205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341200497688376694304803 3511800746532565041457205)
            ·
              refine ⟨329231319987427972636613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3511800746532565041457205 329231319987427972636613)
              ·
                refine ⟨61730872497642744869365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329231319987427972636613 61730872497642744869365)
                ·
                  refine ⟨5787269296654007331503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61730872497642744869365 5787269296654007331503)
                  ·
                    rfl

theorem cell21_25359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_25359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25359 prefixEnd_25359 := by exact prefixLift 25359
  have htrace : WordTrace (prefixWord ++ tailWord_25359) baseStart_25359 baseEnd_25359 := by
    simpa [prefixWord, tailWord_25359, baseEnd_25359] using wordTrace_append hprefix tailTrace_25359
  have hstable : (prefixWord ++ tailWord_25359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25359).length < 2 ^ (prefixWord ++ tailWord_25359).sum := by decide
  have hdescent : baseEnd_25359 < baseStart_25359 := by decide
  rcases family_descends (prefixWord ++ tailWord_25359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25407 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 4]
def baseStart_25407 : Nat := 118140960795 + 25407 * 2 ^ 59
def prefixEnd_25407 : Nat := 4983230072969 + 3 ^ 40 * 25407 * 2
def baseEnd_25407 : Nat := 5798223550616590531405

theorem tailTrace_25407 : CollatzResearch.WordTrace tailWord_25407 prefixEnd_25407 5798223550616590531405 := by
  unfold tailWord_25407
  simp only [CollatzResearch.WordTrace]
  refine ⟨926669418962253015250475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 617779612641502010166983 926669418962253015250475)
  ·
    refine ⟨1390004128443379522875713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926669418962253015250475 1390004128443379522875713)
    ·
      refine ⟨1042503096332534642156785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390004128443379522875713 1042503096332534642156785)
      ·
        refine ⟨781877322249400981617589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1042503096332534642156785 781877322249400981617589)
        ·
          refine ⟨73300998960881342026649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 781877322249400981617589 73300998960881342026649)
          ·
            refine ⟨54975749220661006519987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73300998960881342026649 54975749220661006519987)
            ·
              refine ⟨82463623830991509779981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54975749220661006519987 82463623830991509779981)
              ·
                refine ⟨30923858936621816167493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82463623830991509779981 30923858936621816167493)
                ·
                  refine ⟨5798223550616590531405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30923858936621816167493 5798223550616590531405)
                  ·
                    rfl

theorem cell21_25407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 4].length) (baseStart_25407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25407 prefixEnd_25407 := by exact prefixLift 25407
  have htrace : WordTrace (prefixWord ++ tailWord_25407) baseStart_25407 baseEnd_25407 := by
    simpa [prefixWord, tailWord_25407, baseEnd_25407] using wordTrace_append hprefix tailTrace_25407
  have hstable : (prefixWord ++ tailWord_25407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25407).length < 2 ^ (prefixWord ++ tailWord_25407).sum := by decide
  have hdescent : baseEnd_25407 < baseStart_25407 := by decide
  rcases family_descends (prefixWord ++ tailWord_25407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
